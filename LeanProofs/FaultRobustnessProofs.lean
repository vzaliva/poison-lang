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
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → R.lookup? k = some true

-- Regime consistency with a typing context: (i) tags known true in the context must be true in the
-- regime interpretation, and (ii) the regime's bound is below the context's fresh-tag supply.
--
-- Intended reading: `R` only interprets *input/spec* tags (< R.bound). The context's `nextTag`
-- tracks the current supply for fresh internal tags, and it should stay above `R.bound`.
def regimeConsistentWithCtx (ctx : TypeContext) (R : Regime) : Prop :=
  tagEnvConsistentWithRegime ctx.tagEnv R ∧ R.bound ≤ ctx.nextTag

-- Regime boundedness (imported from `FaultRobustness.lean`): tags at or above the initial
-- `nextTag` supply are outside the regime's domain (model faulty inputs only).
-- We restate it locally for convenience in this file.

-- Step theorem (context-driven, no input/output specs).
-- It assumes agreement on clean items in the initial context and preserves it
-- for the post-context, plus result agreement when the result is clean under R.
def StepFR
  (mode : LeanPoison.EvalMode)
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
      regimeConsistentWithCtx ctx R →
      regimeBounded R →
      agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } →  -- NEW: initial config₀ well-formed
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →  -- NEW: initial config₁ well-formed
        terminatesTo mode e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo mode e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          wfTypeContext (ctxAfter ctx res) ∧
          wfConfig cf₀ ∧  -- final config₀ well-formed
          wfConfig cf₁ ∧  -- final config₁ well-formed
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧  -- preservation
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧  -- preservation
          regimeConsistentWithCtx (ctxAfter ctx res) R ∧  -- regime consistency preserved
          agreeOnClean predSat R (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          resultAgreesIfClean predSat R cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁

-- Step theorem spec derived from typing (context-driven).
-- No input/output specs here; they are handled by the top-level FR statement
-- and the bridge lemma.
def TypeSystemEnforcesFaultRobustness_step_spec
  (mode : LeanPoison.EvalMode)
  (e : Expr)
  (ctxᵢ : TypeContext)
  (predSat : PredSat) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
    ∀ (R : Regime),
      StepFR mode ctxᵢ R e res predSat


section TypeSystemEnforcesFaultRobustness_impl_proof

private lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ t ls, qt.etyp = ETyp.ref t ls) →
  qt.etyp.isFunctionType = false →
  qt.poison = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hnotfun hpoison hret_agree
  cases hret_agree with
  | clean_eq_nonref _ _ _ hval => exact hval
  | poisoned_noPred_eq_nonref _ _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_arrow _ hisArrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        left
        exact hisArrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_internal_parrow _ hetyp _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_parrow _ hisParrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        right
        exact hisParrow
      rw [hfun] at hnotfun
      cases hnotfun
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
  qt.etyp.isFunctionType = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hclean hnotref hnotfun hagree
  cases hagree with
  | clean_eq_nonref _ _ _ hval => exact hval
  | poisoned_noPred_eq_nonref _ _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_arrow _ hisArrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        left
        exact hisArrow
      rw [hfun] at hnotfun
      cases hnotfun
  | clean_internal_parrow _ hetyp _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | dirty_internal_parrow _ hisParrow =>
      exfalso
      have hfun : qt.etyp.isFunctionType = true := by
        simp only [ETyp.isFunctionType, Bool.or_eq_true]
        right
        exact hisParrow
      rw [hfun] at hnotfun
      cases hnotfun
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
      | clean hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | guard k' htag' hreg' _ =>
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by symm; exact htag
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R.lookup? k := by symm; exact hreg
              _ = some true := by exact hreg'
          cases this
  | guardOnly_false_poisoned_any k hgo hreg hpoison =>
      cases hclean with
      | clean hpoison' =>
          have : false = true := by
            calc
              false = qt.poison := by symm; exact hpoison'
              _ = true := by exact hpoison
          cases this
      | guard k' htag' hreg' _ =>
          have hk : k = k' := by
            have : some k = some k' := by
              calc
                some k = qtypGuardTag qt := by simp [qtypGuardTag, hgo]
                _ = some k' := by exact htag'
            exact Option.some.inj this
          subst hk
          have : (some false : Option Bool) = some true := by
            calc
              some false = R.lookup? k := by symm; exact hreg
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
  | clean hpoison =>
      have hpoison2 : qt2.poison = false := hpoison_imp hpoison
      cases hagree with
      | clean_eq_nonref _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref hpoison hnotfun' hnotref' hEq
      | poisoned_noPred_eq_nonref hpoison' _ _ _ _ =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref hpoison hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          -- Need to show internal poison is clean for qt
          -- qt.poison = false (from hpoison), qt.etyp = qt2.etyp (from hetyp)
          -- qt2 has clean_internal_arrow, so its internal poison is clean
          -- Since qt.etyp = qt2.etyp, qt's internal poison is also clean
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap hv₁ hv₂
      | dirty_internal_arrow hdirty_int hisArrow htyp1_qt2 htyp2_qt2 =>
          -- qt2 has dirty internal, but qt.poison = false (hpoison)
          -- We need to construct agreement for qt
          -- Since qt.etyp = qt2.etyp and qt2.etyp.isArrow = true, qt.etyp.isArrow = true
          have hisArrow_qt : qt.etyp.isArrow = true := by
            rw [hetyp]; exact hisArrow
          -- But we need to decide: is qt's internal poison clean or dirty?
          -- qt2's internal is dirty (hdirty_int), and qt.etyp = qt2.etyp, so qt's internal is also dirty
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_arrow hdirty_int_qt hisArrow_qt htyp1_qt htyp2_qt
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap hv₁ hv₂
      | dirty_internal_parrow hdirty_int hisParrow htyp1_qt2 htyp2_qt2 =>
          have hisParrow_qt : qt.etyp.isParrow = true := by
            rw [hetyp]; exact hisParrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_parrow hdirty_int_qt hisParrow_qt htyp1_qt htyp2_qt
      | clean_ref _hpoison2 hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | poisoned_noPred_ref hpoison' _ _ _ _ _ _ _ =>
          have : false = true := by
            calc
              false = qt2.poison := by symm; exact hpoison2
              _ = true := by exact hpoison'
          cases this
      | withPred_true_ref _k _htag _hregime hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin1 hv1 hlookup2 hin2 hv2
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
  | guard k htag hreg _ =>
      cases hagree with
      | clean_eq_nonref _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | poisoned_noPred_eq_nonref _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap hv₁ hv₂
      | dirty_internal_arrow hdirty_int hisArrow htyp1_qt2 htyp2_qt2 =>
          have hisArrow_qt : qt.etyp.isArrow = true := by
            rw [hetyp]; exact hisArrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_arrow hdirty_int_qt hisArrow_qt htyp1_qt htyp2_qt
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap hv₁ hv₂
      | dirty_internal_parrow hdirty_int hisParrow htyp1_qt2 htyp2_qt2 =>
          have hisParrow_qt : qt.etyp.isParrow = true := by
            rw [hetyp]; exact hisParrow
          have hdirty_int_qt : ¬internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hdirty_int
          -- Transport typing proofs from qt2.etyp to qt.etyp
          have htyp1_qt : valueHasETyp θ₀ o₀ qt.etyp := by
            rw [hetyp]; exact htyp1_qt2
          have htyp2_qt : valueHasETyp θ₁ o₁ qt.etyp := by
            rw [hetyp]; exact htyp2_qt2
          exact agreeValueUnder.dirty_internal_parrow hdirty_int_qt hisParrow_qt htyp1_qt htyp2_qt
      | clean_ref _hpoison2 hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | poisoned_noPred_ref _hpoison2 _hpred2 hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin1 hv1 hlookup2 hin2 hv2
      | withPred_true_ref _k2 _htag2 _hregime2 hetyp1 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin1 hv1 hlookup2 hin2 hv2
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
              some false = R.lookup? k := by symm; exact hreg'
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
              some false = R.lookup? k := by symm; exact hreg'
              _ = some true := by exact hreg
          cases this

-- If result is clean, condition must be clean (for standard mode ite)
-- From h_poison: res.qualType.poison = joinPoison ctx.pc (joinPoison res1.poison (joinPoison res2.poison res3.poison))
-- If res is clean, then the join is false, so all components are false
private lemma ite_clean_implies_cond_clean {ctx_pc res1_poison res2_poison res3_poison : Poison} :
  joinPoison ctx_pc (joinPoison res1_poison (joinPoison res2_poison res3_poison)) = false →
  res1_poison = false := by
  intro h
  have ⟨h1, h2⟩ := joinPoison_eq_false h
  have ⟨h3, _h4⟩ := joinPoison_eq_false h2
  exact h3

-- wfTypeContext for ctxAfter is equivalent to wfTypeResult
-- (ctxAfter sets memEnv := res.memEnv' and nextLoc := res.nextLoc')
private lemma wfTypeResult_of_wfTypeContext_ctxAfter (ctx : TypeContext) (res : TypeResult) :
  wfTypeContext (ctxAfter ctx res) → wfTypeResult res := by
  simp only [wfTypeContext, ctxAfter, wfTypeResult]
  exact id

-- If l is not in ctx.memEnv and runtimeInstantiatesCtx holds, then θ.lookup l = none
-- (contrapositive of runtimeInstantiatesCtx's first conjunct)
private lemma theta_not_contains_if_not_in_memEnv
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (l : Loc) :
  runtimeInstantiatesCtx ctx μ ρ θ →
  ¬ ctx.memEnv.contains l →
  θ.lookup l = none := by
  intro hric hnotContains
  by_contra h
  push_neg at h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  have ⟨hcontains, _⟩ := hric.1 l a ha
  exact hnotContains hcontains

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
  (∀ (mode : LeanPoison.EvalMode) e ctxᵢ predSat,
    TypeSystemEnforcesFaultRobustness_step_spec mode e ctxᵢ predSat) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx _hwf _hpc _hte predSat _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro mode μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm check
  have hstep' := hstep mode e ctx predSat
  have hstep' := hstep' fuel res htc
  dsimp only [FaultRobustnessSpec]
  intro cf₁ cf₂ o₁ o₂ hR hRbound hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R : Regime := ⟨ctx.nextTag, check⟩ with hRdef
  have hagree_clean :
      agreeOnClean predSat R ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ :=
    agreeOnCriticalAndTrusted_implies_agreeOnClean
      predSat R s ctx μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ hctx hagree htrusted
  have htagR : tagEnvConsistentWithRegime ctx.tagEnv R := by
    intro k deps hlookup
    -- Empty tag environment at the top level.
    have : (ctx.tagEnv.get? k) = none := by
      simp [_hte]
    rw [this] at hlookup
    cases hlookup
  have hreg : regimeConsistentWithCtx ctx R := by
    refine ⟨htagR, ?_⟩
    -- At the top level, `R.bound = ctx.nextTag`.
    simp [hRdef]
  have hstepFR :=
    (hstep' R) μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ _hwf hric₁ hric₂ hreg hRbound hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  rcases hstepFR with ⟨θ₁', θ₂', hθ₁ext, hθ₂ext, _hwf', _hwfcf₁', _hwfcf₂', _hric₁', _hric₂', _hreg', hagree_clean', hret_agree⟩
  refine ⟨θ₁', θ₂', hθ₁ext, hθ₂ext, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hctx_lookup : (ctxAfter ctx res).memEnv.lookup l = some qt := by
      simpa [ctxAfter] using hlookup_mem
    have hclean : qtypCleanUnder R qt := by
      exact qtypCleanUnder.clean hpoison
    have hlocEntry : agreeLocUnder predSat R cf₁.memory cf₂.memory θ₁' θ₂' (l, qt) :=
      (hagree_clean'.1 l qt hctx_lookup hclean)
    cases hlocEntry with
    | agree_values _l _qt a₁' a₂' n₁ n₂ hreal₁ hreal₂ hlookup₁ hlookup₂ hagree =>
        -- Reduce to equality of stored ints via agreement on the stored values.
        have hvalEq : n₁ = n₂ := by
          cases hagree with
          | clean_eq_nonref _ _ _ hval =>
              cases hval
              rfl
          | poisoned_noPred_eq_nonref _ _ _ _ hval =>
              cases hval
              rfl
          | clean_internal_arrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isArrow = true implies function type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisArrow) (by decide)
          | clean_internal_parrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isParrow = true implies parrow type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisParrow) (by decide)
          | clean_ref _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | poisoned_noPred_ref _ _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ _ hval =>
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
        refine ⟨a₁', ?_⟩
        refine And.intro hreal₁ ?_
        refine ⟨a₂', ?_⟩
        refine And.intro hreal₂ ?_
        calc
          cf₁.memory.lookup a₁' = some n₁ := hlookup₁
          _ = some n₂ := by simp [hvalEq]
          _ = cf₂.memory.lookup a₂' := by symm; exact hlookup₂
    | both_unrealized _l _qt _hnone₁ _hnone₂ =>
        exact Or.inr ⟨_hnone₁, _hnone₂⟩
  · cases hretOpt : obs.retEtyp? with
    | none =>
        simp
    | some et =>
        -- Use return agreement from the step proof.
        rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
        have hret_notfun_obs : et.isFunctionType = false := by
          simpa [wfObsSpec, hretOpt] using _hos
        have hret_clean : qtypCleanUnder R res.qualType := by
          exact qtypCleanUnder.clean hret_poison
        have hret_agree' :
            agreeValueUnder predSat R cf₁.memory cf₂.memory θ₁' θ₂' res.qualType o₁ o₂ :=
          hret_agree hret_clean
        cases et with
        | ref t ls =>
            cases hret_agree' with
            | @clean_ref _t _ls l₁ l₂ a₁ a₂ _qt _v₁ _v₂ hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
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
            | @withPred_true_ref k _t _ls l₁ l₂ a₁ a₂ _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
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
            | clean_eq_nonref _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | poisoned_noPred_eq_nonref _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | withPred_true_eq _ _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | clean_internal_arrow _ hetyp _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_arrow _ hisArrow =>
                -- qt.etyp is an arrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : (ETyp.ref t ls).isArrow = true := by
                  simpa [hret_et] using hisArrow
                -- But references are not arrow types.
                have : (false : Bool) = true := by
                  simp [ETyp.isArrow] at this
                cases this
            | clean_internal_parrow _ hetyp _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_parrow _ hisParrow =>
                -- qt.etyp is a parrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : (ETyp.ref t ls).isParrow = true := by
                  simpa [hret_et] using hisParrow
                -- But references are not parrow types.
                have : (false : Bool) = true := by
                  simp [ETyp.isParrow] at this
                cases this
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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | bool =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | unit =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | string =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | arrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs
        | parrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs

end TypeSystemEnforcesFaultRobustness_impl_proof

section TypeSystemEnforcesFaultRobustness_step_proof

private def isExternExpr : Expr → Prop
  | Expr.externVal _ _ _ => True
  | Expr.externFn _ _ _ _ => True
  | Expr.externPfn _ _ _ => True
  | _ => False

private lemma terminatesTo_extern_false
  (mode : LeanPoison.EvalMode)
  {e : Expr} {c₀ c₁ : Config} {o : Value} :
  isExternExpr e →
  ∀ (w₀ w₁ : Void IO.RealWorld), terminatesToW mode w₀ w₁ e c₀ c₁ o → False := by
  intro hex w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  cases e with
  | externVal _ _ _ =>
      cases mode with
      | ioFree =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
      | normal =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | externFn _ _ _ _ =>
      cases mode with
      | ioFree =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
      | normal =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | externPfn _ _ _ =>
      cases mode with
      | ioFree =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
      | normal =>
          cases fuel <;> simp [LeanPoison.beval] at hbeval <;> cases hbeval
  | _ =>
      cases hex

private lemma terminatesTo_num_inv (mode : LeanPoison.EvalMode) (n : Int)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.num n) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.num n := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_bool_inv (mode : LeanPoison.EvalMode) (b : Bool)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.bool b) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.bool b := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_unit_inv (mode : LeanPoison.EvalMode)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ Expr.unit { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.unit := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_str_inv (mode : LeanPoison.EvalMode) (s : String)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.str s) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = Value.str s := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_literal_inv (mode : LeanPoison.EvalMode)
  (e : Expr) (v : Value)
  (hval : Expr.toValue? e = some v)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧ o = v := by
  intro w₀ w₁ ht
  cases e with
  | unit =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_unit_inv mode μ ρ a pm cf o w₀ w₁ ht
  | num n =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_num_inv mode n μ ρ a pm cf o w₀ w₁ ht
  | bool b =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_bool_inv mode b μ ρ a pm cf o w₀ w₁ ht
  | str s =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_str_inv mode s μ ρ a pm cf o w₀ w₁ ht
  | _ =>
      simp [Expr.toValue?] at hval

private lemma terminatesTo_var_inv (mode : LeanPoison.EvalMode)
  (x : Name) (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.var x) { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  ∃ v, ρ.lookup x = some v ∧
    cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧
    o = v := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_fn_inv (mode : LeanPoison.EvalMode)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.fn x paramType body returnType)
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧
    o = Value.closure x body ρ := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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

private lemma terminatesTo_pfn_inv (mode : LeanPoison.EvalMode)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (μ : Memory) (ρ : VarEnv) (a : Address) (pm : Bool) (cf : Config) (o : Value) :
  ∀ (w₀ w₁ : Void IO.RealWorld),
    terminatesToW mode w₀ w₁ (Expr.pfn x paramType body returnType)
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
  cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } ∧
    o = Value.peClosure x body ρ := by
  intro w₀ w₁ ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
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
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₁ v₂ _ =>
      qtypCleanUnder R qt →
        θ₀.extendsMap θ₀' →
          θ₁.extendsMap θ₁' →
            agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₁ v₂
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₁ ρcap₂ _ =>
      θ₀.extendsMap θ₀' →
        θ₁.extendsMap θ₁' →
          agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₁ ρcap₂
  have htransport : motive₁ qt v₀ v₁ hagree :=
    agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref hpoison hnotfun hnotref hagree)
      (poisoned_noPred_eq_nonref := by
        intro qt v₁ v₂ hpoison hpred hnotfun hnotref hagree hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k htag _ _ =>
            have htag' : False := by
              have htag'' := htag
              simp [qtypGuardTag, hpred] at htag''
            cases htag')
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap hv₁ hv₂ ihCap _hclean
          hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch (ihCap hθ₀ hθ₁) hv₁ hv₂)
      (dirty_internal_arrow := by
        intro qt v₁ v₂ hdirty hisArrow htyp1 htyp2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_arrow hdirty hisArrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap hv₁ hv₂ ihCap
          _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch (ihCap hθ₀ hθ₁) hv₁ hv₂)
      (dirty_internal_parrow := by
        intro qt v₁ v₂ hdirty hisParrow htyp1 htyp2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_parrow hdirty hisParrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_ref := by
        intro t ls l₁ l₂ a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2)
      (poisoned_noPred_ref := by
        intro t ls l₁ l₂ a₁ a₂ qt v₁ v₂ hpoison hpred hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k htag _ _ =>
            have htag' : False := by
              have htag'' := htag
              simp [qtypGuardTag, hpred] at htag''
            cases htag')
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k t ls l₁ l₂ a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2)
      (withPred_false_poisoned_fail := by
        intro k qt v₁ v₂ hclos htag hregime hpoison htyp1 htyp2 hfail1 hfail2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k' htag' hreg' _ =>
            have hk : k = k' := by
              have : some k = some k' := by
                calc
                  some k = qtypGuardTag qt := by symm; exact htag
                  _ = some k' := by exact htag'
              exact Option.some.inj this
            subst hk
            have : (some false : Option Bool) = some true := by
              calc
                some false = R.lookup? k := by symm; exact hregime
                _ = some true := by exact hreg'
            cases this)
      (guardOnly_false_poisoned_any := by
        intro k qt v₁ v₂ hgo hregime hpoison htyp1 htyp2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k' htag' hreg' _ =>
            have hk : k = k' := by
              have : some k = some k' := by
                calc
                  some k = qtypGuardTag qt := by simp [qtypGuardTag, hgo]
                  _ = some k' := by exact htag'
              exact Option.some.inj this
            subst hk
            have : (some false : Option Bool) = some true := by
              calc
                some false = R.lookup? k := by symm; exact hregime
                _ = some true := by exact hreg'
            cases this)
      (nil := by
        intro ρcap₁ ρcap₂ _hθ₀ _hθ₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hclean hlookup1 hlookup2 hagree htail ihAgree ihTail hθ₀ hθ₁
        exact agreeCapturedEnv.cons_clean hclean hlookup1 hlookup2 (ihAgree hclean hθ₀ hθ₁) (ihTail hθ₀ hθ₁))
      (cons_dirty := by
        intro x qt σcap ρcap₁ ρcap₂ hdirty htail ihTail hθ₀ hθ₁
        exact agreeCapturedEnv.cons_dirty hdirty (ihTail hθ₀ hθ₁))
      hagree
  exact htransport hclean hθ₀ hθ₁

private lemma agreeCapturedEnv_clean_extends
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv} :
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
  agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₀ ρcap₁ := by
  intro hθ₀ hθ₁ hcap
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₁ v₂ _ =>
      qtypCleanUnder R qt →
        θ₀.extendsMap θ₀' →
          θ₁.extendsMap θ₁' →
            agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₁ v₂
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₁ ρcap₂ _ =>
      θ₀.extendsMap θ₀' →
        θ₁.extendsMap θ₁' →
          agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₁ ρcap₂
  have htransport : motive₂ σcap ρcap₀ ρcap₁ hcap :=
    agreeCapturedEnv.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref hpoison hnotfun hnotref hagree)
      (poisoned_noPred_eq_nonref := by
        intro qt v₁ v₂ hpoison hpred hnotfun hnotref hagree hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k htag _ _ =>
            have htag' : False := by
              have htag'' := htag
              simp [qtypGuardTag, hpred] at htag''
            cases htag')
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap hv₁ hv₂ ihCap _hclean
          hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch (ihCap hθ₀ hθ₁) hv₁ hv₂)
      (dirty_internal_arrow := by
        intro qt v₁ v₂ hdirty hisArrow htyp1 htyp2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_arrow hdirty hisArrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap hv₁ hv₂ ihCap
          _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch (ihCap hθ₀ hθ₁) hv₁ hv₂)
      (dirty_internal_parrow := by
        intro qt v₁ v₂ hdirty hisParrow htyp1 htyp2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_parrow hdirty hisParrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_ref := by
        intro t ls l₁ l₂ a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2)
      (poisoned_noPred_ref := by
        intro t ls l₁ l₂ a₁ a₂ qt v₁ v₂ hpoison hpred hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k htag _ _ =>
            have htag' : False := by
              have htag'' := htag
              simp [qtypGuardTag, hpred] at htag''
            cases htag')
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k t ls l₁ l₂ a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin1 hv1 (hθ₁ _ _ hlookup2) hin2 hv2)
      (withPred_false_poisoned_fail := by
        intro k qt v₁ v₂ hclos htag hregime hpoison htyp1 htyp2 hfail1 hfail2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k' htag' hreg' _ =>
            have hk : k = k' := by
              have : some k = some k' := by
                calc
                  some k = qtypGuardTag qt := by symm; exact htag
                  _ = some k' := by exact htag'
              exact Option.some.inj this
            subst hk
            have : (some false : Option Bool) = some true := by
              calc
                some false = R.lookup? k := by symm; exact hregime
                _ = some true := by exact hreg'
            cases this)
      (guardOnly_false_poisoned_any := by
        intro k qt v₁ v₂ hgo hregime hpoison htyp1 htyp2 hclean _hθ₀ _hθ₁
        cases hclean with
        | clean hpoison' =>
            have : false = true := by
              calc
                false = qt.poison := by symm; exact hpoison'
                _ = true := by exact hpoison
            cases this
        | guard k' htag' hreg' _ =>
            have hk : k = k' := by
              have : some k = some k' := by
                calc
                  some k = qtypGuardTag qt := by simp [qtypGuardTag, hgo]
                  _ = some k' := by exact htag'
              exact Option.some.inj this
            subst hk
            have : (some false : Option Bool) = some true := by
              calc
                some false = R.lookup? k := by symm; exact hregime
                _ = some true := by exact hreg'
            cases this)
      (nil := by
        intro ρcap₁ ρcap₂ _hθ₀ _hθ₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hclean hlookup1 hlookup2 hagree htail ihAgree ihTail hθ₀ hθ₁
        exact agreeCapturedEnv.cons_clean hclean hlookup1 hlookup2 (ihAgree hclean hθ₀ hθ₁) (ihTail hθ₀ hθ₁))
      (cons_dirty := by
        intro x qt σcap ρcap₁ ρcap₂ hdirty htail ihTail hθ₀ hθ₁
        exact agreeCapturedEnv.cons_dirty hdirty (ihTail hθ₀ hθ₁))
      hcap
  exact htransport hθ₀ hθ₁

private lemma Expr_toPExpr?_eq_some_of_toPExpr_ok (e : Expr) (pe : PExpr) :
  e.toPExpr = .ok pe →
  Expr.toPExpr? e = some pe := by
  intro h
  unfold Expr.toPExpr at h
  cases hpe : Expr.toPExpr? e with
  | none =>
      simp [hpe] at h
  | some pe' =>
      -- Goal: `some pe' = some pe`.
      simp [hpe] at h
      simp [pure, Except.pure] at h
      cases h
      rfl

private lemma typecheckPfn_ok_body_toPExpr?
  (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) (res : TypeResult) :
  typecheckPfn ctx x st1 body st2 = .ok res →
  ∃ pbody,
    Expr.toPExpr? body = some pbody ∧
    res.qualType.etyp = ETyp.parrow st1 st2 ctx.pc [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctx.varEnv)] := by
  intro htc
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody] at htc
  | ok pbody =>
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hres :
          res.qualType.etyp =
            ETyp.parrow st1 st2 ctx.pc [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctx.varEnv)] := by
        simp [typecheckPfn, hbody] at htc
        cases htc
        rfl
      exact ⟨pbody, hto, hres⟩

private lemma agreeCapturedEnv_of_agreeOnClean_aux
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) (σcap : CapturedVarEnv) :
  runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
  runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  (∀ x qt, (x, qt) ∈ σcap → ctx.varEnv.lookup x = some qt) →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρ₀ ρ₁ := by
  intro hric₀ hric₁ hagree
  rcases hric₀ with ⟨_hmem₀, hvars₀⟩
  rcases hric₁ with ⟨_hmem₁, hvars₁⟩
  rcases hagree with ⟨_hlocs, hvarsAg⟩
  induction σcap with
  | nil =>
      intro _hσlookup
      exact agreeCapturedEnv.nil
  | cons entry tail ih =>
      intro hσlookup
      rcases entry with ⟨x, qt⟩
      have hσlookup_tail : ∀ x qt, (x, qt) ∈ tail → ctx.varEnv.lookup x = some qt := by
        intro x qt hx
        exact hσlookup x qt (by simp [hx])
      by_cases hclean : qtypCleanUnder R qt
      · have hctx_lookup : ctx.varEnv.lookup x = some qt :=
          hσlookup x qt (by simp)
        have hvarEntry : agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt) :=
          hvarsAg x qt hctx_lookup hclean
        cases hvarEntry with
        | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagreeVal =>
            exact agreeCapturedEnv.cons_clean hclean hlookup₀ hlookup₁ hagreeVal (ih hσlookup_tail)
        | both_none _ _ hnone₀ _hnone₁ =>
            obtain ⟨v₀, hv₀, _⟩ := hvars₀ hctx_lookup
            have : (some v₀ : Option Value) = none := by
              calc
                some v₀ = ρ₀.lookup x := by symm; exact hv₀
                _ = none := by exact hnone₀
            cases this
      · exact agreeCapturedEnv.cons_dirty hclean (ih hσlookup_tail)

private lemma agreeCapturedEnv_of_agreeOnClean
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) :
  runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
  runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
  agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
  agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ := by
  intro hric₀ hric₁ hagree
  refine
    agreeCapturedEnv_of_agreeOnClean_aux predSat R ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctx.varEnv)
      hric₀ hric₁ hagree ?_
  intro x qt hmem
  have hmem' : (x, qt) ∈ ctx.varEnv.toList := by
    simpa [VarTypeEnv.toCaptured] using hmem
  have hget : ctx.varEnv[x]? = some qt :=
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).1 hmem'
  simpa [VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?] using hget

private lemma RealizationMap_lookup_update_ne
  {θ : RealizationMap} {l l' : Loc} {addr : Address} :
  l' ≠ l →
  (θ.update l addr).lookup l' = θ.lookup l' := by
  intro hne
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [RealizationMap.update, RealizationMap.lookup, ExtTreeMap.getElem?_insert, hcmp]

private lemma MemoryTypeEnv_lookup_updateMemEnv_ne
  {Γ : MemoryTypeEnv} {l l' : Loc} {qt : QTyp} :
  l' ≠ l →
  (updateMemEnv Γ l qt).lookup l' = Γ.lookup l' := by
  intro hne
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.getElem?_insert, hcmp]

private lemma Memory_lookup_update_ne
  {μ : Memory} {a a' : Address} {v : Int} :
  a ≠ a' →
  (Memory.update μ a' v).lookup a = μ.lookup a := by
  intro hne
  have hcmp : compare a' a ≠ Ordering.eq := by
    intro hcmp
    have : a' = a := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [Memory.update, Memory.lookup, ExtTreeMap.getElem?_insert, hcmp]

private lemma Memory_contains_of_lookup {μ : Memory} {a : Address} {n : Int} :
  Memory.lookup μ a = some n →
  μ.contains a = true := by
  intro hlookup
  have hisSome : μ[a]?.isSome = true := by
    have h' : μ[a]? = some n := by
      simpa [Memory.lookup, ExtTreeMap.get?_eq_getElem?] using hlookup
    simp [h']
  have hmem : a ∈ μ := (ExtTreeMap.mem_iff_isSome_getElem?).2 hisSome
  exact (ExtTreeMap.contains_iff_mem).2 hmem

private lemma agreeOnClean_newRef_extend
  (predSat : PredSat) (R : Regime) (ctxᵢ : TypeContext)
  (res1 res : TypeResult) (l : Loc) (etyp : ETyp)
  (cfg₀' cfg₁' cf₀ cf₁ : Config) (n₀ n₁ : Int) (a₀_new a₁_new : Address)
  (θ₀1 θ₁1 θ₀' θ₁' : RealizationMap)
  (h_mem :
      res.memEnv' =
        updateMemEnv res1.memEnv' l
          ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩)
  (h_etyp1 : res1.qualType.etyp = etyp)
  (ha₀_new : a₀_new = cfg₀'.nextAddr)
  (ha₁_new : a₁_new = cfg₁'.nextAddr)
  (hmem₀ : cf₀.memory = cfg₀'.memory.update a₀_new n₀)
  (hmem₁ : cf₁.memory = cfg₁'.memory.update a₁_new n₁)
  (hvar₀ : cf₀.varEnv = cfg₀'.varEnv)
  (hvar₁ : cf₁.varEnv = cfg₁'.varEnv)
  (hθ₀def : θ₀' = θ₀1.update l a₀_new)
  (hθ₁def : θ₁' = θ₁1.update l a₁_new)
  (hθext₀' : wfExtendsMap θ₀1 θ₀')
  (hθext₁' : wfExtendsMap θ₁1 θ₁')
  (hwfcf₀1 : wfConfig cfg₀')
  (hwfcf₁1 : wfConfig cfg₁')
  (hagree_clean_e :
      agreeOnClean predSat R (ctxAfter ctxᵢ res1)
        cfg₀'.memory cfg₀'.varEnv θ₀1 cfg₁'.memory cfg₁'.varEnv θ₁1)
  (hres_agree_e :
      resultAgreesIfClean predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁)) :
  agreeOnClean predSat R (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
  let storedQt : QTyp :=
    ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩
  constructor
  · intro l' qt hlookup hclean
    by_cases h_eq : l' = l
    · subst l'
      have hqt : qt = storedQt := by
        have hlookup' : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
          simp [updateMemEnv, storedQt, MemoryTypeEnv.lookup]
        have : (some qt : Option QTyp) = some storedQt := by
          calc
            some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by symm; exact hlookup'
            _ = some storedQt := by exact hself
        exact Option.some.inj this
      subst hqt
      have hreal0 : θ₀'.lookup l = some a₀_new := by
        rw [hθ₀def]
        simp [RealizationMap.update, RealizationMap.lookup]
      have hreal1 : θ₁'.lookup l = some a₁_new := by
        rw [hθ₁def]
        simp [RealizationMap.update, RealizationMap.lookup]
      have hlookup0 : cf₀.memory.lookup a₀_new = some n₀ := by
        rw [hmem₀]
        simp [Memory.update, Memory.lookup]
      have hlookup1 : cf₁.memory.lookup a₁_new = some n₁ := by
        rw [hmem₁]
        simp [Memory.update, Memory.lookup]
      have hclean_res1 : qtypCleanUnder R res1.qualType := by
        cases hclean with
        | clean hpoison =>
            have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
              simpa [storedQt] using hpoison
            exact qtypCleanUnder.clean (joinPoison_eq_false hjoin).2
        | guard k htag hreg hnotfun =>
            have htag' : qtypGuardTag res1.qualType = some k := by
              simpa [qtypGuardTag, storedQt] using htag
            have hnotfun' : res1.qualType.etyp.isFunctionType = false := by
              simpa [storedQt, h_etyp1] using hnotfun
            exact qtypCleanUnder.guard k htag' hreg hnotfun'
      have hagree_res1 :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁) :=
        hres_agree_e hclean_res1
      have hagree_stored_old :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 storedQt (Value.num n₀) (Value.num n₁) := by
        refine agreeValueUnder_transport_clean hclean ?_ ?_ ?_ hagree_res1
        · simp [storedQt, h_etyp1]
        · simp [storedQt]
        · intro hpoison
          have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
            simpa [storedQt] using hpoison
          exact (joinPoison_eq_false hjoin).2
      have hagree_stored :
          agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' storedQt (Value.num n₀) (Value.num n₁) :=
        agreeValueUnder_clean_extends hclean hθext₀'.1 hθext₁'.1 hagree_stored_old
      exact agreeLocUnder.agree_values l storedQt a₀_new a₁_new n₀ n₁ hreal0 hreal1 hlookup0 hlookup1 hagree_stored
    · have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l' = some qt := by
        have hlookup' : res.memEnv'.lookup l' = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hEq :
            (updateMemEnv res1.memEnv' l storedQt).lookup l' = res1.memEnv'.lookup l' :=
          MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l') (qt := storedQt) h_eq
        have hlookup_old' : res1.memEnv'.lookup l' = some qt := by
          have htmp := hlookup'
          rw [hEq] at htmp
          exact htmp
        simpa [ctxAfter] using hlookup_old'
      have hagree_old := hagree_clean_e.1 l' qt hlookup_old hclean
      cases hagree_old with
      | both_unrealized _ _ hnone0 hnone1 =>
          have hnone0' : θ₀'.lookup l' = none := by
            rw [hθ₀def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l') (addr := a₀_new) h_eq] using hnone0
          have hnone1' : θ₁'.lookup l' = none := by
            rw [hθ₁def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₁1) (l := l) (l' := l') (addr := a₁_new) h_eq] using hnone1
          exact agreeLocUnder.both_unrealized l' qt hnone0' hnone1'
      | agree_values _ _ a0 a1 m0 m1 hreal0 hreal1 hm0 hm1 hagree =>
          have hne0 : a0 ≠ a₀_new := by
            intro hcontra
            have hcontains : cfg₀'.memory.contains a₀_new := by
              have : cfg₀'.memory.contains a0 := Memory_contains_of_lookup hm0
              simpa [hcontra] using this
            have hlt : a₀_new < cfg₀'.nextAddr := hwfcf₀1.1 a₀_new (by simpa using hcontains)
            have : cfg₀'.nextAddr < cfg₀'.nextAddr := by simp [ha₀_new] at hlt
            exact Nat.lt_irrefl cfg₀'.nextAddr this
          have hne1 : a1 ≠ a₁_new := by
            intro hcontra
            have hcontains : cfg₁'.memory.contains a₁_new := by
              have : cfg₁'.memory.contains a1 := Memory_contains_of_lookup hm1
              simpa [hcontra] using this
            have hlt : a₁_new < cfg₁'.nextAddr := hwfcf₁1.1 a₁_new (by simpa using hcontains)
            have : cfg₁'.nextAddr < cfg₁'.nextAddr := by simp [ha₁_new] at hlt
            exact Nat.lt_irrefl cfg₁'.nextAddr this
          have hreal0' : θ₀'.lookup l' = some a0 := by
            rw [hθ₀def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l') (addr := a₀_new) h_eq] using hreal0
          have hreal1' : θ₁'.lookup l' = some a1 := by
            rw [hθ₁def]
            simpa [RealizationMap_lookup_update_ne (θ := θ₁1) (l := l) (l' := l') (addr := a₁_new) h_eq] using hreal1
          have hm0' : cf₀.memory.lookup a0 = some m0 := by
            rw [hmem₀]
            have hEq :=
              Memory_lookup_update_ne (μ := cfg₀'.memory) (a := a0) (a' := a₀_new) (v := n₀) hne0
            simpa [hEq] using hm0
          have hm1' : cf₁.memory.lookup a1 = some m1 := by
            rw [hmem₁]
            have hEq :=
              Memory_lookup_update_ne (μ := cfg₁'.memory) (a := a1) (a' := a₁_new) (v := n₁) hne1
            simpa [hEq] using hm1
          have hagree' :
              agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' qt (Value.num m0) (Value.num m1) :=
            agreeValueUnder_clean_extends hclean hθext₀'.1 hθext₁'.1 hagree
          exact agreeLocUnder.agree_values l' qt a0 a1 m0 m1 hreal0' hreal1' hm0' hm1' hagree'
  · intro x qt hlookup hclean
    have hlookup_old : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    have hagree_old := hagree_clean_e.2 x qt hlookup_old hclean
    cases hagree_old with
    | both_none _ _ hnone0 hnone1 =>
        refine agreeVarUnder.both_none x qt ?_ ?_
        · simpa [hvar₀] using hnone0
        · simpa [hvar₁] using hnone1
    | agree_values _ _ v0 v1 hlook0 hlook1 hagree =>
        have hagree' :
            agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' qt v0 v1 :=
          agreeValueUnder_clean_extends hclean hθext₀'.1 hθext₁'.1 hagree
        refine agreeVarUnder.agree_values x qt v0 v1 ?_ ?_ hagree'
        · simpa [hvar₀] using hlook0
        · simpa [hvar₁] using hlook1

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

private lemma typecheckExpr_ite_succ (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.ite e1 e2 e3) (fuel + 1) = typecheckIf ctx e1 e2 e3 fuel := by
  simp [typecheckExpr]

private lemma typecheckExpr_app_succ (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.app e1 e2) (fuel + 1) = typecheckApp ctx e1 e2 fuel := by
  simp [typecheckExpr]

private lemma opEType_ne_ref (op : Op) (et1 et2 : ETyp) (t : ETyp) (ls : LocSet) :
  opEType? op et1 et2 ≠ some (ETyp.ref t ls) := by
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?]

private lemma opEType_implies_nonfun (op : Op) (et1 et2 result : ETyp) :
  opEType? op et1 et2 = some result →
  et1.isFunctionType = false ∧ et2.isFunctionType = false ∧ result.isFunctionType = false := by
  intro h
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?] at h <;> cases h <;>
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]

private lemma opUnaryEType_ne_ref (op : UnaryOp) (et1 : ETyp) (t : ETyp) (ls : LocSet) :
  opUnaryEType? op et1 ≠ some (ETyp.ref t ls) := by
  cases op
  cases et1 <;> simp [opUnaryEType?]

private lemma opUnaryEType_implies_nonfun (op : UnaryOp) (et1 result : ETyp) :
  opUnaryEType? op et1 = some result →
  et1.isFunctionType = false ∧ result.isFunctionType = false := by
  intro h
  cases op with
  | not =>
      cases et1 with
      | int =>
          cases h
      | bool =>
          cases h
          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
      | unit =>
          cases h
      | string =>
          cases h
      | ref t ls =>
          cases h
      | arrow st1 st2 p tcls =>
          cases h
      | parrow st1 st2 p tcls =>
          cases h

-- IOFree-restricted induction hypothesis type for stepFR_* lemmas
abbrev StepFR_IH (predSat : PredSat) (fuel : Nat) : Prop :=
  ∀ m < fuel, ∀ (e : Expr) (ctxᵢ : TypeContext),
    ∀ (res : TypeResult), typecheck ctxᵢ e m = .ok res → ∀ (R : Regime), StepFR .ioFree ctxᵢ R e res predSat

private lemma stepFR_literal
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hpoison : res.qualType.poison = false)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFR mode ctx R e res predSat := by
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for literals
  have ⟨hcf₀, ho₀⟩ := terminatesTo_literal_inv' mode e v hval
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_literal_inv' mode e v hval
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  -- StepFR existential has structure:
  -- ∃ θ₀' θ₁', wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
  --   wfTypeContext (ctxAfter ctx res) ∧ wfConfig cf₀ ∧ wfConfig cf₁ ∧
  --   runtimeInstantiatesCtx ... ∧ runtimeInstantiatesCtx ... ∧
  --   regimeConsistentWithCtx ... ∧ agreeOnClean ... ∧ resultAgreesIfClean ...
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfTypeContext (ctxAfter ctx res)
    simpa [hctxAfter] using hwf
  · -- runtimeInstantiatesCtx for θ₀' (literal doesn't change context, configs unchanged)
    simpa [hctxAfter] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [hctxAfter] using hric₁
  · -- regimeConsistentWithCtx (literal doesn't change context)
    simpa [hctxAfter] using hreg
  · -- agreeOnClean for updated context (literal doesn't change context)
    simpa [hctxAfter] using hagree
  · -- resultAgreesIfClean
    intro _hclean
    have hval' : o₀ = o₁ := by
      simp [ho₀, ho₁]
    exact agreeValueUnder.clean_eq_nonref hpoison hnotfun hnotref hval'

private lemma stepFR_var
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ R (Expr.var name) res predSat := by
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have htagR : tagEnvConsistentWithRegime ctxᵢ.tagEnv R := hreg.1
  -- Use inversion lemma to extract config and value
  have hinv₀ := terminatesTo_var_inv' mode name
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have hinv₁ := terminatesTo_var_inv' mode name
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hinv₀ with ⟨v₀', hlookup₀, hcf₀, hv₀⟩
  rcases hinv₁ with ⟨v₁', hlookup₁, hcf₁, hv₁⟩
  -- Substitute: o₀ = v₀', o₁ = v₁'
  subst hv₀ hv₁
  -- After subst hcf₀/hcf₁, cf₀ and cf₁ become the original input configs
  subst hcf₀ hcf₁
  -- StepFR existential structure:
  -- ∃ θ₀' θ₁', wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
  --            wfTypeContext (ctxAfter ctx res) ∧
  --            wfConfig cf₀ ∧ wfConfig cf₁ ∧
  --            runtimeInstantiatesCtx ... ∧ runtimeInstantiatesCtx ... ∧
  --            regimeConsistentWithCtx ... ∧ agreeOnClean ... ∧ resultAgreesIfClean ...
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
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfTypeContext (ctxAfter ctxᵢ res): typecheckVar does not change the context
    simpa [ctxAfter, wfTypeContext, hmem, hnextLoc] using hwf
  · -- wfConfig cf₀ (unchanged since var doesn't modify config)
    exact hwfcfg₀
  · -- wfConfig cf₁ (unchanged since var doesn't modify config)
    exact hwfcfg₁
  · -- runtimeInstantiatesCtx for θ₀' (var doesn't change context or config)
    simpa [ctxAfter, hmem] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [ctxAfter, hmem] using hric₁
  · -- regimeConsistentWithCtx (var doesn't change tagEnv or nextTag)
    simpa [ctxAfter, regimeConsistentWithCtx, htag, hnextTag] using hreg
  · -- agreeOnClean for ctxAfter: typecheckVar doesn't change the context
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
              cases hclean with
              | clean hpoison_res =>
                  simpa [hres] using hpoison_res
              | guard k htag hreg _ =>
                  exfalso
                  simp [qtypGuardTag, hres] at htag
            have hpc_poison := joinPoison_eq_false hjoin
            have hpc : ctxᵢ.pc = false := hpc_poison.1
            have hpoison : qt.poison = false := hpc_poison.2
            have hclean_qt : qtypCleanUnder R qt := by
              exact qtypCleanUnder.clean hpoison
            have hvar := hvar_agree_of_clean hclean_qt
            have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
              agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
            have hres_eq : res.qualType = qt := by
              cases qt with
              | mk etyp poison pred =>
                  cases hpred
                  simp [hres, hpc, joinPoison]
            have hres_agree :
                agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
              simpa [hres_eq] using hval
            exact hres_agree
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
                | clean hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder R qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_eq : res.qualType = qt := by
                      cases qt with
                      | mk etyp poison pred =>
                          cases hpred
                          simp [hres, hpc, joinPoison]
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      simpa [hres_eq] using hval
                    simpa [hlookup₀, hlookup₁] using hres_agree
                | guard k' htag' hregime hnotfun_res =>
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hclean_qt : qtypCleanUnder R qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      have hnotfun_qt : qt.etyp.isFunctionType = false := by
                        simpa [hres] using hnotfun_res
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                        | poisoned_noPred_eq_nonref _ hpred' _ _ _ =>
                            have : Predicate.noPred = Predicate.guardOnly k := by
                              simpa [hpred] using hpred'.symm
                            cases this
                        | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Arrow types are function types, contradicting hnotfun_res
                            simp only [hres, hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.true_or] at hnotfun_res
                            cases hnotfun_res
                        | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                            -- dirty_internal_arrow requires isArrow = true, contradicting hnotfun_res
                            simp only [hres, ETyp.isFunctionType] at hnotfun_res
                            rw [hisArrow, Bool.true_or] at hnotfun_res
                            cases hnotfun_res
                        | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Parrow types are function types, contradicting hnotfun_res
                            simp only [hres, hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.or_true] at hnotfun_res
                            cases hnotfun_res
                        | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                            -- dirty_internal_parrow requires isParrow = true, contradicting hnotfun_res
                            simp only [hres, ETyp.isFunctionType] at hnotfun_res
                            rw [hisParrow, Bool.or_true] at hnotfun_res
                            cases hnotfun_res
                        | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                            have htagRes : qtypGuardTag res.qualType = some k := by
                              simp [qtypGuardTag, hres, hpred]
                            have hetyp' : res.qualType.etyp = qt.etyp := by
                              simp [hres]
                            exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                              hlookup1 hin1 hv1 hlookup2 hin2 hv2
                      | poisoned_noPred_ref _ hpred' _ _ _ _ _ _ _ =>
                          have : Predicate.noPred = Predicate.guardOnly k := by
                            simpa [hpred] using hpred'.symm
                          cases this
                      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
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
                              some false = R.lookup? k := by symm; exact hreg
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
                              some false = R.lookup? k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                    simpa [hlookup₀, hlookup₁] using hres_agree
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
                          cases hclean with
                          | clean hpoison_res =>
                              simpa [hres] using hpoison_res
                          | guard k_guard htag_guard hreg_guard _ =>
                              exfalso
                              simp [qtypGuardTag, hres] at htag_guard
                        have hregime : R.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder R qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          have hnotfun_qt : qt.etyp.isFunctionType = false := by
                            sorry  -- TODO: derive from context or add constraint
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref (by simp [hres, hpc]) hnotfun' hnotref' hEq
                          | poisoned_noPred_eq_nonref _ hpred' _ _ _ =>
                              have : Predicate.noPred = Predicate.guardOnly k := by
                                simpa [hpred] using hpred'.symm
                              cases this
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hclean' : internalPoisonClean res.qualType := by
                                simp only [internalPoisonClean] at hclean ⊢
                                simp only [getInternalPoison, hetyp'] at hclean ⊢
                                exact hclean
                              exact agreeValueUnder.clean_internal_arrow hclean' (hetyp'.trans hetyp) htcl hmatch hcap hv₁ hv₂
                          | dirty_internal_arrow _ _ =>
                              -- Dirty arrow: transport to result type
                              sorry
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hclean' : internalPoisonClean res.qualType := by
                                simp only [internalPoisonClean] at hclean ⊢
                                simp only [getInternalPoison, hetyp'] at hclean ⊢
                                exact hclean
                              exact agreeValueUnder.clean_internal_parrow hclean' (hetyp'.trans hetyp) htcl hmatch hcap hv₁ hv₂
                          | dirty_internal_parrow _ _ =>
                              -- Dirty parrow: transport to result type
                              sorry
                          | clean_ref _ hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin1 hv1 hlookup2 hin2 hv2
                          | poisoned_noPred_ref _ hpred' hetyp _ _ _ _ _ _ =>
                              have : Predicate.noPred = Predicate.guardOnly k := by
                                simpa [hpred] using hpred'.symm
                              cases this
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotfun' hnotref' hEq
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
                                  some false = R.lookup? k := by symm; exact hreg
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
                                  some false = R.lookup? k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                        simpa [hlookup₀, hlookup₁] using hres_agree
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
                        exfalso
                        cases hclean with
                        | clean hpoison =>
                            have : false = true := by
                              calc
                                false = res.qualType.poison := by symm; exact hpoison
                                _ = true := by simp [hres]
                            cases this
                        | guard k_guard htag_guard hreg_guard _ =>
                            simp [qtypGuardTag, hres] at htag_guard
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
                | clean hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder R qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      have hqt_eq : qt = ⟨qt.etyp, false, qt.pred⟩ := by
                        cases qt with
                        | mk etyp poison pred =>
                            simpa [hpoison]
                      have hres_eq : res.qualType = qt := by
                        have : res.qualType = ⟨qt.etyp, false, qt.pred⟩ := by
                          simp [hres, hpoison, hpc, joinPoison]
                        exact this.trans hqt_eq.symm
                      simpa [hres_eq] using hval
                    simpa [hlookup₀, hlookup₁] using hres_agree
                | guard k' htag' hregime hnotfun_res =>
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hclean_qt : qtypCleanUnder R qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      have hnotfun_qt : qt.etyp.isFunctionType = false := by
                        simpa [hres] using hnotfun_res
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                      | poisoned_noPred_eq_nonref _ hpred' _ _ _ =>
                          have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                            calc
                              Predicate.noPred = qt.pred := by symm; exact hpred'
                              _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                          cases this
                        | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Guard predicate + arrow type combination
                            sorry
                        | dirty_internal_arrow _ _ =>
                            sorry
                        | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Guard predicate + parrow type combination
                            sorry
                        | dirty_internal_parrow _ _ =>
                            sorry
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
                      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
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
                              some false = R.lookup? k := by symm; exact hreg
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
                              some false = R.lookup? k := by symm; exact hreg
                              _ = some true := by exact hregime
                          cases this
                    simpa [hlookup₀, hlookup₁] using hres_agree
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
                          cases hclean with
                          | clean hpoison => simpa [hres] using hpoison
                          | guard k_guard htag_guard hreg_guard _ =>
                              exfalso
                              simp [qtypGuardTag, hres] at htag_guard
                        have hregime : R.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder R qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          have hnotfun_qt : qt.etyp.isFunctionType = false := by
                            sorry  -- TODO: derive from context or add constraint
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotfun' hnotref' hEq
                          | poisoned_noPred_eq_nonref _ hpred' _ _ _ =>
                              have : Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env := by
                                calc
                                  Predicate.noPred = qt.pred := by symm; exact hpred'
                                  _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hpred
                              cases this
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hclean' : internalPoisonClean res.qualType := by
                                simp only [internalPoisonClean] at hclean ⊢
                                simp only [getInternalPoison, hetyp'] at hclean ⊢
                                exact hclean
                              exact agreeValueUnder.clean_internal_arrow hclean' (hetyp'.trans hetyp) htcl hmatch hcap hv₁ hv₂
                          | dirty_internal_arrow _ _ =>
                              -- Dirty arrow: transport to result type
                              sorry
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hclean' : internalPoisonClean res.qualType := by
                                simp only [internalPoisonClean] at hclean ⊢
                                simp only [getInternalPoison, hetyp'] at hclean ⊢
                                exact hclean
                              exact agreeValueUnder.clean_internal_parrow hclean' (hetyp'.trans hetyp) htcl hmatch hcap hv₁ hv₂
                          | dirty_internal_parrow _ _ =>
                              -- Dirty parrow: transport to result type
                              sorry
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
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref hpoison' hnotfun' hnotref' hEq
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
                                  some false = R.lookup? k := by symm; exact hreg
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
                                  some false = R.lookup? k := by symm; exact hreg
                                  _ = some true := by exact hregime
                              cases this
                        simpa [hlookup₀, hlookup₁] using hres_agree
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
                        exfalso
                        cases hclean with
                        | clean hpoison =>
                            have : false = true := by
                              calc
                                false = res.qualType.poison := by symm; exact hpoison
                                _ = true := by simp [hres]
                            cases this
                        | guard k_guard htag_guard hreg_guard _ =>
                            simp [qtypGuardTag, hres] at htag_guard

-- World-free version of stepFRW_op
-- TODO: Needs refactoring - StepFR structure changed and terminatesTo lemmas need adjusting
private lemma stepFR_op
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.op e1 op e2) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckOp ctxᵢ e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag,
          h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctxᵢ e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext :=
    { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ res1 htc1' R
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res2 htc2' R
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for binary op
  have hstruct₀ := terminatesTo_op_inv' e1 op e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, v₀2, ht₀_e1, ht₀_e2, h_evalop₀, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_op_inv' e1 op e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, v₁2, ht₁_e1, ht₁_e2, h_evalop₁, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
  -- Prepare for IH2: need wf maps and agreement for ctx'
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [ctx', ctxAfter] using hwf1
  -- runtimeInstantiatesCtx and regimeConsistentWithCtx come directly from IH1
  -- Just need to transfer from ctxAfter ctxᵢ res1 to ctx' (which are equal)
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hric₁1
  have htagR1' : regimeConsistentWithCtx ctx' R := by
    simpa [ctx', ctxAfter] using htagR1
  have hagree_clean1' :
      agreeOnClean predSat R ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hagree_clean1
  -- Apply IH for e2
  -- Note: cfg₀1.pureMode = cfg₁1.pureMode = pm (from inversion lemmas)
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  -- Convert ht₁_e2 to use cfg₀1.pureMode
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cf₁ v₁2 := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e2 :=
    hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ v₀2 v₁2
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag]
  have hagree_clean :
      agreeOnClean predSat R (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) R := by
    simpa [hctxAfter] using htagR2
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hagree_clean, ?_⟩
  · simpa [hctxAfter] using hwf2
  intro hclean
  have hpoison_res : res.qualType.poison = false := by
    cases hclean with
    | clean hpoison => exact hpoison
    | guard k htag hreg _ =>
        exfalso
        simp [qtypGuardTag, h_ret_pred] at htag
  have hjoin :
      joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
    calc
      joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) =
          res.qualType.poison := by symm; exact h_ret_poison
      _ = false := by exact hpoison_res
  have hjoin_pc := joinPoison_eq_false hjoin
  have hjoin_12 := joinPoison_eq_false hjoin_pc.2
  have hclean1 : qtypCleanUnder R res1.qualType := qtypCleanUnder.clean hjoin_12.1
  have hclean2 : qtypCleanUnder R res2.qualType := qtypCleanUnder.clean hjoin_12.2
  have hagree_v1 :
      agreeValueUnder predSat R cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 :=
    hres_agree1 hclean1
  have hagree_v2 :
      agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType v₀2 v₁2 :=
    hres_agree2 hclean2
  have hnotref1 : ¬ ∃ t ls, res1.qualType.etyp = ETyp.ref t ls := by
    intro ⟨t, ls, h_etyp⟩
    have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
      simp [h_etyp, opEType?]
    rw [hnone] at h_op; cases h_op
  have hnotref2 : ¬ ∃ t ls, res2.qualType.etyp = ETyp.ref t ls := by
    intro ⟨t, ls, h_etyp⟩
    have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
      simp [h_etyp, opEType?]
    rw [hnone] at h_op; cases h_op
  have hnonfun_args :
      res1.qualType.etyp.isFunctionType = false ∧
      res2.qualType.etyp.isFunctionType = false ∧
      result_etyp.isFunctionType = false :=
    opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op
  have hv1Eq : v₀1 = v₁1 :=
    agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hnonfun_args.1 hagree_v1
  have hv2Eq : v₀2 = v₁2 :=
    agreeValueUnder_nonref_eq_of_clean hclean2 hnotref2 hnonfun_args.2.1 hagree_v2
  have hEval₁' : LeanPoison.evalOp op v₀1 v₀2 = some o₁ := by
    simpa [hv1Eq, hv2Eq] using h_evalop₁
  have hEq : o₀ = o₁ := by
    have : some o₀ = some o₁ := by
      calc some o₀ = LeanPoison.evalOp op v₀1 v₀2 := by symm; exact h_evalop₀
           _ = some o₁ := hEval₁'
    exact Option.some.inj this
  have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
    intro ⟨t, ls, h_etyp⟩
    have h_etyp' : result_etyp = ETyp.ref t ls := by simpa [h_ret_etyp] using h_etyp
    have h_op' : opEType? op res1.qualType.etyp res2.qualType.etyp = some (ETyp.ref t ls) := by
      simpa [h_etyp'] using h_op
    exact (opEType_ne_ref op res1.qualType.etyp res2.qualType.etyp t ls) h_op'
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    simpa [h_ret_etyp] using hnonfun_args.2.2
  exact agreeValueUnder.clean_eq_nonref hpoison_res hnotfun_res hnotref hEq

-- World-free version of stepFRW_unaryop
private lemma stepFR_unaryop
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (op : UnaryOp) (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.unaryop op e) res predSat := by
  have htc' : typecheckUnaryOp ctxᵢ op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctxᵢ op e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ res1 htc1' R
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for unaryop
  have hstruct₀ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', v₀', ht₀_e, h_evalop₀, hmem₀, hvar₀, _hnext₀, _hpure₀⟩
  have hstruct₁ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', v₁', ht₁_e, h_evalop₁, hmem₁, hvar₁, _hnext₁, _hpure₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', hreg', hagree_clean_e, hres_agree_e⟩
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
  have hagree_clean :
      agreeOnClean predSat R (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) R := by
    simpa [hctxAfter] using hreg'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hagree_clean, ?_⟩
  · simpa [hctxAfter] using hwf'
  intro hclean
  have hpoison_res : res.qualType.poison = false := by
    cases hclean with
    | clean hpoison => exact hpoison
    | guard k htag hreg _ =>
        exfalso
        simp [qtypGuardTag, h_ret_pred] at htag
  have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
    calc
      joinPoison ctxᵢ.pc res1.qualType.poison = res.qualType.poison := by
        symm
        exact h_ret_poison
      _ = false := by exact hpoison_res
  have hres1_poison : res1.qualType.poison = false :=
    (joinPoison_eq_false hjoin).2
  have hclean1 : qtypCleanUnder R res1.qualType := by
    exact qtypCleanUnder.clean hres1_poison
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
  have hnonfun_arg : res1.qualType.etyp.isFunctionType = false ∧ result_etyp.isFunctionType = false :=
    opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op
  have hvEq : v₀' = v₁' :=
    agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hnonfun_arg.1 hagree_v
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
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    simpa [h_ret_etyp] using hnonfun_arg.2
  exact agreeValueUnder.clean_eq_nonref hpoison_res hnotfun_res hnotref hEq

-- World-free version of stepFRW_newRef
private lemma stepFR_newRef
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.newRef e) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckNewRef ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, l, etyp, htc1, hl, h_etyp1, h_etyp, h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ res1 htc1' R
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for newRef
  have hstruct₀ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', n₀, ht₀_e, ho₀, hmem₀, hnext₀, hvar₀, hpm₀⟩
  have hstruct₁ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', n₁, ht₁_e, ho₁, hmem₁, hnext₁, hvar₁, hpm₁⟩
  -- Apply IH for e
  have hstep_e :=
    hIH μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.num n₀) (Value.num n₁)
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean_e, hres_agree_e⟩
  -- Fresh logical location l = res1.nextLoc' is not realized after evaluating e
  have h_fresh₀ : θ₀1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg₀'.memory cfg₀'.varEnv θ₀1 l hwf1 hric₀1 hge
  have h_fresh₁ : θ₁1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg₁'.memory cfg₁'.varEnv θ₁1 l hwf1 hric₁1 hge
  -- Extended maps: θ₀' = θ₀1.update l cfg₀'.nextAddr, θ₁' = θ₁1.update l cfg₁'.nextAddr
  let θ₀' := θ₀1.update l cfg₀'.nextAddr
  let θ₁' := θ₁1.update l cfg₁'.nextAddr
  -- Prove wfExtendsMap for the extended maps
  have hθext₀' : wfExtendsMap θ₀1 θ₀' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst h_eq; rw [h_fresh₀] at hlookup; cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have h_theta_def : θ₀' = θ₀1.insert l cfg₀'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]; simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]; exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ₀1.get? l' ≠ some cfg₀'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ₀1.lookup l' = some cfg₀'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]; exact h_eq
        have h_contains : cfg₀'.memory.contains cfg₀'.nextAddr := (hric₀1.1 l' cfg₀'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg₀'.nextAddr (hwfcf₀1.1 cfg₀'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a, θ₀1.get? k₁ = some a → θ₀1.get? k₂ = some a → k₁ = k₂ := by
        intro k₁ k₂ a h1 h2; exact hWF k₁ k₂ a h1 h2
      have hlookup1' : (θ₀1.insert l cfg₀'.nextAddr).get? l₁ = some a := hlookup1
      have hlookup2' : (θ₀1.insert l cfg₀'.nextAddr).get? l₂ = some a := hlookup2
      exact ExtTreeMap_insert_preserves_injectivity θ₀1 l cfg₀'.nextAddr h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
  have hθext₁' : wfExtendsMap θ₁1 θ₁' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst l'; rw [h_fresh₁] at hlookup; cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have h_theta_def : θ₁' = θ₁1.insert l cfg₁'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]; simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]; exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ₁1.get? l' ≠ some cfg₁'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ₁1.lookup l' = some cfg₁'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]; exact h_eq
        have h_contains : cfg₁'.memory.contains cfg₁'.nextAddr := (hric₁1.1 l' cfg₁'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg₁'.nextAddr (hwfcf₁1.1 cfg₁'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a, θ₁1.get? k₁ = some a → θ₁1.get? k₂ = some a → k₁ = k₂ := by
        intro k₁ k₂ a h1 h2; exact hWF k₁ k₂ a h1 h2
      have hlookup1' : (θ₁1.insert l cfg₁'.nextAddr).get? l₁ = some a := hlookup1
      have hlookup2' : (θ₁1.insert l cfg₁'.nextAddr).get? l₂ = some a := hlookup2
      exact ExtTreeMap_insert_preserves_injectivity θ₁1 l cfg₁'.nextAddr h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
  -- Prove wfTypeContext for result
  have hwf_result : wfTypeContext (ctxAfter ctxᵢ res) := by
    intro l' hcontains
    simp [ctxAfter] at hcontains ⊢
    rw [h_mem] at hcontains
    rw [h_loc]
    by_cases h_eq : l' = l
    · subst h_eq; rw [hl]; exact Nat.lt_succ_self res1.nextLoc'
    · have hmem : l' ∈ updateMemEnv res1.memEnv' l ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩ :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have h_isSome : ((updateMemEnv res1.memEnv' l ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩)[l']?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      have h_cmp_ne : compare l l' ≠ Ordering.eq := by
        intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
      have h_isSome' : (res1.memEnv'[l']?).isSome = true := by
        simpa [updateMemEnv, ExtTreeMap.getElem?_insert, h_cmp_ne] using h_isSome
      have hmem' : l' ∈ res1.memEnv' := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 h_isSome'
      have hcontains' : res1.memEnv'.contains l' = true := (Std.ExtTreeMap.contains_iff_mem).2 hmem'
      have hlt : l' < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l' := by simpa [ctxAfter] using hcontains'
        exact hwf1 l' this
      exact Nat.lt_succ_of_lt hlt
  -- Prove runtimeInstantiatesCtx for θ₀'
  have hric₀' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    unfold runtimeInstantiatesCtx
    rcases hric₀1 with ⟨hmem₀1, hvars₀1⟩
    constructor
    · intro l' a hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a = cfg₀'.nextAddr := by
          have hself : θ₀'.lookup l = some cfg₀'.nextAddr := by simp [θ₀', RealizationMap.update, RealizationMap.lookup]
          have : (some a : Option Address) = some cfg₀'.nextAddr := by
            calc some a = θ₀'.lookup l := by symm; exact hlookup
                 _ = some cfg₀'.nextAddr := by exact hself
          exact Option.some.inj this
        subst a
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by rw [h_mem]; simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf₀.memory.contains cfg₀'.nextAddr := by
          rw [hmem₀]; simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have hlookup_old : θ₀1.lookup l' = some a := by
          have hget : (θ₀1.insert l cfg₀'.nextAddr).get? l' = some a := by
            simpa [θ₀', RealizationMap.update, RealizationMap.lookup] using hlookup
          have hElem : (θ₀1.insert l cfg₀'.nextAddr)[l']? = some a := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hget
          have hElem2 : θ₀1[l']? = some a := by simpa [ExtTreeMap.getElem?_insert, hcmp] using hElem
          have : θ₀1.get? l' = some a := by simpa [ExtTreeMap.get?_eq_getElem?] using hElem2
          simpa [RealizationMap.lookup] using this
        have hmem := hmem₀1 l' a hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by simpa [ctxAfter] using hmem.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]; simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf₀.memory.contains a := by
          have hμ1 : cfg₀'.memory.contains a := hmem.2
          rw [hmem₀, ExtTreeMap.contains_insert]; simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₀1 (by simpa [ctxAfter] using hlookup)
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar₀] using hvlookup
      · exact valueHasETyp_extends hθext₀'.1 hvtyp
  -- Prove runtimeInstantiatesCtx for θ₁'
  have hric₁' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    unfold runtimeInstantiatesCtx
    rcases hric₁1 with ⟨hmem₁1, hvars₁1⟩
    constructor
    · intro l' a hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a = cfg₁'.nextAddr := by
          have hself : θ₁'.lookup l = some cfg₁'.nextAddr := by simp [θ₁', RealizationMap.update, RealizationMap.lookup]
          have : (some a : Option Address) = some cfg₁'.nextAddr := by
            calc some a = θ₁'.lookup l := by symm; exact hlookup
                 _ = some cfg₁'.nextAddr := by exact hself
          exact Option.some.inj this
        subst a
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by rw [h_mem]; simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf₁.memory.contains cfg₁'.nextAddr := by
          rw [hmem₁]; simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have hlookup_old : θ₁1.lookup l' = some a := by
          have hget : (θ₁1.insert l cfg₁'.nextAddr).get? l' = some a := by
            simpa [θ₁', RealizationMap.update, RealizationMap.lookup] using hlookup
          have hElem : (θ₁1.insert l cfg₁'.nextAddr)[l']? = some a := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hget
          have hElem2 : θ₁1[l']? = some a := by simpa [ExtTreeMap.getElem?_insert, hcmp] using hElem
          have : θ₁1.get? l' = some a := by simpa [ExtTreeMap.get?_eq_getElem?] using hElem2
          simpa [RealizationMap.lookup] using this
        have hmem := hmem₁1 l' a hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by simpa [ctxAfter] using hmem.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]; simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf₁.memory.contains a := by
          have hμ1 : cfg₁'.memory.contains a := hmem.2
          rw [hmem₁, ExtTreeMap.contains_insert]; simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁1 (by simpa [ctxAfter] using hlookup)
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar₁] using hvlookup
      · exact valueHasETyp_extends hθext₁'.1 hvtyp
  -- Prove regimeConsistentWithCtx
  have hreg' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) R := by
    simpa [regimeConsistentWithCtx, ctxAfter, h_tag, h_ntag] using htagR1
  -- Prove agreeOnClean
  have hagree_clean :
      agreeOnClean predSat R (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' :=
    agreeOnClean_newRef_extend
      predSat R ctxᵢ res1 res l etyp
      cfg₀' cfg₁' cf₀ cf₁ n₀ n₁ cfg₀'.nextAddr cfg₁'.nextAddr θ₀1 θ₁1 θ₀' θ₁'
      h_mem h_etyp1.symm rfl rfl hmem₀ hmem₁ hvar₀ hvar₁ rfl rfl
      hθext₀' hθext₁' hwfcf₀1 hwfcf₁1 hagree_clean_e hres_agree_e
  -- Derive wfConfig for final configs
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  refine ⟨θ₀', θ₁', ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀', hric₁', hreg', hagree_clean, ?_⟩
  · -- wfExtendsMap θ₀ θ₀'
    exact wfExtendsMap_trans hθext₀1 hθext₀'
  · -- wfExtendsMap θ₁ θ₁'
    exact wfExtendsMap_trans hθext₁1 hθext₁'
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    exact hwf_result
  · -- resultAgreesIfClean
    intro hclean
    have hpoison_res : res.qualType.poison = false := by
      cases hclean with
      | clean hpoison => exact hpoison
      | guard k htag hreg _ =>
          exfalso
          simp [qtypGuardTag, h_pred] at htag
    have hlookup1 : θ₀'.lookup l = some cfg₀'.nextAddr := by
      simp [RealizationMap.lookup]; rw [← ExtTreeMap.get?_eq_getElem?]; exact ExtTreeMap.getElem?_insert_self
    have hlookup2 : θ₁'.lookup l = some cfg₁'.nextAddr := by
      simp [RealizationMap.lookup]; rw [← ExtTreeMap.get?_eq_getElem?]; exact ExtTreeMap.getElem?_insert_self
    have hin1 : l ∈ LocSet.singleton l := by simp [LocSet.singleton]
    have hin2 : l ∈ LocSet.singleton l := by simp [LocSet.singleton]
    exact agreeValueUnder.clean_ref hpoison_res h_etyp hlookup1 hin1 ho₀ hlookup2 hin2 ho₁

-- World-free version of stepFRW_seq
private lemma stepFR_seq
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.seq e1 e2) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckSeq ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_seq_succ] at htc
    exact htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ res1 htc1' R
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res htc2' R
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for seq
  have hstruct₀ := terminatesTo_seq_inv' e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, ht₀_e1, ht₀_e2, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_seq_inv' e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, ht₁_e1, ht₁_e2, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
  -- Prepare for IH2
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
  -- hric₀1, hric₁1, htagR1 are already extracted from hstep_e1 for (ctxAfter ctxᵢ res1)
  -- Since ctx' = ctxAfter ctxᵢ res1, we convert them
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [hctx', ctxAfter] using hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', ctxAfter] using hric₁1
  have htagR1' : regimeConsistentWithCtx ctx' R := by
    simpa [hctx', ctxAfter] using htagR1
  have hagree_clean1' :
      agreeOnClean predSat R ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', ctxAfter] using hagree_clean1
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1; simp only [Config.mk.injEq, true_and]; exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by rw [← hcfg₁1_eq]; exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]; exact hwfcf₁1
  -- Apply IH for e2
  have hstep_e2 :=
    hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res := by
    simp [ctxAfter, hctx', updateCtxFromResult]
  have hagree_clean :
      agreeOnClean predSat R (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) R := by
    simpa [hctxAfter] using htagR2
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hagree_clean, ?_⟩
  · simpa [hctxAfter] using hwf2
  -- Since res is directly the result of e2, hres_agree2 gives us the result directly
  exact hres_agree2

-- World-free version of stepFRW_vlet
private lemma stepFR_vlet
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.vlet vname e1 e2) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckVlet ctxᵢ vname e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_vlet_succ] at htc
    exact htc
  obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, h_tag, h_loc, h_ntag,
          h_ret_poison, h_ret_pred⟩ :=
    typecheckVlet_structure ctxᵢ vname e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ res1 htc1' R
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res2 htc2' R
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for vlet
  have hstruct₀ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, cfg₀3, ht₀_e1, ht₀_e2, hcf₀_eq, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, cfg₁3, ht₁_e1, ht₁_e2, hcf₁_eq, hpm₁1, hpm₁2⟩
  -- Define intermediate configs with extended varEnv
  let cfg₀2 : Config := { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 }
  let cfg₁2 : Config := { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 }
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
  -- Prepare for IH2
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
  have hric₀1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxAfter] using hric₀1
  have hric₁1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxAfter] using hric₁1
  -- Get value types using preservation with defaultWorld
  let w_default := LeanProofs.defaultWorld
  -- TODO: check why we using w_default here
  have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 v₀1 := by
    rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
    exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
  have ht₁_e1_w : terminatesToW .ioFree w_default w_default e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 v₁1 := by
    rcases ht₁_e1 with ⟨fuel₁, verbose₁, hpure₁⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
    exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
  have hv₀1_typed : valueHasETyp θ₀1 v₀1 res1.qualType.etyp :=
    (preservation_valueW .ioFree e1 ctxᵢ fuel' res1 μ₀ cfg₀1.memory ρ₀ cfg₀1.varEnv θ₀ θ₀1
      a₀ cfg₀1.nextAddr pm cfg₀1.pureMode v₀1 w_default w_default
      hwf htc1' hθ₀ hθ₀1wf hθext₀1 hric₀ hric₀1_mem ht₀_e1_w).1
  have hv₁1_typed : valueHasETyp θ₁1 v₁1 res1.qualType.etyp :=
    (preservation_valueW .ioFree e1 ctxᵢ fuel' res1 μ₁ cfg₁1.memory ρ₁ cfg₁1.varEnv θ₁ θ₁1
      a₁ cfg₁1.nextAddr pm cfg₁1.pureMode v₁1 w_default w_default
      hwf htc1' hθ₁ hθ₁1wf hθext₁1 hric₁ hric₁1_mem ht₁_e1_w).1
  have hv₀1_wf : wfValue cfg₀1.nextAddr v₀1 :=
    (wfConfig_preservedW .ioFree w_default w_default e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 v₀1 ht₀_e1_w hwfcfg₀).2
  have hv₁1_wf : wfValue cfg₁1.nextAddr v₁1 :=
    (wfConfig_preservedW .ioFree w_default w_default e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 v₁1 ht₁_e1_w hwfcfg₁).2
  have hreg_ctx' : regimeConsistentWithCtx ctx' R := by
    simpa [hctx', ctxAfter] using htagR1
  -- runtimeInstantiatesCtx for extended configs
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
    unfold runtimeInstantiatesCtx at hric₀1 ⊢
    rcases hric₀1 with ⟨hmem₀1, hvars₀1⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₀1 l a hlookup
      simpa [hctx', ctxAfter, cfg₀2] using hmem
    · intro w qt hlookup
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxᵢ.varEnv.update w res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv w res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update w res1.qualType).lookup w := by symm; exact hlookup'
                 _ = some res1.qualType := by exact h
          exact Option.some.inj this
        have hlookup_var : cfg₀2.varEnv.lookup w = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        refine ⟨v₀1, hlookup_var, ?_⟩
        simpa [hqt] using hv₀1_typed
      · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₀1 hlookup_ctx
        have hvlookup' : cfg₀2.varEnv.lookup w = some v := by
          simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hvlookup
        exact ⟨v, hvlookup', hvtyp⟩
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    unfold runtimeInstantiatesCtx at hric₁1 ⊢
    rcases hric₁1 with ⟨hmem₁1, hvars₁1⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₁1 l a hlookup
      simpa [hctx', ctxAfter, cfg₁2] using hmem
    · intro w qt hlookup
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxᵢ.varEnv.update w res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv w res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update w res1.qualType).lookup w := by symm; exact hlookup'
                 _ = some res1.qualType := by exact h
          exact Option.some.inj this
        have hlookup_var : cfg₁2.varEnv.lookup w = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        refine ⟨v₁1, hlookup_var, ?_⟩
        simpa [hqt] using hv₁1_typed
      · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁1 hlookup_ctx
        have hvlookup' : cfg₁2.varEnv.lookup w = some v := by
          simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hvlookup
        exact ⟨v, hvlookup', hvtyp⟩
  -- wfConfig for extended configs
  have hwfcfg₀2 : wfConfig cfg₀2 := by
    rcases hwfcf₀1 with ⟨hwfmem₀, hwfenv₀⟩
    refine ⟨?_, ?_⟩
    · simpa [cfg₀2] using hwfmem₀
    · have hwfenv₀' : wfVarEnv cfg₀1.nextAddr ((vname, v₀1) :: cfg₀1.varEnv) :=
        wfVarEnv.cons vname v₀1 cfg₀1.varEnv hv₀1_wf hwfenv₀
      simpa [cfg₀2, VarEnv.update] using hwfenv₀'
  have hwfcfg₁2 : wfConfig cfg₁2 := by
    rcases hwfcf₁1 with ⟨hwfmem₁, hwfenv₁⟩
    refine ⟨?_, ?_⟩
    · simpa [cfg₁2] using hwfmem₁
    · have hwfenv₁' : wfVarEnv cfg₁1.nextAddr ((vname, v₁1) :: cfg₁1.varEnv) :=
        wfVarEnv.cons vname v₁1 cfg₁1.varEnv hv₁1_wf hwfenv₁
      simpa [cfg₁2, VarEnv.update] using hwfenv₁'
  -- agreeOnClean for extended configs
  have hagree_clean1' :
      agreeOnClean predSat R ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    constructor
    · intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hagree_loc := (hagree_clean1.1 l qt hlookup' hclean)
      simpa [cfg₀2, cfg₁2] using hagree_loc
    · intro w qt hlookup hclean
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxᵢ.varEnv.update w res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv w res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update w res1.qualType).lookup w := by symm; exact hlookup'
                 _ = some res1.qualType := by exact h
          exact Option.some.inj this
        have hlookup₀ : cfg₀2.varEnv.lookup w = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        have hlookup₁ : cfg₁2.varEnv.lookup w = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        have hclean1 : qtypCleanUnder R res1.qualType := by simpa [hqt] using hclean
        have hagree_val : agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 := by
          have hagree := hres_agree1 hclean1
          simpa [cfg₀2, cfg₁2] using hagree
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
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hlookup₀
            have hlookup₁' : cfg₁2.varEnv.lookup w = some v₁ := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hlookup₁
            have hagree' : agreeValueUnder predSat R cfg₀2.memory cfg₁2.memory θ₀1 θ₁1 qt v₀ v₁ := by
              simpa [cfg₀2, cfg₁2] using hagree
            exact agreeVarUnder.agree_values w qt v₀ v₁ hlookup₀' hlookup₁' hagree'
        | both_none _ _ hnone₀ hnone₁ =>
            have hnone₀' : cfg₀2.varEnv.lookup w = none := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hnone₀
            have hnone₁' : cfg₁2.varEnv.lookup w = none := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hnone₁
            exact agreeVarUnder.both_none w qt hnone₀' hnone₁'
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₀2_eq : cfg₀2 = { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 } := rfl
  have hcfg₁2_eq : cfg₁2 = { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 } := rfl
  -- Convert ht₁_e2 to have matching pureMode
  have ht₁_e2' : terminatesTo .ioFree e2 { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } cfg₁3 o₁ := by
    have hcfg_eq : ({ cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 } : Config) =
                   { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
      simp [hpm_eq]
    rw [← hcfg_eq]; exact ht₁_e2
  -- wfConfig for cfg₁2 with adjusted pureMode
  have hwfcfg₁2' : wfConfig { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
    have hcfg_eq : cfg₁2 = { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
      simp [cfg₁2, hpm_eq]
    rw [← hcfg_eq]; exact hwfcfg₁2
  -- Apply IH for e2
  have hstep_e2 :=
    hIH2 cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀1 θ₁1
      cfg₀3 cfg₁3 o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' hreg_ctx' hRbound hagree_clean1'
      cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀3, hwfcf₁3, hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
  -- Combine map extensions
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  -- VarEnv preservation through e2
  have ht₀_e2_w : terminatesToW .ioFree w_default w_default e2 cfg₀2 cfg₀3 o₀ := by
    rcases ht₀_e2 with ⟨fuel₀, verbose₀, hpure₀⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
    exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
  have ht₁_e2_w : terminatesToW .ioFree w_default w_default e2 cfg₁2 cfg₁3 o₁ := by
    rcases ht₁_e2 with ⟨fuel₁, verbose₁, hpure₁⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
    exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
  have hvar_pres₀ : cfg₀3.varEnv = cfg₀2.varEnv := by
    symm
    rcases ht₀_e2_w with ⟨fuel₀', verbose₀', heval₀⟩
    exact beval_preserves_varEnv .ioFree e2 fuel₀' verbose₀' cfg₀2 cfg₀3 o₀ ⟨w_default, w_default, heval₀⟩
  have hvar_pres₁ : cfg₁3.varEnv = cfg₁2.varEnv := by
    symm
    rcases ht₁_e2_w with ⟨fuel₁', verbose₁', heval₁⟩
    exact beval_preserves_varEnv .ioFree e2 fuel₁' verbose₁' cfg₁2 cfg₁3 o₁ ⟨w_default, w_default, heval₁⟩
  -- Final runtimeInstantiatesCtx
  have hric₀'' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    unfold runtimeInstantiatesCtx
    rcases hric₀2 with ⟨hmem₂, _hvars₂⟩
    rcases hric₀1 with ⟨_hmem₁, hvars₁⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₂ l a hlookup
      simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcf₀_eq] using hmem
    · intro u qt hlookup
      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
      have hvlookup' : cf₀.varEnv.lookup u = some v := by
        simpa [hcf₀_eq] using hvlookup
      have hvtyp' : valueHasETyp θ₀2 v qt.etyp := valueHasETyp_extends hθext₀2.1 hvtyp
      exact ⟨v, hvlookup', hvtyp'⟩
  have hric₁'' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    unfold runtimeInstantiatesCtx
    rcases hric₁2 with ⟨hmem₂, _hvars₂⟩
    rcases hric₁1 with ⟨_hmem₁, hvars₁⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₂ l a hlookup
      simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcf₁_eq] using hmem
    · intro u qt hlookup
      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
      have hvlookup' : cf₁.varEnv.lookup u = some v := by
        simpa [hcf₁_eq] using hvlookup
      have hvtyp' : valueHasETyp θ₁2 v qt.etyp := valueHasETyp_extends hθext₁2.1 hvtyp
      exact ⟨v, hvlookup', hvtyp'⟩
  have hreg'' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) R := by
    simpa [regimeConsistentWithCtx, ctxAfter, h_tag, h_loc, h_ntag] using htagR2
  -- Final agreeOnClean
  have hagree_clean :
      agreeOnClean predSat R (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    constructor
    · intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag] using hlookup
      have hagree_loc := (hagree_clean2.1 l qt hlookup' hclean)
      simpa [hcf₀_eq, hcf₁_eq] using hagree_loc
    · intro w qt hlookup hclean
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup w = some qt := by
          simpa [ctxAfter] using hlookup
        have hagree_var := (hagree_clean1.2 w qt hlookup' hclean)
        cases hagree_var with
        | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
            have hlookup₀' : cf₀.varEnv.lookup w = some v₀ := by
              simpa [hcf₀_eq] using hlookup₀
            have hlookup₁' : cf₁.varEnv.lookup w = some v₁ := by
              simpa [hcf₁_eq] using hlookup₁
            have hagree' : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ :=
              agreeValueUnder_clean_extends hclean hθext₀2.1 hθext₁2.1 hagree
            exact agreeVarUnder.agree_values w qt v₀ v₁ hlookup₀' hlookup₁' hagree'
        | both_none _ _ hnone₀ hnone₁ =>
            have hnone₀' : cf₀.varEnv.lookup w = none := by simpa [hcf₀_eq] using hnone₀
            have hnone₁' : cf₁.varEnv.lookup w = none := by simpa [hcf₁_eq] using hnone₁
            exact agreeVarUnder.both_none w qt hnone₀' hnone₁'
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
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hlookup₀2
            have hlookup₁1 : cfg₁1.varEnv.lookup w = some v₁ := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hlookup₁2
            have hlookup₀' : cf₀.varEnv.lookup w = some v₀ := by
              simpa [hcf₀_eq] using hlookup₀1
            have hlookup₁' : cf₁.varEnv.lookup w = some v₁ := by
              simpa [hcf₁_eq] using hlookup₁1
            have hagree' : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ := by
              simpa [hcf₀_eq, hcf₁_eq] using hagree
            exact agreeVarUnder.agree_values w qt v₀ v₁ hlookup₀' hlookup₁' hagree'
        | both_none _ _ hnone₀ hnone₁ =>
            have hnone₀2 : cfg₀2.varEnv.lookup w = none := by
              simpa [hvar_pres₀] using hnone₀
            have hnone₁2 : cfg₁2.varEnv.lookup w = none := by
              simpa [hvar_pres₁] using hnone₁
            have hnone₀1 : cfg₀1.varEnv.lookup w = none := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hnone₀2
            have hnone₁1 : cfg₁1.varEnv.lookup w = none := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hnone₁2
            have hnone₀' : cf₀.varEnv.lookup w = none := by simpa [hcf₀_eq] using hnone₀1
            have hnone₁' : cf₁.varEnv.lookup w = none := by simpa [hcf₁_eq] using hnone₁1
            exact agreeVarUnder.both_none w qt hnone₀' hnone₁'
  -- Final wfConfig
  have hwfcf₀_final : wfConfig cf₀ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀_final, hwfcf₁_final, hric₀'', hric₁'', hreg'', hagree_clean, ?_⟩
  -- wfTypeContext
  · intro l hcontains
    simp only [ctxAfter, h_mem, h_loc] at hcontains ⊢
    exact hwf2 l hcontains
  -- resultAgreesIfClean
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
        calc joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by symm; exact h_ret_poison
             _ = false := by exact hpoison_res
      exact (joinPoison_eq_false hjoin).2
    have hclean2 : qtypCleanUnder R res2.qualType := by
      cases hclean with
      | clean hpoison_res => exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k htag hreg hnotfun =>
          have htag' : qtypGuardTag res2.qualType = some k := by
            simpa [qtypGuardTag, h_ret_pred] using htag
          have hnotfun' : res2.qualType.etyp.isFunctionType = false := by
            simpa [h_ret_etyp] using hnotfun
          exact qtypCleanUnder.guard k htag' hreg hnotfun'
    have hagree2 : agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      simpa [hcf₀_eq, hcf₁_eq] using (hres_agree2 hclean2)
    exact agreeValueUnder_transport_clean hclean h_ret_etyp h_ret_pred hpoison_imp hagree2

-- World-free version of stepFRW_fn
private lemma stepFR_fn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ R (Expr.fn x paramType body returnType) res predSat := by
  -- Extract typecheck result
  have htcFn : typecheckFn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  let res_expected : TypeResult := {
    qualType :=
      ⟨ETyp.arrow paramType returnType ctxᵢ.pc
          [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
        ctxᵢ.pc, Predicate.noPred⟩
    memEnv' := ctxᵢ.memEnv
    tagEnv' := ctxᵢ.tagEnv
    nextLoc' := ctxᵢ.nextLoc
    nextTag' := ctxᵢ.nextTag
  }
  have hres : res = res_expected := by
    have htc' := htcFn
    simp [typecheckFn] at htc'
    cases htc'
    rfl
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter, hres, res_expected]
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma
  have ⟨hcf₀, ho₀⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hcap :
      agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
    agreeCapturedEnv_of_agreeOnClean predSat R ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using hwf
  · -- runtimeInstantiatesCtx for θ₀' (fn doesn't change context or config)
    simpa [hctxAfter] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [hctxAfter] using hric₁
  · -- regimeConsistentWithCtx (fn doesn't change context)
    simpa [hctxAfter] using hreg
  · -- agreeOnClean for updated context (fn doesn't change context)
    simpa [hctxAfter] using hagree
  · -- resultAgreesIfClean
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp :
            res.qualType.etyp =
              ETyp.arrow paramType returnType ctxᵢ.pc
                [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        -- res.qualType.poison = ctxᵢ.pc (from res_expected)
        -- hpoison says qt.poison = false, and qt = res.qualType
        -- Therefore ctxᵢ.pc = false, so internal poison is clean
        have hpc_clean : ctxᵢ.pc = false := by
          have hqt_poison : res.qualType.poison = ctxᵢ.pc := by
            simp [hres, res_expected]
          calc
            ctxᵢ.pc = res.qualType.poison := by symm; exact hqt_poison
            _ = false := by exact hpoison
        have hclean_internal : internalPoisonClean res.qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        exact
          agreeValueUnder.clean_internal_arrow
            (tcl := FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv))
            (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
            hclean_internal hetyp (by simp) rfl hcap (by simp [ho₀]) (by simp [ho₁])
    | guard k htag _hregime _ =>
        have : False := by
          have hpred : qtypGuardTag res.qualType = none := by
            simp [qtypGuardTag, hres, res_expected]
          simp [hpred] at htag
        exact False.elim this
  /- OLD PROOF (preserved for reference):
  have htcFn : typecheckFn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  let res_expected : TypeResult := {
    qualType :=
      ⟨ETyp.arrow paramType returnType ctxᵢ.pc
          [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
        ctxᵢ.pc, Predicate.noPred⟩
    memEnv' := ctxᵢ.memEnv
    tagEnv' := ctxᵢ.tagEnv
    nextLoc' := ctxᵢ.nextLoc
    nextTag' := ctxᵢ.nextTag
  }
  have hres : res = res_expected := by
    have htc' := htcFn
    simp [typecheckFn] at htc'
    cases htc'
    rfl
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter, hres, res_expected]
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Extract config and value from terminatesTo
  rcases ht₀ with ⟨fuel₀, verbose₀, hbeval₀⟩
  rcases ht₁ with ⟨fuel₁, verbose₁, hbeval₁⟩
  -- fn doesn't change config or perform I/O
  have hcf₀ : cf₀ = { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } := by
    cases fuel₀ with
    | zero =>
        simp [LeanPoison.beval] at hbeval₀
        cases hbeval₀
    | succ fuel₀ =>
        simp [LeanPoison.beval, pure] at hbeval₀
        injection hbeval₀ with hcfg
        cases hcfg
        rfl
  have hcf₁ : cf₁ = { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } := by
    cases fuel₁ with
    | zero =>
        simp [LeanPoison.beval] at hbeval₁
        cases hbeval₁
    | succ fuel₁ =>
        simp [LeanPoison.beval, pure] at hbeval₁
        injection hbeval₁ with hcfg
        cases hcfg
        rfl
  have ho₀ : o₀ = Value.closure x body ρ₀ := by
    cases fuel₀ with
    | zero =>
        simp [LeanPoison.beval] at hbeval₀
        cases hbeval₀
    | succ fuel₀ =>
        simp [LeanPoison.beval, pure] at hbeval₀
        injection hbeval₀ with _hcfg hval
        cases hval
        rfl
  have ho₁ : o₁ = Value.closure x body ρ₁ := by
    cases fuel₁ with
    | zero =>
        simp [LeanPoison.beval] at hbeval₁
        cases hbeval₁
    | succ fuel₁ =>
        simp [LeanPoison.beval, pure] at hbeval₁
        injection hbeval₁ with _hcfg hval
        cases hval
        rfl
  subst hcf₀
  subst hcf₁
  have hcap :
      agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
    agreeCapturedEnv_of_agreeOnClean predSat R ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_⟩
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
  · simpa [hctxAfter] using hric₀
  · simpa [hctxAfter] using hric₁
  · simpa [hctxAfter] using hreg
  · simpa [hctxAfter] using hagree
  · intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp :
            res.qualType.etyp =
              ETyp.arrow paramType returnType ctxᵢ.pc
                [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        have hpred : qtypGuardTag res.qualType = none := by
          simp [qtypGuardTag, hres, res_expected]
        exact
          agreeValueUnder.clean_internal_arrow
            (tcl := FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv))
            (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
            hpoison hetyp (by simp) rfl hcap (by simp [ho₀]) (by simp [ho₁])
    | guard k htag _hregime _ =>
        have : False := by
          have hpred : qtypGuardTag res.qualType = none := by
            simp [qtypGuardTag, hres, res_expected]
          simp [hpred] at htag
            exact False.elim this
  -/

-- World-free version of stepFRW_pfn
private lemma stepFR_pfn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ R (Expr.pfn x paramType body returnType) res predSat := by
  -- Extract typecheck result
  have htcPfn : typecheckPfn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody] at htcPfn
  | ok pbody =>
      let res_expected : TypeResult := {
        qualType :=
          ⟨ETyp.parrow paramType returnType ctxᵢ.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
            ctxᵢ.pc, Predicate.noPred⟩
        memEnv' := ctxᵢ.memEnv
        tagEnv' := ctxᵢ.tagEnv
        nextLoc' := ctxᵢ.nextLoc
        nextTag' := ctxᵢ.nextTag
      }
      have hres : res = res_expected := by
        have htc' := htcPfn
        simp [typecheckPfn, hbody] at htc'
        cases htc'
        rfl
      have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
        simp [ctxAfter, hres, res_expected]
      intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
      -- Use world-free inversion lemma
      have ⟨hcf₀, ho₀⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
      have ⟨hcf₁, ho₁⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
      subst hcf₀ hcf₁
      have hcap :
          agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
        agreeCapturedEnv_of_agreeOnClean predSat R ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_⟩
      · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · -- wfTypeContext (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using hwf
      · -- runtimeInstantiatesCtx for θ₀' (pfn doesn't change context or config)
        simpa [hctxAfter] using hric₀
      · -- runtimeInstantiatesCtx for θ₁'
        simpa [hctxAfter] using hric₁
      · -- regimeConsistentWithCtx (pfn doesn't change context)
        simpa [hctxAfter] using hreg
      · -- agreeOnClean for updated context (pfn doesn't change context)
        simpa [hctxAfter] using hagree
      · -- resultAgreesIfClean
        intro hclean
        cases hclean with
        | clean hpoison =>
            have hetyp :
                res.qualType.etyp =
                  ETyp.parrow paramType returnType ctxᵢ.pc
                    [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
              simp [hres, res_expected]
            have htcl : PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) ∈
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
              simp
            have hmatch : Expr.toPExpr? body = some pbody ∧
                PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) =
                  PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) := by
              exact ⟨hto, rfl⟩
            -- Same reasoning as stepFR_fn: outer poison = ctxᵢ.pc = false, so internal clean
            have hpc_clean : ctxᵢ.pc = false := by
              have hqt_poison : res.qualType.poison = ctxᵢ.pc := by
                simp [hres, res_expected]
              calc
                ctxᵢ.pc = res.qualType.poison := by symm; exact hqt_poison
                _ = false := by exact hpoison
            have hclean_internal : internalPoisonClean res.qualType := by
              simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
            exact
              agreeValueUnder.clean_internal_parrow
                (pbody := pbody)
                (tcl := PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv))
                (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
                hclean_internal hetyp htcl hmatch hcap (by simp [ho₀]) (by simp [ho₁])
        | guard k htag _hregime _ =>
            have : False := by
              have hpred : qtypGuardTag res.qualType = none := by
                simp [qtypGuardTag, hres, res_expected]
              simp [hpred] at htag
            exact False.elim this
  /- OLD PROOF (preserved for reference):
  have htcPfn : typecheckPfn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody] at htcPfn
  | ok pbody =>
      let res_expected : TypeResult := {
        qualType :=
          ⟨ETyp.parrow paramType returnType ctxᵢ.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
            ctxᵢ.pc, Predicate.noPred⟩
        memEnv' := ctxᵢ.memEnv
        tagEnv' := ctxᵢ.tagEnv
        nextLoc' := ctxᵢ.nextLoc
        nextTag' := ctxᵢ.nextTag
      }
      have hres : res = res_expected := by
        have htc' := htcPfn
        simp [typecheckPfn, hbody] at htc'
        cases htc'
        rfl
      have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
        simp [ctxAfter, hres, res_expected]
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
      -- Extract config and value from terminatesTo
      rcases ht₀ with ⟨fuel₀, verbose₀, hbeval₀⟩
      rcases ht₁ with ⟨fuel₁, verbose₁, hbeval₁⟩
      -- pfn doesn't change config or perform I/O
      have hcf₀ : cf₀ = { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } := by
        cases fuel₀ with
        | zero =>
            simp [LeanPoison.beval] at hbeval₀
            cases hbeval₀
        | succ fuel₀ =>
            simp [LeanPoison.beval, pure] at hbeval₀
            injection hbeval₀ with hcfg
            cases hcfg
            rfl
      have hcf₁ : cf₁ = { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } := by
        cases fuel₁ with
        | zero =>
            simp [LeanPoison.beval] at hbeval₁
            cases hbeval₁
        | succ fuel₁ =>
            simp [LeanPoison.beval, pure] at hbeval₁
            injection hbeval₁ with hcfg
            cases hcfg
            rfl
      have ho₀ : o₀ = Value.pclosure x pbody ρ₀ := by
        cases fuel₀ with
        | zero =>
            simp [LeanPoison.beval] at hbeval₀
            cases hbeval₀
        | succ fuel₀ =>
            simp [LeanPoison.beval, pure] at hbeval₀
            injection hbeval₀ with _hcfg hval
            cases hval
            rfl
      have ho₁ : o₁ = Value.pclosure x pbody ρ₁ := by
        cases fuel₁ with
        | zero =>
            simp [LeanPoison.beval] at hbeval₁
            cases hbeval₁
        | succ fuel₁ =>
            simp [LeanPoison.beval, pure] at hbeval₁
            injection hbeval₁ with _hcfg hval
            cases hval
            rfl
      subst hcf₀
      subst hcf₁
      have hcap :
          agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
        agreeCapturedEnv_of_agreeOnClean predSat R ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
      refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_⟩
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
      · simpa [hctxAfter] using hric₀
      · simpa [hctxAfter] using hric₁
      · simpa [hctxAfter] using hreg
      · simpa [hctxAfter] using hagree
      · intro hclean
        cases hclean with
        | clean hpoison =>
            have hetyp :
                res.qualType.etyp =
                  ETyp.parrow paramType returnType ctxᵢ.pc
                    [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
              simp [hres, res_expected]
            exact
              agreeValueUnder.clean_internal_parrow
                (tcl := PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv))
                (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
                hpoison hetyp (by simp) rfl hto hcap (by simp [ho₀]) (by simp [ho₁])
        | guard k htag _hregime _ =>
            have : False := by
              have hpred : qtypGuardTag res.qualType = none := by
                simp [qtypGuardTag, hres, res_expected]
              simp [hpred] at htag
            exact False.elim this
  -/

-- World-free version of ite fault-robustness
-- Key insight: if condition is clean, both runs take same branch
private lemma stepFR_ite
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.ite e1 e2 e3) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckIf ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_ite_succ] at htc
    exact htc
  -- Get structure from typecheckIf
  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htc'
  -- Introduce quantified variables
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for ite
  have hinv₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hinv₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀2⟩
  have hinv₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hinv₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁2⟩
  -- Both modes share the property that e1 typechecks to bool and e2, e3 typecheck
  -- We handle both modes uniformly by extracting the key properties
  cases hstruct with
  | inl hmode1 =>
    -- Mode 1: Predicate-based (matchGuard succeeds)
    -- In this mode, e2/e3 use original memEnv with modified tagEnv
    -- This is complex because the IH contexts differ from ctxAfter
    -- For now, we admit this case - it requires careful handling of
    -- the different context structures
    sorry
  | inr hmode2 =>
    -- Mode 2: Standard (matchGuard fails)
    -- This is similar to seq/vlet - contexts chain through
    rcases hmode2 with ⟨⟨err, hmatch_fail⟩, res1, htc1, hbool1, res2, htc2, res3, htc3,
                        h_memEnv, h_tagEnv, h_nextLoc, h_nextTag, h_poison⟩
    -- Convert typecheck results to full typecheck form
    have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
      simpa [typecheck, Nat.succ_sub_one] using htc1
    -- Define intermediate contexts
    let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                            nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
    let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
    let ctx'' := { ctx' with pc := pc' }
    have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by
      simpa [ctx'', ctx', typecheck, Nat.succ_sub_one] using htc2
    let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
    have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by
      simpa [ctxForE3, ctx'', ctx', typecheck, Nat.succ_sub_one] using htc3
    -- Get IH for e1
    have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
      e1 ctxᵢ res1 htc1' R
    -- Apply IH for e1
    have hstep_e1 :=
      hIH1 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
        hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
    rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1,
                          hric₀1, hric₁1, htagR1, hagree_clean1, hres_agree1⟩
    -- Prepare for branch IH
    have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
    have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
    -- ctx'' has elevated pc, need to establish properties
    have hwf1' : wfTypeContext ctx'' := by
      simp only [ctx'', ctx']
      unfold wfTypeContext at hwf1 ⊢
      simpa [ctxAfter] using hwf1
    have hric₀1' : runtimeInstantiatesCtx ctx'' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
      simpa [ctx'', ctx', ctxAfter] using hric₀1
    have hric₁1' : runtimeInstantiatesCtx ctx'' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      simpa [ctx'', ctx', ctxAfter] using hric₁1
    have htagR1' : regimeConsistentWithCtx ctx'' R := by
      simpa [ctx'', ctx', ctxAfter] using htagR1
    -- agreeOnClean for ctx'' (pc is elevated but other fields preserved)
    have hagree_clean1' : agreeOnClean predSat R ctx'' cfg₀1.memory cfg₀1.varEnv θ₀1
                                                      cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      -- agreeOnClean depends on memEnv, varEnv, tagEnv - not pc
      -- ctx'' has same memEnv, varEnv, tagEnv as ctxAfter ctxᵢ res1
      simpa [ctx'', ctx', ctxAfter] using hagree_clean1
    -- Handle pureMode equality for branch IH
    have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
    have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv,
                               nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
      cases cfg₁1; simp only [Config.mk.injEq, true_and]; exact hpm_eq
    have hwfcf₁1' : wfConfig { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv,
                               nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
      rw [← hcfg₁1_eq]; exact hwfcf₁1
    -- The key insight: if result is clean, condition must be clean, so b₀ = b₁
    -- First, let's establish that both runs take the same branch when result is clean
    -- We'll case split on the branch and apply appropriate IH
    cases hbranch₀ with
    | inl htrue₀ =>
      rcases htrue₀ with ⟨hb₀, ht₀_e2⟩
      cases hbranch₁ with
      | inl htrue₁ =>
        -- Both runs take true branch
        rcases htrue₁ with ⟨hb₁, ht₁_e2⟩
        -- Get IH for e2
        have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          e2 ctx'' res2 htc2' R
        have ht₁_e2' : terminatesTo .ioFree e2
            { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv,
              nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
            cf₁ o₁ := by rw [← hcfg₁1_eq]; exact ht₁_e2
        -- Apply IH for e2
        have hstep_e2 :=
          hIH2 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
            cf₀ cf₁ o₀ o₁
            hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound hagree_clean1'
            cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
            ht₀_e2 ht₁_e2'
        rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2,
                              hric₀2, hric₁2, htagR2, hagree_clean2, hres_agree2⟩
        have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
        have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
        -- For ite in standard mode, the final result is constructed from branch results
        -- res.memEnv' = joinMemEnvs res2.memEnv' res3.memEnv'
        -- res.tagEnv' = res1.tagEnv' (the tagEnv from e1's result)
        -- But both runs took the true branch (e2), so we use res2's properties
        -- The key insight: since only one branch executed at runtime, the actual
        -- memory environment is res2.memEnv' (from e2), not the joined one
        -- This creates a gap between typing context and runtime
        -- Need lemmas about join being conservative: properties of res2.memEnv' ⊆ joinMemEnvs
        -- For now, we refine the result using sorry for the complex join-related proofs
        refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?hwf_final, hwfcf₀2, hwfcf₁2, ?hric₀_final,
                ?hric₁_final, ?htagR_final, ?hagree_final, ?hres_final⟩
        -- wfTypeContext (ctxAfter ctxᵢ res)
        case hwf_final =>
          unfold wfTypeContext ctxAfter
          simp only [h_memEnv, h_nextLoc]
          -- Need: ∀ l ∈ joinMemEnvs res2.memEnv' res3.memEnv', l < max res2.nextLoc' res3.nextLoc'
          -- From hwf2: ∀ l ∈ res2.memEnv', l < res2.nextLoc'
          -- Need wfTypeResult res3: ∀ l ∈ res3.memEnv', l < res3.nextLoc'
          -- Get wfTypeContext ctxForE3 first
          have hwfForE3 : wfTypeContext ctxForE3 := by
            intro l hcontains
            simp only [ctxForE3] at hcontains ⊢
            -- l ∈ ctx''.memEnv = res1.memEnv'
            -- From hwf1': ∀ l ∈ res1.memEnv', l < res1.nextLoc'
            have hlt1 : l < res1.nextLoc' := by
              have hwf1'_unfolded : ∀ l', ctx''.memEnv.contains l' → l' < ctx''.nextLoc := hwf1'
              simp only [ctx'', ctx'] at hwf1'_unfolded
              exact hwf1'_unfolded l hcontains
            -- From typecheck_nextLoc_mono: res1.nextLoc' ≤ res2.nextLoc'
            have h_mono : ctx''.nextLoc ≤ res2.nextLoc' := typecheck_nextLoc_mono ctx'' e2 fuel' res2 htc2'
            simp only [ctx'', ctx'] at h_mono
            exact Nat.lt_of_lt_of_le hlt1 h_mono
          -- Now use typecheck_wfTypeResult to get wfTypeResult res3
          have hwfres3 : wfTypeResult res3 := typecheck_wfTypeResult ctxForE3 e3 fuel' res3 hwfForE3 htc3'
          -- hwf2 gives wfTypeResult res2 via ctxAfter
          have hwfres2 : ∀ l, res2.memEnv'.contains l → l < res2.nextLoc' := by
            simp only [wfTypeContext, ctxAfter, ctx'', ctx'] at hwf2
            exact hwf2
          -- Apply our join lemma
          exact wfTypeContext_joinMemEnvs_max res2.memEnv' res3.memEnv' res2.nextLoc' res3.nextLoc'
            hwfres2 hwfres3
        -- runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2
        -- The runtime actually executed e2, but the type context expects joined memEnv.
        -- Key: θ₀2 only maps locations that are in res2.memEnv', and those are also in joinMemEnvs
        case hric₀_final =>
          unfold runtimeInstantiatesCtx ctxAfter
          simp only [h_memEnv]
          have hric₀2_parts := hric₀2
          unfold runtimeInstantiatesCtx ctxAfter at hric₀2_parts
          simp only [ctx'', ctx'] at hric₀2_parts
          constructor
          · -- For all (l, a) in θ₀2: joinMemEnvs contains l ∧ μ contains a
            intro l a hlookup
            have ⟨hcontains2, hmem_contains⟩ := hric₀2_parts.1 l a hlookup
            constructor
            · exact joinMemEnvs_contains_left res2.memEnv' res3.memEnv' l hcontains2
            · exact hmem_contains
          · -- varEnv part: unchanged since ctxᵢ.varEnv = ctx''.varEnv
            intro x qt hvar_lookup
            exact hric₀2_parts.2 hvar_lookup
        case hric₁_final =>
          -- Same argument as hric₀_final
          unfold runtimeInstantiatesCtx ctxAfter
          simp only [h_memEnv]
          have hric₁2_parts := hric₁2
          unfold runtimeInstantiatesCtx ctxAfter at hric₁2_parts
          simp only [ctx'', ctx'] at hric₁2_parts
          constructor
          · intro l a hlookup
            have ⟨hcontains2, hmem_contains⟩ := hric₁2_parts.1 l a hlookup
            constructor
            · exact joinMemEnvs_contains_left res2.memEnv' res3.memEnv' l hcontains2
            · exact hmem_contains
          · intro x qt hvar_lookup
            exact hric₁2_parts.2 hvar_lookup
        -- regimeConsistentWithCtx (ctxAfter ctxᵢ res) R
        -- This depends on tagEnv = res1.tagEnv' and nextTag = max res2.nextTag' res3.nextTag'
        case htagR_final =>
          -- ctxAfter ctxᵢ res has tagEnv = res.tagEnv' = res1.tagEnv' (from h_tagEnv in standard mode)
          -- and nextTag = res.nextTag' = max res2.nextTag' res3.nextTag' (from h_nextTag)
          unfold regimeConsistentWithCtx ctxAfter
          simp only [h_tagEnv, h_nextTag]
          -- From htagR1, we have tagEnvConsistentWithRegime on ctxAfter ctxᵢ res1
          -- which has tagEnv = res1.tagEnv'
          have htagR1_vals : tagEnvConsistentWithRegime res1.tagEnv' R ∧ R.bound ≤ res1.nextTag' := by
            simp only [regimeConsistentWithCtx, ctxAfter] at htagR1
            exact htagR1
          constructor
          · exact htagR1_vals.1
          · -- R.bound ≤ res2.nextTag' ≤ max res2.nextTag' res3.nextTag'
            have hbound2 : R.bound ≤ res2.nextTag' := by
              simp only [regimeConsistentWithCtx, ctxAfter] at htagR2
              exact htagR2.2
            exact Nat.le_trans hbound2 (Nat.le_max_left res2.nextTag' res3.nextTag')
        -- agreeOnClean predSat R (ctxAfter ctxᵢ res) ...
        case hagree_final =>
          -- We need to show agreement for clean locations in joined memEnv
          -- From hagree_clean2, we have agreement for clean locations in res2.memEnv'
          -- The joined memEnv = joinMemEnvs res2.memEnv' res3.memEnv'
          -- Key insight: θ₀2, θ₁2 only contain locations from res2 (we executed e2, not e3)
          -- So locations only in res3 are both_unrealized
          unfold agreeOnClean ctxAfter
          simp only [h_memEnv]
          have hagree2_parts := hagree_clean2
          unfold agreeOnClean ctxAfter at hagree2_parts
          simp only [ctx'', ctx'] at hagree2_parts
          constructor
          · -- Locations in joined memEnv
            intro l qt hlookup hclean
            -- Check if l is in res2.memEnv'
            by_cases hres2 : res2.memEnv'.contains l
            · -- l is in res2.memEnv'
              -- Key insight: if the joined type qt is clean (poison=false), then
              -- res2's type at l must also be clean since joinPoison p1 p2 = false → p1 = false.
              -- We need to get the actual type from res2.memEnv' and apply hagree2_parts.1.
              cases hclean with
              | clean hpoison =>
                  -- qt.poison = false, so by joinMemEnvs_lookup_clean_left, res2's type has poison=false
                  have hres2_lookup_ne : res2.memEnv'.lookup l ≠ none := by
                    simp only [MemoryTypeEnv.lookup]
                    have hmem : l ∈ res2.memEnv' := (Std.ExtTreeMap.contains_iff_mem).1 hres2
                    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_eq_some_getElem hmem]
                    exact Option.some_ne_none _
                  have ⟨qt1, hlookup1, hetyp1, hpoison1⟩ :=
                    joinMemEnvs_lookup_clean_left res2.memEnv' res3.memEnv' l qt hlookup hpoison hres2_lookup_ne
                  -- qt1 is clean via poison = false
                  have hclean1 : qtypCleanUnder R qt1 := qtypCleanUnder.clean hpoison1
                  -- Apply hagree2_parts.1 to get agreement for (l, qt1)
                  have hagree_qt1 := hagree2_parts.1 l qt1 hlookup1 hclean1
                  -- Transport from qt1 to qt
                  cases hagree_qt1 with
                  | agree_values _ _ a₁ a₂ n₁ n₂ hreal1 hreal2 hmem1 hmem2 hagree_val =>
                      apply agreeLocUnder.agree_values l qt a₁ a₂ n₁ n₂ hreal1 hreal2 hmem1 hmem2
                      cases hagree_val with
                      | clean_eq_nonref _ hnotfun1 hnotref1 hEq =>
                          have hnotfun : qt.etyp.isFunctionType = false := by rw [← hetyp1]; exact hnotfun1
                          have hnotref : ¬ (∃ t ls, qt.etyp = ETyp.ref t ls) := by
                            intro ⟨t, ls, heq⟩; apply hnotref1; exact ⟨t, ls, hetyp1 ▸ heq⟩
                          exact agreeValueUnder.clean_eq_nonref hpoison hnotfun hnotref hEq
                      | poisoned_noPred_eq_nonref hp _ _ _ _ =>
                          -- Contradiction: qt1 has poison = false but this case requires poison = true
                          simp [hpoison1] at hp
                      | _ =>
                          -- Function/ref types - need more detailed handling
                          sorry
                  | both_unrealized _ _ hreal1 hreal2 =>
                      exact agreeLocUnder.both_unrealized l qt hreal1 hreal2
              | guard k htag hregime hnotfun =>
                  -- Guarded cleanness: requires predicate analysis through joinMemEnvs
                  sorry
            · -- l is only in res3.memEnv' (not in res2)
              -- θ₀2 and θ₁2 don't have l realized (they come from executing e2)
              -- Use both_unrealized
              -- (ctxAfter ctx'' res2).memEnv = res2.memEnv'
              have hctx_memEnv : (ctxAfter ctx'' res2).memEnv = res2.memEnv' := by
                simp only [ctxAfter]
              have hnotContains_ctx : ¬ (ctxAfter ctx'' res2).memEnv.contains l := by
                rw [hctx_memEnv]; exact hres2
              -- θ₀2.lookup l = none
              have hθ₀2_none : θ₀2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv (ctxAfter ctx'' res2)
                  cf₀.memory cf₀.varEnv θ₀2 l hric₀2 hnotContains_ctx
              -- θ₁2.lookup l = none
              have hθ₁2_none : θ₁2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv (ctxAfter ctx'' res2)
                  cf₁.memory cf₁.varEnv θ₁2 l hric₁2 hnotContains_ctx
              exact agreeLocUnder.both_unrealized l qt hθ₀2_none hθ₁2_none
          · -- Variables: unchanged since varEnv is the same
            intro x qt hvar_lookup hclean
            exact hagree2_parts.2 (x := x) (qt := qt) hvar_lookup hclean
        -- resultAgreesIfClean predSat R cf₀.memory cf₁.memory θ₀2 θ₁2 res.qualType o₀ o₁
        -- res2 and res have same qualType in many cases, but poison is joined
        case hres_final =>
          -- Show that if res.qualType is clean, then res2.qualType is also clean
          -- From h_poison: res.qualType.poison = joinPoison ctx.pc (joinPoison res1.poison (joinPoison res2.poison res3.poison))
          unfold resultAgreesIfClean
          intro hclean_res
          -- Since res.qualType.pred = Predicate.noPred (from typecheckIf standard mode),
          -- cleanness must be via poison = false
          have hres_noPred : res.qualType.pred = Predicate.noPred :=
            typecheckIf_standard_pred_noPred ctxᵢ e1 e2 e3 fuel'.succ res htc' ⟨err, hmatch_fail⟩
          have hres_poison : res.qualType.poison = false := by
            cases hclean_res with
            | clean hp => exact hp
            | guard k htag _ _ =>
                simp [qtypGuardTag, hres_noPred] at htag
          -- Extract res2.qualType.poison = false from h_poison
          have hres2_poison : res2.qualType.poison = false := by
            have hjoin : joinPoison ctxᵢ.pc
              (joinPoison res1.qualType.poison (joinPoison res2.qualType.poison res3.qualType.poison)) = false := by
              rw [← h_poison]; exact hres_poison
            have ⟨_, h2⟩ := joinPoison_eq_false hjoin
            have ⟨_, h4⟩ := joinPoison_eq_false h2
            have ⟨h5, _⟩ := joinPoison_eq_false h4
            exact h5
          -- Show res2.qualType is clean
          have hclean2 : qtypCleanUnder R res2.qualType := by
            exact qtypCleanUnder.clean hres2_poison
          -- Apply hres_agree2 to get agreement on res2.qualType
          have hagree2 := hres_agree2 hclean2
          -- Transport from res2.qualType to res.qualType
          -- Both have poison = false (hres_poison, hres2_poison)
          -- res.qualType.etyp = joinETyps res2.etyp res3.etyp p'' p'''
          -- For non-function, non-ref types: joinETyps t1 t2 _ _ = t1
          -- Get the etyp relationship using the specific lemma with our res2, res3
          have hetyp_join' : res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                              res2.qualType.poison res3.qualType.poison := by
            apply typecheckIf_standard_etyp' ctxᵢ e1 e2 e3 fuel'.succ res res1 res2 res3
              htc' ⟨err, hmatch_fail⟩
            · simp only [Nat.succ_sub_one]; exact htc1
            · exact hbool1
            · simp only [Nat.succ_sub_one] at htc2 ⊢; exact htc2
            · simp only [Nat.succ_sub_one] at htc3 ⊢; exact htc3
          -- Case analyze on hagree2 to reconstruct agreement
          cases hagree2 with
          | clean_eq_nonref _hpoison2 hnotfun2 hnotref2 hEq =>
              -- o₀ = o₁, and res.qualType is clean with same etyp category
              -- joinETyps on non-arrow, non-ref returns t1, so res.etyp preserves non-fun/non-ref
              have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
                rw [hetyp_join']
                exact joinETyps_isFunctionType_false_of_left hnotfun2 hnotref2
              have hnotref_res : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                rw [hetyp_join']
                exact joinETyps_notRef_of_left_simple hnotfun2 hnotref2
              exact agreeValueUnder.clean_eq_nonref hres_poison hnotfun_res hnotref_res hEq
          | poisoned_noPred_eq_nonref hpoison2 _ _ _ _ =>
              -- Contradiction: res2.qualType.poison = false but hpoison2 says true
              simp [hres2_poison] at hpoison2
          | withPred_true_eq _ _ _ hnotfun2 hnotref2 hEq =>
              have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
                rw [hetyp_join']
                exact joinETyps_isFunctionType_false_of_left hnotfun2 hnotref2
              have hnotref_res : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                rw [hetyp_join']
                exact joinETyps_notRef_of_left_simple hnotfun2 hnotref2
              exact agreeValueUnder.clean_eq_nonref hres_poison hnotfun_res hnotref_res hEq
          | @clean_internal_arrow st1 st2 p tcls _ tcl x body σcap ρcap₁ ρcap₂ _ _ hclean2 hetyp2 htcl2 hmatch hcap hv₁ hv₂ =>
              -- For arrow types, joinETyps preserves or merges closures
              -- If signatures incompatible, left type returned unchanged
              -- If compatible, closures merged and tcl ∈ left implies tcl ∈ merged
              -- From hclean2, we know p = false (internal poison of res2 is clean)
              have hp : p = false := by
                simp only [internalPoisonClean, getInternalPoison, hetyp2] at hclean2
                exact hclean2
              have hetyp_preserved : ∃ p' tcls',
                  res.qualType.etyp = ETyp.arrow st1 st2 p' tcls' ∧ tcl ∈ tcls' ∧ p' = false := by
                rw [hetyp_join', hetyp2]
                cases hres3 : res3.qualType.etyp with
                | arrow st1' st2' p3 tcls3 =>
                  simp only [joinETyps]
                  by_cases hcompat : st1 == st1' && st2 == st2'
                  · simp only [hcompat, ↓reduceIte, hp]
                    -- p' = joinPoison false p3 = p3, but we need p3 = false for internal clean
                    -- This may not be provable without knowing res3's internal poison is clean
                    sorry
                  · simp only [hcompat, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨p, tcls, rfl, htcl2, hp⟩
                | _ => simp only [joinETyps]; exact ⟨p, tcls, rfl, htcl2, hp⟩
              obtain ⟨p', tcls', hetyp_res, htcl_res, hp'⟩ := hetyp_preserved
              have hclean_res : internalPoisonClean res.qualType := by
                simp only [internalPoisonClean, getInternalPoison, hetyp_res, hp']
              exact agreeValueUnder.clean_internal_arrow hclean_res hetyp_res htcl_res hmatch hcap hv₁ hv₂
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- Dirty arrow: need to show res.qualType.etyp is arrow and transport typing proofs
              -- First show res.qualType.etyp is an arrow type
              have hisArrow_res : res.qualType.etyp.isArrow = true := by
                rw [hetyp_join']
                -- Extract arrow structure from res2.qualType.etyp
                cases hres2etyp : res2.qualType.etyp with
                | arrow st1 st2 p tcls =>
                    cases hres3etyp : res3.qualType.etyp with
                    | arrow st1' st2' p3 tcls3 =>
                        simp only [joinETyps]
                        split <;> simp [ETyp.isArrow]
                    | _ => simp only [joinETyps, ETyp.isArrow]
                | int =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | bool =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | unit =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | string =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | ref _ _ =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | parrow _ _ _ _ =>
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
              -- Case split on whether res.qualType's internal poison is clean
              by_cases hclean_internal_res : internalPoisonClean res.qualType
              · -- res.qualType has clean internal poison - derive contradiction
                -- This is impossible: res2 has dirty internal poison (hdirty),
                -- and joinETyps preserves dirty internal poison for arrow types
                exfalso
                -- Extract arrow structure from res2.qualType.etyp
                cases hres2etyp : res2.qualType.etyp with
                | arrow st1_2 st2_2 p2 tcls2 =>
                    -- From hdirty, p2 = true
                    have hp2_dirty : p2 = true := by
                      simp only [internalPoisonClean, getInternalPoison, hres2etyp] at hdirty
                      cases p2; simp at hdirty; rfl
                    -- Use joinETyps_preserves_dirty_arrow to show res has dirty internal poison
                    have hres_dirty : getInternalPoison res.qualType.etyp = some true := by
                      rw [hetyp_join', hres2etyp]
                      exact joinETyps_preserves_dirty_arrow hp2_dirty
                    -- This contradicts hclean_internal_res
                    simp only [internalPoisonClean, hres_dirty] at hclean_internal_res
                    -- hclean_internal_res now has type (true = false), which is a contradiction
                    cases hclean_internal_res
                | _ =>
                    -- res2.qualType.etyp is not an arrow, contradicts hisArrow
                    rw [hres2etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
              · -- res.qualType has dirty internal poison - use dirty_internal_arrow
                -- Need to transport typing proofs from res2.qualType.etyp to res.qualType.etyp
                -- Extract arrow structure from res2.qualType.etyp
                have htyp1_res : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
                  -- Extract arrow structure from res2.qualType.etyp
                  cases hres2etyp : res2.qualType.etyp with
                  | arrow st1_2 st2_2 p2 tcls2 =>
                      -- Rewrite htyp1 to match the arrow structure
                      have htyp1' : valueHasETyp θ₀2 o₀ (ETyp.arrow st1_2 st2_2 p2 tcls2) := by
                        rw [← hres2etyp]; exact htyp1
                      cases htyp1' with
                      | closure x e env _ _ _ _ =>
                          rw [hetyp_join', hres2etyp]
                          cases hres3etyp : res3.qualType.etyp with
                          | arrow st1' st2' p3 tcls3 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.closure x e env _ _ _ _
                          | _ => simp only [joinETyps]; exact valueHasETyp.closure x e env _ _ _ _
                  | _ =>
                      rw [hres2etyp] at hisArrow
                      simp [ETyp.isArrow] at hisArrow
                have htyp2_res : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
                  cases hres2etyp : res2.qualType.etyp with
                  | arrow st1_2 st2_2 p2 tcls2 =>
                      have htyp2' : valueHasETyp θ₁2 o₁ (ETyp.arrow st1_2 st2_2 p2 tcls2) := by
                        rw [← hres2etyp]; exact htyp2
                      cases htyp2' with
                      | closure x e env _ _ _ _ =>
                          rw [hetyp_join', hres2etyp]
                          cases hres3etyp : res3.qualType.etyp with
                          | arrow st1' st2' p3 tcls3 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.closure x e env _ _ _ _
                          | _ => simp only [joinETyps]; exact valueHasETyp.closure x e env _ _ _ _
                  | _ =>
                      rw [hres2etyp] at hisArrow
                      simp [ETyp.isArrow] at hisArrow
                exact agreeValueUnder.dirty_internal_arrow hclean_internal_res hisArrow_res htyp1_res htyp2_res
          | @clean_internal_parrow st1 st2 p tcls _ tcl x body pbody σcap ρcap₁ ρcap₂ _ _ hclean2 hetyp2 htcl2 hmatch hcap hv₁ hv₂ =>
              -- Similar to clean_internal_arrow but for parrow types
              -- From hclean2, we know p = false (internal poison of res2 is clean)
              have hp : p = false := by
                simp only [internalPoisonClean, getInternalPoison, hetyp2] at hclean2
                exact hclean2
              have hetyp_preserved : ∃ p' tcls',
                  res.qualType.etyp = ETyp.parrow st1 st2 p' tcls' ∧ tcl ∈ tcls' ∧ p' = false := by
                rw [hetyp_join', hetyp2]
                cases hres3 : res3.qualType.etyp with
                | parrow st1' st2' p3 tcls3 =>
                  simp only [joinETyps]
                  by_cases hcompat : st1 == st1' && st2 == st2'
                  · simp only [hcompat, ↓reduceIte, hp]
                    -- p' = joinPoison false p3 = p3, but we need p3 = false for internal clean
                    -- This may not be provable without knowing res3's internal poison is clean
                    sorry
                  · simp only [hcompat, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨p, tcls, rfl, htcl2, hp⟩
                | _ => simp only [joinETyps]; exact ⟨p, tcls, rfl, htcl2, hp⟩
              obtain ⟨p', tcls', hetyp_res, htcl_res, hp'⟩ := hetyp_preserved
              have hclean_res : internalPoisonClean res.qualType := by
                simp only [internalPoisonClean, getInternalPoison, hetyp_res, hp']
              exact agreeValueUnder.clean_internal_parrow hclean_res hetyp_res htcl_res hmatch hcap hv₁ hv₂
          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
              -- Dirty parrow: need to show res.qualType.etyp is parrow and transport typing proofs
              have hisParrow_res : res.qualType.etyp.isParrow = true := by
                rw [hetyp_join']
                cases hres2etyp : res2.qualType.etyp with
                | parrow st1 st2 p tcls =>
                    cases hres3etyp : res3.qualType.etyp with
                    | parrow st1' st2' p3 tcls3 =>
                        simp only [joinETyps]
                        split <;> simp [ETyp.isParrow]
                    | _ => simp only [joinETyps, ETyp.isParrow]
                | int =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | bool =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | unit =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | string =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | ref _ _ =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | arrow _ _ _ _ =>
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
              by_cases hclean_internal_res : internalPoisonClean res.qualType
              · -- res.qualType has clean internal poison - derive contradiction
                -- This is impossible: res2 has dirty internal poison (hdirty),
                -- and joinETyps preserves dirty internal poison for parrow types
                exfalso
                -- Extract parrow structure from res2.qualType.etyp
                cases hres2etyp : res2.qualType.etyp with
                | parrow st1_2 st2_2 p2 tcls2 =>
                    -- From hdirty, p2 = true
                    have hp2_dirty : p2 = true := by
                      simp only [internalPoisonClean, getInternalPoison, hres2etyp] at hdirty
                      cases p2; simp at hdirty; rfl
                    -- Use joinETyps_preserves_dirty_parrow to show res has dirty internal poison
                    have hres_dirty : getInternalPoison res.qualType.etyp = some true := by
                      rw [hetyp_join', hres2etyp]
                      exact joinETyps_preserves_dirty_parrow hp2_dirty
                    -- This contradicts hclean_internal_res
                    simp only [internalPoisonClean, hres_dirty] at hclean_internal_res
                    -- hclean_internal_res now has type (true = false), which is a contradiction
                    cases hclean_internal_res
                | _ =>
                    -- res2.qualType.etyp is not a parrow, contradicts hisParrow
                    rw [hres2etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
              · -- res.qualType has dirty internal poison - use dirty_internal_parrow
                have htyp1_res : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
                  cases hres2etyp : res2.qualType.etyp with
                  | parrow st1_2 st2_2 p2 tcls2 =>
                      have htyp1' : valueHasETyp θ₀2 o₀ (ETyp.parrow st1_2 st2_2 p2 tcls2) := by
                        rw [← hres2etyp]; exact htyp1
                      cases htyp1' with
                      | peClosure x pe env _ _ _ _ =>
                          rw [hetyp_join', hres2etyp]
                          cases hres3etyp : res3.qualType.etyp with
                          | parrow st1' st2' p3 tcls3 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.peClosure x pe env _ _ _ _
                          | _ => simp only [joinETyps]; exact valueHasETyp.peClosure x pe env _ _ _ _
                  | _ =>
                      rw [hres2etyp] at hisParrow
                      simp [ETyp.isParrow] at hisParrow
                have htyp2_res : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
                  cases hres2etyp : res2.qualType.etyp with
                  | parrow st1_2 st2_2 p2 tcls2 =>
                      have htyp2' : valueHasETyp θ₁2 o₁ (ETyp.parrow st1_2 st2_2 p2 tcls2) := by
                        rw [← hres2etyp]; exact htyp2
                      cases htyp2' with
                      | peClosure x pe env _ _ _ _ =>
                          rw [hetyp_join', hres2etyp]
                          cases hres3etyp : res3.qualType.etyp with
                          | parrow st1' st2' p3 tcls3 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.peClosure x pe env _ _ _ _
                          | _ => simp only [joinETyps]; exact valueHasETyp.peClosure x pe env _ _ _ _
                  | _ =>
                      rw [hres2etyp] at hisParrow
                      simp [ETyp.isParrow] at hisParrow
                exact agreeValueUnder.dirty_internal_parrow hclean_internal_res hisParrow_res htyp1_res htyp2_res
          | @clean_ref t ls l₁ l₂ a₁ a₂ _ _ _ _ hetyp2 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
              -- For ref types, joinETyps unions location sets
              -- l₁ ∈ ls2 implies l₁ ∈ joined_ls
              have hetyp_preserved : ∃ ls',
                  res.qualType.etyp = ETyp.ref t ls' ∧ l₁ ∈ ls' ∧ l₂ ∈ ls' := by
                rw [hetyp_join', hetyp2]
                cases hres3 : res3.qualType.etyp with
                | ref t3 ls3 =>
                  simp only [joinETyps]
                  by_cases hcompat : beqETypSignature t t3
                  · simp only [hcompat, ↓reduceIte]
                    exact ⟨LocSet.union ls ls3, rfl,
                           Std.ExtTreeSet.mem_union_iff.mpr (Or.inl hin1),
                           Std.ExtTreeSet.mem_union_iff.mpr (Or.inl hin2)⟩
                  · simp only [hcompat, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨ls, rfl, hin1, hin2⟩
                | _ => simp only [joinETyps]; exact ⟨ls, rfl, hin1, hin2⟩
              obtain ⟨ls', hetyp_res, hin1', hin2'⟩ := hetyp_preserved
              exact agreeValueUnder.clean_ref hres_poison hetyp_res hlookup1 hin1' hv1 hlookup2 hin2' hv2
          | poisoned_noPred_ref hpoison2 _ _ _ _ _ _ _ =>
              simp [hres2_poison] at hpoison2
          | @withPred_true_ref k t ls l₁ l₂ a₁ a₂ _ _ _ htag2 hregime hetyp2 hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
              -- res.qualType has pred = noPred, so use clean_ref (not withPred_true_ref)
              have hetyp_preserved : ∃ ls',
                  res.qualType.etyp = ETyp.ref t ls' ∧ l₁ ∈ ls' ∧ l₂ ∈ ls' := by
                rw [hetyp_join', hetyp2]
                cases hres3 : res3.qualType.etyp with
                | ref t3 ls3 =>
                  simp only [joinETyps]
                  by_cases hcompat : beqETypSignature t t3
                  · simp only [hcompat, ↓reduceIte]
                    exact ⟨LocSet.union ls ls3, rfl,
                           Std.ExtTreeSet.mem_union_iff.mpr (Or.inl hin1),
                           Std.ExtTreeSet.mem_union_iff.mpr (Or.inl hin2)⟩
                  · simp only [hcompat, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨ls, rfl, hin1, hin2⟩
                | _ => simp only [joinETyps]; exact ⟨ls, rfl, hin1, hin2⟩
              obtain ⟨ls', hetyp_res, hin1', hin2'⟩ := hetyp_preserved
              exact agreeValueUnder.clean_ref hres_poison hetyp_res hlookup1 hin1' hv1 hlookup2 hin2' hv2
          | withPred_false_poisoned_fail _ _ _ _ hpoison2 _ _ =>
              simp [hres2_poison] at hpoison2
          | guardOnly_false_poisoned_any _ _ _ hpoison2 =>
              simp [hres2_poison] at hpoison2
      | inr hfalse₁ =>
        -- Run 0 takes true branch, Run 1 takes false branch
        -- This can only happen if the condition is NOT clean under R
        rcases hfalse₁ with ⟨hb₁, ht₁_e3⟩
        -- The condition bool values differ: b₀ = true ≠ false = b₁
        have hbNe : b₀ ≠ b₁ := by simp [hb₀, hb₁]
        -- If res1.qualType were clean under R, then from hres_agree1, the bool values must agree
        -- Since they differ, res1.qualType is NOT clean under R
        have hres1_not_clean : ¬ qtypCleanUnder R res1.qualType := fun hclean => by
          have hbool_typ : res1.qualType.etyp = ETyp.bool := hbool1
          have hnotref : ¬ ∃ t ls, res1.qualType.etyp = ETyp.ref t ls := by
            simp [hbool_typ]
          have hnotfun : res1.qualType.etyp.isFunctionType = false := by
            simp [hbool_typ, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have heq : Value.bool b₀ = Value.bool b₁ :=
            agreeValueUnder_nonref_eq_of_clean hclean hnotref hnotfun (hres_agree1 hclean)
          simp at heq
          exact hbNe heq
        -- Show res.qualType is not clean: from h_poison, if res is clean then res1.poison = false
        -- But ¬ qtypCleanUnder R res1 means res1.poison = true (when no guard tag applies)
        -- For divergent branches, we still need to construct full StepFR output
        -- Run 0 executed e2, Run 1 executed e3 - we need IH on each independently
        -- This is complex: need θ₀' from IH2 for run 0, θ₁' from IH3 for run 1
        -- For now, use sorry - this case requires substantial additional infrastructure
        sorry
    | inr hfalse₀ =>
      rcases hfalse₀ with ⟨hb₀, ht₀_e3⟩
      cases hbranch₁ with
      | inl htrue₁ =>
        -- Run 0 takes false branch, Run 1 takes true branch
        -- Similar to above - condition is not clean under R
        rcases htrue₁ with ⟨hb₁, ht₁_e2⟩
        have hbNe : b₀ ≠ b₁ := by simp [hb₀, hb₁]
        have hres1_not_clean : ¬ qtypCleanUnder R res1.qualType := fun hclean => by
          have hbool_typ : res1.qualType.etyp = ETyp.bool := hbool1
          have hnotref : ¬ ∃ t ls, res1.qualType.etyp = ETyp.ref t ls := by
            simp [hbool_typ]
          have hnotfun : res1.qualType.etyp.isFunctionType = false := by
            simp [hbool_typ, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have heq : Value.bool b₀ = Value.bool b₁ :=
            agreeValueUnder_nonref_eq_of_clean hclean hnotref hnotfun (hres_agree1 hclean)
          simp at heq
          exact hbNe heq
        -- Same reasoning as true-false case
        sorry
      | inr hfalse₁ =>
        -- Both runs take false branch
        rcases hfalse₁ with ⟨hb₁, ht₁_e3⟩
        -- Get IH for e3
        have hIH3 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          e3 ctxForE3 res3 htc3' R
        -- Use monotonicity lemmas to relate nextLoc/nextTag across typechecking
        have hlocMono : res1.nextLoc' ≤ res2.nextLoc' := by
          have : ctx''.nextLoc ≤ res2.nextLoc' := typecheck_nextLoc_mono ctx'' e2 fuel' res2 htc2'
          simp only [ctx'', ctx'] at this
          exact this
        have htagMono : res1.nextTag' ≤ res2.nextTag' := by
          have : ctx''.nextTag ≤ res2.nextTag' := typecheck_nextTag_mono ctx'' e2 fuel' res2 htc2'
          simp only [ctx'', ctx'] at this
          exact this
        -- ctxForE3 context setup - need to prove wfTypeContext
        have hwf3 : wfTypeContext ctxForE3 := by
          simp only [ctxForE3, ctx'', ctx']
          unfold wfTypeContext at hwf1 ⊢
          simp only [ctxAfter] at hwf1
          intro l hmem
          have hlt1 : l < res1.nextLoc' := hwf1 l hmem
          exact Nat.lt_of_lt_of_le hlt1 hlocMono
        have hric₀3 : runtimeInstantiatesCtx ctxForE3 cfg₀1.memory cfg₀1.varEnv θ₀1 := by
          -- runtimeInstantiatesCtx depends on memEnv and varEnv
          -- ctxForE3 has same memEnv and varEnv as ctx'' (only nextLoc/nextTag differ)
          simpa [ctxForE3, ctx'', ctx', ctxAfter] using hric₀1
        have hric₁3 : runtimeInstantiatesCtx ctxForE3 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
          simpa [ctxForE3, ctx'', ctx', ctxAfter] using hric₁1
        have htagR3 : regimeConsistentWithCtx ctxForE3 R := by
          -- regimeConsistentWithCtx = tagEnvConsistentWithRegime ∧ R.bound ≤ nextTag
          simp only [ctxForE3, ctx'', ctx', regimeConsistentWithCtx]
          simp only [ctxAfter, regimeConsistentWithCtx] at htagR1
          constructor
          · exact htagR1.1  -- tagEnvConsistentWithRegime preserved
          · exact Nat.le_trans htagR1.2 htagMono  -- R.bound ≤ res2.nextTag'
        have hagree_clean3 : agreeOnClean predSat R ctxForE3 cfg₀1.memory cfg₀1.varEnv θ₀1
                                                            cfg₁1.memory cfg₁1.varEnv θ₁1 := by
          simpa [ctxForE3, ctx'', ctx', ctxAfter] using hagree_clean1
        have ht₁_e3' : terminatesTo .ioFree e3
            { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv,
              nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
            cf₁ o₁ := by rw [← hcfg₁1_eq]; exact ht₁_e3
        -- Apply IH for e3
        have hstep_e3 :=
          hIH3 cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
            cf₀ cf₁ o₀ o₁
            hθ₀1wf hθ₁1wf hwf3 hric₀3 hric₁3 htagR3 hRbound hagree_clean3
            cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
            ht₀_e3 ht₁_e3'
        rcases hstep_e3 with ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, hwf3', hwfcf₀3, hwfcf₁3,
                              hric₀3', hric₁3', htagR3', hagree_clean3', hres_agree3⟩
        have hθext₀ : wfExtendsMap θ₀ θ₀3 := wfExtendsMap_trans hθext₀1 hθext₀3
        have hθext₁ : wfExtendsMap θ₁ θ₁3 := wfExtendsMap_trans hθext₁1 hθext₁3
        -- Similar to true-true case - both runs took false branch (e3)
        -- Same reasoning applies with res3 instead of res2
        refine ⟨θ₀3, θ₁3, hθext₀, hθext₁, ?hwf_final, hwfcf₀3, hwfcf₁3, ?hric₀_final,
                ?hric₁_final, ?htagR_final, ?hagree_final, ?hres_final⟩
        case hwf_final =>
          -- Same approach as true-true case
          unfold wfTypeContext ctxAfter
          simp only [h_memEnv, h_nextLoc]
          -- Get wfTypeResult res2 via typecheck_wfTypeResult
          have hwfres2 : wfTypeResult res2 := typecheck_wfTypeResult ctx'' e2 fuel' res2 hwf1' htc2'
          -- From hwf3': wfTypeContext (ctxAfter ctxForE3 res3), get wfTypeResult res3
          have hwfres3 : ∀ l, res3.memEnv'.contains l → l < res3.nextLoc' := by
            simp only [wfTypeContext, ctxAfter, ctxForE3, ctx'', ctx'] at hwf3'
            exact hwf3'
          exact wfTypeContext_joinMemEnvs_max res2.memEnv' res3.memEnv' res2.nextLoc' res3.nextLoc'
            hwfres2 hwfres3
        case hric₀_final =>
          -- Similar to true-true case but for e3
          unfold runtimeInstantiatesCtx ctxAfter
          simp only [h_memEnv]
          have hric₀3_parts := hric₀3'
          unfold runtimeInstantiatesCtx ctxAfter at hric₀3_parts
          simp only [ctxForE3, ctx'', ctx'] at hric₀3_parts
          constructor
          · intro l a hlookup
            have ⟨hcontains3, hmem_contains⟩ := hric₀3_parts.1 l a hlookup
            constructor
            · exact joinMemEnvs_contains_right res2.memEnv' res3.memEnv' l hcontains3
            · exact hmem_contains
          · intro x qt hvar_lookup
            exact hric₀3_parts.2 hvar_lookup
        case hric₁_final =>
          unfold runtimeInstantiatesCtx ctxAfter
          simp only [h_memEnv]
          have hric₁3_parts := hric₁3'
          unfold runtimeInstantiatesCtx ctxAfter at hric₁3_parts
          simp only [ctxForE3, ctx'', ctx'] at hric₁3_parts
          constructor
          · intro l a hlookup
            have ⟨hcontains3, hmem_contains⟩ := hric₁3_parts.1 l a hlookup
            constructor
            · exact joinMemEnvs_contains_right res2.memEnv' res3.memEnv' l hcontains3
            · exact hmem_contains
          · intro x qt hvar_lookup
            exact hric₁3_parts.2 hvar_lookup
        case htagR_final =>
          -- Similar to true-true case
          unfold regimeConsistentWithCtx ctxAfter
          simp only [h_tagEnv, h_nextTag]
          have htagR1_vals : tagEnvConsistentWithRegime res1.tagEnv' R ∧ R.bound ≤ res1.nextTag' := by
            simp only [regimeConsistentWithCtx, ctxAfter] at htagR1
            exact htagR1
          constructor
          · exact htagR1_vals.1
          · -- R.bound ≤ res3.nextTag' ≤ max res2.nextTag' res3.nextTag'
            have hbound3 : R.bound ≤ res3.nextTag' := by
              simp only [regimeConsistentWithCtx, ctxAfter] at htagR3'
              exact htagR3'.2
            exact Nat.le_trans hbound3 (Nat.le_max_right res2.nextTag' res3.nextTag')
        case hagree_final =>
          -- Similar to true-true case but for res3
          unfold agreeOnClean ctxAfter
          simp only [h_memEnv]
          have hagree3_parts := hagree_clean3'
          unfold agreeOnClean ctxAfter at hagree3_parts
          simp only [ctxForE3, ctx'', ctx'] at hagree3_parts
          constructor
          · -- Locations in joined memEnv
            intro l qt hlookup hclean
            by_cases hres3 : res3.memEnv'.contains l
            · -- l is in res3.memEnv' - use hagree3_parts
              -- For clean types under R, need detailed joinMemEnvs analysis
              sorry
            · -- l is only in res2.memEnv' (not in res3)
              -- θ₀3 and θ₁3 don't have l realized (they come from executing e3)
              -- Use both_unrealized
              have hctx_memEnv : (ctxAfter ctxForE3 res3).memEnv = res3.memEnv' := by
                simp only [ctxAfter]
              have hnotContains_ctx : ¬ (ctxAfter ctxForE3 res3).memEnv.contains l := by
                rw [hctx_memEnv]; exact hres3
              -- θ₀3.lookup l = none - use hric₀3' from IH3
              have hθ₀3_none : θ₀3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv (ctxAfter ctxForE3 res3)
                  cf₀.memory cf₀.varEnv θ₀3 l hric₀3' hnotContains_ctx
              have hθ₁3_none : θ₁3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv (ctxAfter ctxForE3 res3)
                  cf₁.memory cf₁.varEnv θ₁3 l hric₁3' hnotContains_ctx
              exact agreeLocUnder.both_unrealized l qt hθ₀3_none hθ₁3_none
          · -- Variables: unchanged since varEnv is the same
            intro x qt hvar_lookup hclean
            exact hagree3_parts.2 (x := x) (qt := qt) hvar_lookup hclean
        case hres_final =>
          -- Show that if res.qualType is clean, then res3.qualType is also clean
          -- Mirror of true-true case but using res3
          unfold resultAgreesIfClean
          intro hclean_res
          have hres_noPred : res.qualType.pred = Predicate.noPred :=
            typecheckIf_standard_pred_noPred ctxᵢ e1 e2 e3 fuel'.succ res htc' ⟨err, hmatch_fail⟩
          have hres_poison : res.qualType.poison = false := by
            cases hclean_res with
            | clean hp => exact hp
            | guard k htag _ _ =>
                simp [qtypGuardTag, hres_noPred] at htag
          -- Extract res3.qualType.poison = false from h_poison
          have hres3_poison : res3.qualType.poison = false := by
            have hjoin : joinPoison ctxᵢ.pc
              (joinPoison res1.qualType.poison (joinPoison res2.qualType.poison res3.qualType.poison)) = false := by
              rw [← h_poison]; exact hres_poison
            have ⟨_, h2⟩ := joinPoison_eq_false hjoin
            have ⟨_, h4⟩ := joinPoison_eq_false h2
            have ⟨_, h5⟩ := joinPoison_eq_false h4
            exact h5
          -- Show res3.qualType is clean
          have hclean3 : qtypCleanUnder R res3.qualType := by
            exact qtypCleanUnder.clean hres3_poison
          -- Apply hres_agree3 to get agreement on res3.qualType
          have hagree3 := hres_agree3 hclean3
          -- Transport from res3.qualType to res.qualType
          have hetyp_join' : res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                              res2.qualType.poison res3.qualType.poison := by
            apply typecheckIf_standard_etyp' ctxᵢ e1 e2 e3 fuel'.succ res res1 res2 res3
              htc' ⟨err, hmatch_fail⟩
            · simp only [Nat.succ_sub_one]; exact htc1
            · exact hbool1
            · simp only [Nat.succ_sub_one] at htc2 ⊢; exact htc2
            · simp only [Nat.succ_sub_one] at htc3 ⊢; exact htc3
          -- Case analyze on hagree3 to reconstruct agreement
          cases hagree3 with
          | clean_eq_nonref _hpoison3 hnotfun3 hnotref3 hEq =>
              -- Need to show joinETyps res2.qualType.etyp res3.qualType.etyp is non-function/non-ref
              -- Case split on res2.qualType.etyp structure
              cases hres2etyp : res2.qualType.etyp with
              | bool | int | unit | string =>
                have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
                  rw [hetyp_join', hres2etyp]
                  simp [joinETyps, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hnotref_res : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                  rw [hetyp_join', hres2etyp]
                  simp [joinETyps]
                exact agreeValueUnder.clean_eq_nonref hres_poison hnotfun_res hnotref_res hEq
              | arrow _ _ _ _ | parrow _ _ _ _ | ref _ _ =>
                -- If res2 is function/ref type and res3 is non-function/non-ref,
                -- this case should be impossible for well-typed programs since both
                -- branches must have compatible type structures.
                -- TODO: Add lemma showing branches have compatible type structures
                sorry
          | poisoned_noPred_eq_nonref hpoison3 _ _ _ _ =>
              simp [hres3_poison] at hpoison3
          | withPred_true_eq _ _ _ hnotfun3 hnotref3 hEq =>
              cases hres2etyp : res2.qualType.etyp with
              | bool | int | unit | string =>
                have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
                  rw [hetyp_join', hres2etyp]
                  simp [joinETyps, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hnotref_res : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                  rw [hetyp_join', hres2etyp]
                  simp [joinETyps]
                exact agreeValueUnder.clean_eq_nonref hres_poison hnotfun_res hnotref_res hEq
              | arrow _ _ _ _ | parrow _ _ _ _ | ref _ _ =>
                -- Same as above - should be impossible for well-typed programs
                sorry
          | @clean_internal_arrow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              -- Arrow case - anticipating changes to function handling
              sorry
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- Dirty arrow: same approach as true-true case but with res3
              have hisArrow_res : res.qualType.etyp.isArrow = true := by
                rw [hetyp_join']
                -- Extract arrow structure from res3.qualType.etyp
                cases hres3etyp : res3.qualType.etyp with
                | arrow st1 st2 p tcls =>
                    cases hres2etyp : res2.qualType.etyp with
                    | arrow st1' st2' p2 tcls2 =>
                        simp only [joinETyps]
                        split <;> simp [ETyp.isArrow]
                    | int | bool | unit | string | ref _ _ | parrow _ _ _ _ =>
                        -- Impossible: type mismatch would cause typechecker to fail
                        -- res3.etyp is arrow but res2.etyp is not, violates beqETypSignature check
                        sorry
                | int =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | bool =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | unit =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | string =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | ref _ _ =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
                | parrow _ _ _ _ =>
                    rw [hres3etyp] at hisArrow
                    simp [ETyp.isArrow] at hisArrow
              by_cases hclean_internal_res : internalPoisonClean res.qualType
              · sorry
              · have htyp1_res : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
                  cases hres3etyp : res3.qualType.etyp with
                  | arrow st1_3 st2_3 p3 tcls3 =>
                      have htyp1' : valueHasETyp θ₀3 o₀ (ETyp.arrow st1_3 st2_3 p3 tcls3) := by
                        rw [← hres3etyp]; exact htyp1
                      cases htyp1' with
                      | closure x e env _ _ _ _ =>
                          rw [hetyp_join', hres3etyp]
                          cases hres2etyp : res2.qualType.etyp with
                          | arrow st1' st2' p2 tcls2 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.closure x e env _ _ _ _
                          | int | bool | unit | string | ref _ _ | parrow _ _ _ _ =>
                              -- Impossible: contradicts hisArrow_res (type mismatch)
                              sorry
                  | _ =>
                      rw [hres3etyp] at hisArrow
                      simp [ETyp.isArrow] at hisArrow
                have htyp2_res : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
                  cases hres3etyp : res3.qualType.etyp with
                  | arrow st1_3 st2_3 p3 tcls3 =>
                      have htyp2' : valueHasETyp θ₁3 o₁ (ETyp.arrow st1_3 st2_3 p3 tcls3) := by
                        rw [← hres3etyp]; exact htyp2
                      cases htyp2' with
                      | closure x e env _ _ _ _ =>
                          rw [hetyp_join', hres3etyp]
                          cases hres2etyp : res2.qualType.etyp with
                          | arrow st1' st2' p2 tcls2 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.closure x e env _ _ _ _
                          | int | bool | unit | string | ref _ _ | parrow _ _ _ _ =>
                              -- Impossible: contradicts hisArrow_res (type mismatch)
                              sorry
                  | _ =>
                      rw [hres3etyp] at hisArrow
                      simp [ETyp.isArrow] at hisArrow
                exact agreeValueUnder.dirty_internal_arrow hclean_internal_res hisArrow_res htyp1_res htyp2_res
          | @clean_internal_parrow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              sorry
          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
              have hisParrow_res : res.qualType.etyp.isParrow = true := by
                rw [hetyp_join']
                cases hres3etyp : res3.qualType.etyp with
                | parrow st1 st2 p tcls =>
                    cases hres2etyp : res2.qualType.etyp with
                    | parrow st1' st2' p2 tcls2 =>
                        simp only [joinETyps]
                        split <;> simp [ETyp.isParrow]
                    | int | bool | unit | string | ref _ _ | arrow _ _ _ _ =>
                        -- Impossible: type mismatch would cause typechecker to fail
                        -- res3.etyp is parrow but res2.etyp is not, violates beqETypSignature check
                        sorry
                | int =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | bool =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | unit =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | string =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | ref _ _ =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
                | arrow _ _ _ _ =>
                    rw [hres3etyp] at hisParrow
                    simp [ETyp.isParrow] at hisParrow
              by_cases hclean_internal_res : internalPoisonClean res.qualType
              · sorry
              · have htyp1_res : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
                  cases hres3etyp : res3.qualType.etyp with
                  | parrow st1_3 st2_3 p3 tcls3 =>
                      have htyp1' : valueHasETyp θ₀3 o₀ (ETyp.parrow st1_3 st2_3 p3 tcls3) := by
                        rw [← hres3etyp]; exact htyp1
                      cases htyp1' with
                      | peClosure x pe env _ _ _ _ =>
                          rw [hetyp_join', hres3etyp]
                          cases hres2etyp : res2.qualType.etyp with
                          | parrow st1' st2' p2 tcls2 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.peClosure x pe env _ _ _ _
                          | int | bool | unit | string | ref _ _ | arrow _ _ _ _ =>
                              -- Impossible: contradicts hisParrow_res (type mismatch)
                              sorry
                  | _ =>
                      rw [hres3etyp] at hisParrow
                      simp [ETyp.isParrow] at hisParrow
                have htyp2_res : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
                  cases hres3etyp : res3.qualType.etyp with
                  | parrow st1_3 st2_3 p3 tcls3 =>
                      have htyp2' : valueHasETyp θ₁3 o₁ (ETyp.parrow st1_3 st2_3 p3 tcls3) := by
                        rw [← hres3etyp]; exact htyp2
                      cases htyp2' with
                      | peClosure x pe env _ _ _ _ =>
                          rw [hetyp_join', hres3etyp]
                          cases hres2etyp : res2.qualType.etyp with
                          | parrow st1' st2' p2 tcls2 =>
                              simp only [joinETyps]
                              split <;> exact valueHasETyp.peClosure x pe env _ _ _ _
                          | int | bool | unit | string | ref _ _ | arrow _ _ _ _ =>
                              -- Impossible: contradicts hisParrow_res (type mismatch)
                              sorry
                  | _ =>
                      rw [hres3etyp] at hisParrow
                      simp [ETyp.isParrow] at hisParrow
                exact agreeValueUnder.dirty_internal_parrow hclean_internal_res hisParrow_res htyp1_res htyp2_res
          | @clean_ref _ _ _ _ _ _ _ _ =>
              sorry
          | @withPred_true_ref _ _ _ _ _ _ _ _ _ =>
              sorry
          | @poisoned_noPred_ref _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              -- res3 is poisoned, but we know res3.qualType.poison = false from hres3_poison
              -- This contradicts hclean3 which requires res3.qualType to be clean
              sorry
          | @withPred_false_poisoned_fail _ _ _ _ _ _ _ _ _ _ =>
              -- res3 is poisoned, contradiction with hclean3
              sorry
          | @guardOnly_false_poisoned_any _ _ _ _ _ _ _ =>
              -- res3 is poisoned under guard conditions
              sorry

-- Stub lemma for assignment (not yet proven)
private lemma stepFR_assign
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.assign e1 e2) res predSat := by
  sorry

-- World-free version of stepFRW_deref (simplified with sorry)
private lemma stepFR_deref
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.deref e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.deref e) res predSat := by
  sorry -- TODO: Complex proof involving memory lookups and ref type agreement

-- Stub lemma for while loop (not yet proven)
private lemma stepFR_kwhile
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.kwhile e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.kwhile e1 e2) res predSat := by
  sorry

-- Stub lemma for function application (not yet proven)
private lemma stepFR_app
  (ctxᵢ : TypeContext) (predSat : PredSat) (R : Regime)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ R (Expr.app e1 e2) res predSat := by
  /-
  PROOF STRATEGY (based on function-poison.md):

  The key design decision is that closure agreement is gated on INTERNAL poison
  (the `p` in the arrow type), not outer poison:

  1. Parse typecheck result to extract:
     - res2: result of typechecking e2 (argument)
     - res1: result of typechecking e1 (function)
     - Function type: arrow st1 st2 p tcls (with internal poison p)

  2. For StepFR, introduce premises and apply IH:
     - Apply IH for e2 → agreement on argument value, intermediate state agreement
     - Apply IH for e1 → agreement on function value (closure)

  3. Case split on internal poison p (the key insight from function-poison.md):

     CASE p = false (clean internal poison):
     - Both runs have closures with the same body (from clean_internal_arrow agreement)
     - Establish agreeCapturedEnv from agreeOnClean using agreeCapturedEnv_of_agreeOnClean
     - Set up body evaluation context with parameter bound to agreeing arguments
     - Apply IH for body to get result agreement
     - Build final StepFR result

     CASE p = true (dirty internal poison):
     - Use dirty_internal_arrow for closure agreement (no constraints)
     - The body's pc will include p = true, making results necessarily dirty
     - resultAgreesIfClean is vacuously satisfied:
       * If result is clean_under_R, then its poison must be false
       * But result poison includes internal poison p = true
       * So clean result is impossible, making the implication vacuously true
     - Build StepFR result with extended realization maps

  The proof requires:
  - terminatesTo_app_inv': Inversion lemma for app evaluation (TODO)
  - typecheckApp_structure: Helper to extract typecheck structure (TODO)
  - IH application for body evaluation (recursive case)
  -/
  -- Parse typecheck result (via typecheckApp)
  have htc' : typecheckApp ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  -- Use the full structure lemma (exposes the closure-application mapM spine)
  obtain ⟨res2, res1, argEtyp, argPoison, argPred, hres2_qt, htc2, htc1, happ_cases⟩ :=
    typecheckApp_arrow_structure_full ctxᵢ e1 e2 fuel' res htc'
  have htc2' : typecheck ctxᵢ e2 fuel' = .ok res2 := by
    simpa [typecheck] using htc2
  let ctx' : TypeContext :=
    { ctxᵢ with memEnv := res2.memEnv', tagEnv := res2.tagEnv', nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
  have htc1' : typecheck ctx' e1 fuel' = .ok res1 := by
    simpa [ctx', typecheck] using htc1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctxᵢ res2 htc2' R
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx' res1 htc1' R
  -- Introduce StepFR premises
  intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert evaluation of app for both runs
  have hstruct₀ := terminatesTo_app_inv' e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have hstruct₁ := terminatesTo_app_inv' e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁

  -- Extract the common sub-evaluation of the argument `e2`.
  -- We keep the closure vs peClosure split for later, but `e2` is evaluated in both cases.
  rcases hstruct₀ with hcl₀ | hpe₀
  · rcases hcl₀ with
      ⟨cfg₀2, v₀2, cfg₀1, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm₀1, ht₀_body, hcf₀_eq, hpm₀2, hpm₀_final⟩
    rcases hstruct₁ with hcl₁ | hpe₁
    · rcases hcl₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm₁1, ht₁_body, hcf₁_eq, hpm₁2, hpm₁_final⟩

      -- Step on the argument evaluation using IH2.
      have hstep_e2 :=
        hIH2 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hagree2, harg_agree⟩
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁

      -- Prepare the inputs for IH1 (function evaluation under ctx' = ctxAfter ctxᵢ res2).
      have hwf_ctx' : wfTypeContext ctx' := by
        simpa [ctx', ctxAfter] using hwf2
      have hric₀2' : runtimeInstantiatesCtx ctx' cfg₀2.memory cfg₀2.varEnv θ₀2 := by
        simpa [ctx', ctxAfter] using hric₀2
      have hric₁2' : runtimeInstantiatesCtx ctx' cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        simpa [ctx', ctxAfter] using hric₁2
      have htagR2' : regimeConsistentWithCtx ctx' R := by
        simpa [ctx', ctxAfter] using htagR2
      have hagree2' :
          agreeOnClean predSat R ctx' cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        simpa [ctx', ctxAfter] using hagree2

      -- Ensure the two runs agree on pureMode at the start of `e1` (required by StepFR).
      have hpm_cfg2 : cfg₀2.pureMode = cfg₁2.pureMode := by
        -- both are preserved from the initial pm
        rw [hpm₀2, hpm₁2]

      -- Step on the function evaluation using IH1.
      -- We use cfg₀2.pureMode as the shared pureMode witness, and rewrite the second run if needed.
      have hcfg₁2_eq :
          cfg₁2 =
            { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        cases cfg₁2
        simp [hpm_cfg2]
      have ht₁_e1' :
          terminatesTo .ioFree e1
            { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode }
            cfg₁1 (Value.closure x₁ body₁ env₁) := by
        rw [← hcfg₁2_eq]
        exact ht₁_e1
      have hwfcfg₁2' :
          wfConfig { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        rw [← hcfg₁2_eq]
        exact hwfcfg₁2
      have hstep_e1 :=
        hIH1 cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf_ctx' hric₀2' hric₁2' htagR2' hRbound hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, hwf3, hwfcfg₀3, hwfcfg₁3,
          hric₀3, hric₁3, htagR3, hagree3, hfun_agree⟩

      -- Use preservation to connect runtime closures to the arrow/parrow split in `happ_cases`.
      -- This lets us rule out mixed closure/peClosure outcomes for well-typed programs.
      let w_default := LeanProofs.defaultWorld
      have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₀2.memory, varEnv := cfg₀2.varEnv, nextAddr := cfg₀2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₀1 (Value.closure x₀ body₀ env₀) := by
        rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
        exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
      have ht₁_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₁1 (Value.closure x₁ body₁ env₁) := by
        rcases ht₁_e1' with ⟨fuel₁, verbose₁, hpure₁⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
        exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
      have hθ₀3wf : wfRealizationMap θ₀3 := hθext₀3.2 hθ₀2wf
      have hθ₁3wf : wfRealizationMap θ₁3 := hθext₁3.2 hθ₁2wf
      have hric₀3_mem : runtimeInstantiatesCtx { ctx' with memEnv := res1.memEnv' }
          cfg₀1.memory cfg₀1.varEnv θ₀3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter, ctx'] using hric₀3
      have hric₁3_mem : runtimeInstantiatesCtx { ctx' with memEnv := res1.memEnv' }
          cfg₁1.memory cfg₁1.varEnv θ₁3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter, ctx'] using hric₁3
      have hv₀_fun_typed : valueHasETyp θ₀3 (Value.closure x₀ body₀ env₀) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 ctx' fuel' res1
          cfg₀2.memory cfg₀1.memory cfg₀2.varEnv cfg₀1.varEnv θ₀2 θ₀3
          cfg₀2.nextAddr cfg₀1.nextAddr cfg₀2.pureMode cfg₀1.pureMode
          (Value.closure x₀ body₀ env₀) w_default w_default
          hwf_ctx' htc1' hθ₀2wf hθ₀3wf hθext₀3 hric₀2' hric₀3_mem ht₀_e1_w).1
      have hv₁_fun_typed : valueHasETyp θ₁3 (Value.closure x₁ body₁ env₁) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 ctx' fuel' res1
          cfg₁2.memory cfg₁1.memory cfg₁2.varEnv cfg₁1.varEnv θ₁2 θ₁3
          cfg₁2.nextAddr cfg₁1.nextAddr cfg₀2.pureMode cfg₁1.pureMode
          (Value.closure x₁ body₁ env₁) w_default w_default
          hwf_ctx' htc1' hθ₁2wf hθ₁3wf hθext₁3 hric₁2' hric₁3_mem ht₁_e1_w).1
      -- Split on the typing spine: since both runs produced regular closures,
      -- the `.parrow` branch is impossible.
      cases happ_cases with
      | inl harr =>
          -- Remaining work for the `.arrow` case:
          -- relate the body evaluations (`ht₀_body`, `ht₁_body`) to the `mapM applyFnTClosure` spine,
          -- and lift post-state agreement to `ctxAfter ctxᵢ res` (similar to `stepFR_ite`).
          sorry
      | inr hparr =>
          -- Contradiction: `res1.qualType.etyp` is parrow, but we have a runtime closure value.
          rcases hparr with ⟨st1, st2, p, p1, tcls, _results, _first, _rest, hetyp_parr, _hpoison1, _hnonEmpty, _hsub, _hmapM, _hresults, _hjoin⟩
          have hv_parr : valueHasETyp θ₀3 (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := by
            simpa [hetyp_parr] using hv₀_fun_typed
          cases hv_parr
    · -- Mixed case: run 0 evaluates to closure, run 1 evaluates to peClosure.
      -- This is impossible for well-typed programs: `e1` cannot evaluate to a regular closure
      -- in one run and to a predicated closure in the other, because both runs share the same
      -- static function type `res1.qualType.etyp`.
      rcases hpe₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, hcf₁_eq, hpm₁2, hpm₁_final⟩

      -- Step on `e2` to obtain a post-`e2` instantiation for `ctx'`.
      have hstep_e2 :=
        hIH2 μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hagree2, _harg_agree⟩
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁

      -- Prepare the preconditions for stepping `e1` under `ctx'`.
      have hwf_ctx' : wfTypeContext ctx' := by
        simpa [ctx', ctxAfter] using hwf2
      have hric₀2' : runtimeInstantiatesCtx ctx' cfg₀2.memory cfg₀2.varEnv θ₀2 := by
        simpa [ctx', ctxAfter] using hric₀2
      have hric₁2' : runtimeInstantiatesCtx ctx' cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        simpa [ctx', ctxAfter] using hric₁2
      have htagR2' : regimeConsistentWithCtx ctx' R := by
        simpa [ctx', ctxAfter] using htagR2
      have hagree2' :
          agreeOnClean predSat R ctx' cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        simpa [ctx', ctxAfter] using hagree2

      -- Align pureMode for the StepFR call on `e1`.
      have hpm_cfg2 : cfg₀2.pureMode = cfg₁2.pureMode := by
        rw [hpm₀2, hpm₁2]
      have hcfg₁2_eq :
          cfg₁2 =
            { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        cases cfg₁2
        simp [hpm_cfg2]
      have ht₁_e1' :
          terminatesTo .ioFree e1
            { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode }
            cfg₁1 (Value.peClosure x₁ body₁ env₁) := by
        rw [← hcfg₁2_eq]
        exact ht₁_e1
      have hwfcfg₁2' :
          wfConfig { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        rw [← hcfg₁2_eq]
        exact hwfcfg₁2

      -- Step on `e1` (closure vs peClosure).
      have hstep_e1 :=
        hIH1 cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf_ctx' hric₀2' hric₁2' htagR2' hRbound hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, _hwf3, _hwfcfg₀3, _hwfcfg₁3,
          hric₀3, hric₁3, _htagR3, _hagree3, _hfun_agree⟩
      have hθ₀3wf : wfRealizationMap θ₀3 := hθext₀3.2 hθ₀2wf
      have hθ₁3wf : wfRealizationMap θ₁3 := hθext₁3.2 hθ₁2wf

      -- Convert to world-indexed evaluation and apply preservation to get value typing for each run.
      let w_default := LeanProofs.defaultWorld
      have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₀2.memory, varEnv := cfg₀2.varEnv, nextAddr := cfg₀2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₀1 (Value.closure x₀ body₀ env₀) := by
        rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
        exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
      have ht₁_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₁1 (Value.peClosure x₁ body₁ env₁) := by
        rcases ht₁_e1' with ⟨fuel₁, verbose₁, hpure₁⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
        exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩

      -- `runtimeInstantiatesCtx` only depends on memEnv/varEnv, so we can reuse it for the
      -- specific context shape required by `preservation_valueW`.
      have hric₀3_mem : runtimeInstantiatesCtx { ctx' with memEnv := res1.memEnv' }
          cfg₀1.memory cfg₀1.varEnv θ₀3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter, ctx'] using hric₀3
      have hric₁3_mem : runtimeInstantiatesCtx { ctx' with memEnv := res1.memEnv' }
          cfg₁1.memory cfg₁1.varEnv θ₁3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter, ctx'] using hric₁3

      have hv₀_fun_typed : valueHasETyp θ₀3 (Value.closure x₀ body₀ env₀) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 ctx' fuel' res1
          cfg₀2.memory cfg₀1.memory cfg₀2.varEnv cfg₀1.varEnv θ₀2 θ₀3
          cfg₀2.nextAddr cfg₀1.nextAddr cfg₀2.pureMode cfg₀1.pureMode
          (Value.closure x₀ body₀ env₀) w_default w_default
          hwf_ctx' htc1' hθ₀2wf hθ₀3wf hθext₀3 hric₀2' hric₀3_mem ht₀_e1_w).1
      have hv₁_fun_typed : valueHasETyp θ₁3 (Value.peClosure x₁ body₁ env₁) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 ctx' fuel' res1
          cfg₁2.memory cfg₁1.memory cfg₁2.varEnv cfg₁1.varEnv θ₁2 θ₁3
          cfg₁2.nextAddr cfg₁1.nextAddr cfg₀2.pureMode cfg₁1.pureMode
          (Value.peClosure x₁ body₁ env₁) w_default w_default
          hwf_ctx' htc1' hθ₁2wf hθ₁3wf hθext₁3 hric₁2' hric₁3_mem ht₁_e1_w).1

      -- Expose the (unique) shape of `res1.qualType.etyp` by splitting `res1.qualType`.
      cases hqt1 : res1.qualType with
      | mk etyp1 poison1 pred1 =>
        -- Now `res1.qualType.etyp = etyp1`.
        have harr : ∃ st1 st2 p tcls, etyp1 = ETyp.arrow st1 st2 p tcls := by
          -- rewrite to match the closure constructor
          have : valueHasETyp θ₀3 (Value.closure x₀ body₀ env₀) etyp1 := by simpa [hqt1] using hv₀_fun_typed
          cases this with
          | closure _ _ _ st1 st2 p tcls =>
            exact ⟨st1, st2, p, tcls, rfl⟩
        have hparr : ∃ st1 st2 p tcls, etyp1 = ETyp.parrow st1 st2 p tcls := by
          have : valueHasETyp θ₁3 (Value.peClosure x₁ body₁ env₁) etyp1 := by simpa [hqt1] using hv₁_fun_typed
          cases this with
          | peClosure _ _ _ st1 st2 p tcls =>
            exact ⟨st1, st2, p, tcls, rfl⟩
        rcases harr with ⟨st1a, st2a, pa, tclsa, het_arrow⟩
        rcases hparr with ⟨st1p, st2p, pp, tclsp, het_parrow⟩
        -- Contradiction: an `ETyp` cannot be both `arrow` and `parrow`.
        exfalso
        have : ETyp.arrow st1a st2a pa tclsa = ETyp.parrow st1p st2p pp tclsp :=
          het_arrow.symm.trans het_parrow
        cases this
  · -- peClosure case for run 0 (handled symmetrically to closure case above).
    -- The proof follows the same structure, using the `.parrow` branch of `happ_cases`
    -- and the `peClosure` branch of `terminatesTo_app_inv'`.
    sorry


-- ================================================================
-- I/O-free fault-robustness proofs
-- ================================================================

section TypeSystemEnforcesFaultRobustness_IOFree_proof

-- I/O-free step theorem: proves StepFR directly (no world-threading)
-- Restructured to avoid variable capture: induction is generalized over all expressions
theorem TypeSystemEnforcesFaultRobustness_step_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat := by
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel res htc R
  -- Use strong induction on fuel, generalized over all e and ctxᵢ
  -- The key insight: we need IH to work for any I/O-free expression, not just our specific e
  revert e ctxᵢ res htc R
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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat R Expr.unit res Value.unit hval hpoison hnotfun hnotref hctxAfter
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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat R (Expr.num n) res (Value.num n) hval hpoison hnotfun hnotref hctxAfter
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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat R (Expr.bool b) res (Value.bool b) hval hpoison hnotfun hnotref hctxAfter
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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat R (Expr.str s) res (Value.str s) hval hpoison hnotfun hnotref hctxAfter
        | var name =>
            exact stepFR_var .ioFree ctxᵢ predSat R name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                exact stepFR_op ctxᵢ predSat R e1 e2 op fuel' res IH htc
        | unaryop uop e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                exact stepFR_unaryop ctxᵢ predSat R uop e fuel' res IH htc
        | ite e1 e2 e3 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckIf] at htc
            | succ fuel' =>
                exact stepFR_ite ctxᵢ predSat R e1 e2 e3 fuel' res IH htc
        | newRef e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                exact stepFR_newRef ctxᵢ predSat R e fuel' res IH htc
        | assign e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckAssign] at htc
            | succ fuel' =>
                exact stepFR_assign ctxᵢ predSat R e1 e2 fuel' res IH htc
        | deref e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckDeref] at htc
            | succ fuel' =>
                exact stepFR_deref ctxᵢ predSat R e fuel' res IH htc
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                exact stepFR_seq ctxᵢ predSat R e1 e2 fuel' res IH htc
        | kwhile e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckWhile] at htc
            | succ fuel' =>
                exact stepFR_kwhile ctxᵢ predSat R e1 e2 fuel' res IH htc
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                exact stepFR_vlet ctxᵢ predSat R vname e1 e2 fuel' res IH htc
        | fn name ty e1 ty2 =>
            exact stepFR_fn .ioFree ctxᵢ predSat R name ty e1 ty2 fuel res htc
        | pfn name ty e1 ty2 =>
            exact stepFR_pfn .ioFree ctxᵢ predSat R name ty e1 ty2 fuel res htc
        | app e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckApp] at htc
            | succ fuel' =>
                exact stepFR_app ctxᵢ predSat R e1 e2 fuel' res IH htc
        | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            -- In `.ioFree` mode, I/O constructs cannot terminate, so StepFR is vacuous.
            intro μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
            have : False := by
              rcases ht₀ with ⟨fuelT, verboseT, hpureT⟩
              -- In `.ioFree` mode, evaluation yields `ioForbidden`, never `.success`.
              have h_world := congrArg (fun f => f LeanProofs.defaultWorld) hpureT
              cases fuelT with
              | zero =>
                  -- fuel = 0 yields outOfFuel, not success
                  simp [LeanPoison.beval, pure] at h_world
                  cases h_world
              | succ fuelT' =>
                  -- fuel > 0: these constructs yield ioForbidden, not success
                  simp [LeanPoison.beval, pure] at h_world
                  cases h_world
            exact False.elim this

end TypeSystemEnforcesFaultRobustness_IOFree_proof

-- Bridges from step theorem to full specification
def FaultRobustnessSpec_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool) (check : Tag → Option Bool),
    let R : Regime := ⟨ctx.nextTag, check⟩
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime R s →
    regimeBounded R →
    wfRealizationMap θ₁ →  wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } →
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ →  consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat R s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs predSat R s ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo .ioFree e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
    terminatesTo .ioFree e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

def TypeSystemEnforcesFaultRobustness_spec_ioFree
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      wfTypeContext ctx →
      ctx.pc = false →
      ctx.tagEnv = {} →
      ∀ (predSat : PredSat),
        PredSatLaws predSat →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          FaultRobustnessSpec_ioFree e s obs ctx predSat)

theorem TypeSystemEnforcesFaultRobustness_impl_IOFree :
  (∀ e ctxᵢ predSat, TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx hwf _hpc hte predSat _hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm check
  have hstep' := hstep e ctx predSat
  have hstep' := hstep' fuel res htc
  dsimp only [FaultRobustnessSpec_ioFree]
  intro cf₁ cf₂ o₁ o₂ hR hRbound hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R : Regime := ⟨ctx.nextTag, check⟩ with hRdef
  have hagree_clean :
      agreeOnClean predSat R ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ :=
    agreeOnCriticalAndTrusted_implies_agreeOnClean
      predSat R s ctx μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ hctx hagree htrusted
  have htagR : tagEnvConsistentWithRegime ctx.tagEnv R := by
    intro k deps hlookup
    -- Empty tag environment at the top level.
    have hempty : ctx.tagEnv.get? k = none := by simp [hte]
    rw [hempty] at hlookup
    cases hlookup
  -- regimeConsistentWithCtx is now a conjunction: tagEnvConsistentWithRegime ∧ R.bound ≤ nextTag
  have hreg : regimeConsistentWithCtx ctx R := by
    constructor
    · exact htagR
    · simp [R]
  have hstep_fr := hstep' R μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂ hθ₁ hθ₂ hwf hric₁ hric₂ hreg hRbound hagree_clean a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  -- StepFR result structure: ∃ θ₁' θ₂', wfExtendsMap ∧ wfExtendsMap ∧ wfTypeContext ∧
  --   wfConfig ∧ wfConfig ∧ agreeOnClean ∧ resultAgreesIfClean
  rcases hstep_fr with ⟨θ₁', θ₂', hwfext₁, hwfext₂, _hwfctx', _hwfcfg₁', _hwfcfg₂', _hric₁', _hric₂', _hreg', hagree_clean', hret_agree⟩
  refine ⟨θ₁', θ₂', hwfext₁, hwfext₂, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · -- Observable memory locations agree
    intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hctx_lookup : (ctxAfter ctx res).memEnv.lookup l = some qt := by
      simpa [ctxAfter] using hlookup_mem
    have hclean : qtypCleanUnder R qt := by
      exact qtypCleanUnder.clean hpoison
    have hlocEntry : agreeLocUnder predSat R cf₁.memory cf₂.memory θ₁' θ₂' (l, qt) :=
      (hagree_clean'.1 l qt hctx_lookup hclean)
    cases hlocEntry with
    | agree_values _l _qt a₁' a₂' n₁ n₂ hreal₁ hreal₂ hlookup₁ hlookup₂ hagree =>
        -- Reduce to equality of stored ints via agreement on the stored values.
        have hvalEq : n₁ = n₂ := by
          cases hagree with
          | clean_eq_nonref _ _ _ hval =>
              cases hval
              rfl
          | poisoned_noPred_eq_nonref _ _ _ _ hval =>
              cases hval
              rfl
          | clean_internal_arrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isArrow = true implies function type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisArrow) (by decide)
          | clean_internal_parrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isParrow = true implies parrow type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisParrow) (by decide)
          | clean_ref _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | poisoned_noPred_ref _ _ _ _ _ hv1 _ _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ _ hval =>
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
        refine ⟨a₁', ?_⟩
        refine And.intro hreal₁ ?_
        refine ⟨a₂', ?_⟩
        refine And.intro hreal₂ ?_
        calc
          cf₁.memory.lookup a₁' = some n₁ := hlookup₁
          _ = some n₂ := by simp [hvalEq]
          _ = cf₂.memory.lookup a₂' := by symm; exact hlookup₂
    | both_unrealized _l _qt _hnone₁ _hnone₂ =>
        exact Or.inr ⟨_hnone₁, _hnone₂⟩
  · -- Return value agrees
    cases hretOpt : obs.retEtyp? with
    | none =>
        simp
    | some et =>
        -- Use return agreement from the step proof.
        rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
        have hret_notfun_obs : et.isFunctionType = false := by
          simpa [wfObsSpec, hretOpt] using _hos
        have hret_clean : qtypCleanUnder R res.qualType := by
          exact qtypCleanUnder.clean hret_poison
        have hret_agree' :
            agreeValueUnder predSat R cf₁.memory cf₂.memory θ₁' θ₂' res.qualType o₁ o₂ :=
          hret_agree hret_clean
        cases et with
        | ref t ls =>
            cases hret_agree' with
            | @clean_ref _t _ls l₁ l₂ a₁' a₂' _qt _v₁ _v₂ hpoison' hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l₁, ?_⟩
                  refine And.intro hin1 ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l₂, ?_⟩
                  refine And.intro hin2 ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k _t _ls l₁ l₂ a₁' a₂' _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin1 hv1 hlookup2 hin2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l₁, ?_⟩
                  refine And.intro hin1 ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l₂, ?_⟩
                  refine And.intro hin2 ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | clean_eq_nonref _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | poisoned_noPred_eq_nonref _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | withPred_true_eq _ _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨t, ls, hret_et⟩
                exact False.elim this
            | clean_internal_arrow _ hetyp _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_arrow _ hisArrow =>
                -- qt.etyp is an arrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                sorry
            | clean_internal_parrow _ hetyp _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_parrow _ hisParrow =>
                -- qt.etyp is a parrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                sorry



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
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | bool =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | unit =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | string =>
            have hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | arrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs
        | parrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs

-- Main I/O-free theorem
theorem TypeSystemEnforcesFaultRobustness_IOFree
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs := by
  apply TypeSystemEnforcesFaultRobustness_impl_IOFree
  · intro e' ctxᵢ predSat
    exact TypeSystemEnforcesFaultRobustness_step_IOFree e' ctxᵢ predSat
