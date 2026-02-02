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
import LeanProofs.Equality
import LeanProofs.PreservationProofs
import LeanProofs.VarEnvPreservation
import LeanProofs.MemoryMonotonicity
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open List.Mem
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
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true

-- Regime consistency with a typing context: (i) tags known true in the context must be true in the
-- regime interpretation, and (ii) the regime's bound is below the context's fresh-tag supply.
--
-- Intended reading: `R` only interprets *input/spec* tags (< R.bound). The context's `nextTag`
-- tracks the current supply for fresh internal tags, and it should stay above `R.bound`.
def regimeConsistentWithCtx (ctx : TypeContext) (R : Regime) : Prop :=
  tagEnvConsistentWithRegime ctx.tagEnv R ∧ R.bound ≤ ctx.nextTag

-- Helper lemma: regimeConsistentWithCtx transfers from input regime to output regime
-- when we have monotonicity and a typecheck result.
-- The key insight is that the typechecker maintains the invariant that tags that are
-- still `true` in the output tagEnv are also present in the output regime.
lemma regimeConsistentWithCtx_of_typecheckResult (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (h_input : regimeConsistentWithCtx ctx ctx.regime)
    (h_mono : Regime.monotoneStep ctx.regime res.regime')
    (htc : typecheck ctx e fuel = .ok res) :
    regimeConsistentWithCtx (ctxAfter ctx res) res.regime' := by
  unfold regimeConsistentWithCtx at h_input ⊢
  constructor
  · -- tagEnvConsistentWithRegime res.tagEnv' res.regime'
    -- This requires proving: if res.tagEnv'.get? k = some (true, deps), then res.regime'.lookup? k = some true
    -- The typechecker maintains this invariant through invalidateRegimeDeps which syncs tagEnv and regime.
    -- Key insight: if k is true in res.tagEnv', either:
    -- (a) k was true in ctx.tagEnv and survived invalidation → ctx.regime.lookup? k = some true by h_input.1,
    --     and since invalidation syncs tagEnv and regime, res.regime'.lookup? k = some true
    -- (b) k is fresh (>= ctx.nextTag) → but fresh tags can't be true with regime entry (contradiction)
    -- This is a complex typechecker invariant; sorry for now.
    intro k deps hget
    sorry
  · -- res.regime'.bound ≤ (ctxAfter ctx res).nextTag
    simp only [ctxAfter]
    have hbound_eq : res.regime'.bound = ctx.regime.bound := h_mono.1
    rw [hbound_eq]
    have h_nextTag_mono : ctx.nextTag ≤ res.nextTag' := typecheck_nextTag_mono ctx e fuel res htc
    exact Nat.le_trans h_input.2 h_nextTag_mono

-- Helper lemma: regimeBounded transfers under monotonicity (bounds are equal)
lemma regimeBounded_of_monotoneStep (R R' : Regime)
    (h_bounded : regimeBounded R)
    (h_mono : Regime.monotoneStep R R') :
    regimeBounded R' := by
  intro k hk
  have hbound_eq : R'.bound = R.bound := h_mono.1
  rw [hbound_eq] at hk
  have hR_none := h_bounded k hk
  -- Use contrapositive of h_mono.2.2: R.lookup? k = none → R'.lookup? k = none
  by_contra h_not_none
  have h_R_not_none := h_mono.2.2 k h_not_none
  exact h_R_not_none hR_none

-- Bridge lemma: connect spec-indexed consistency to context-indexed consistency
lemma consistentRegimeSpec_implies_consistentWithRegime
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (h_spec : consistentRegimeSpec predSat R s μ ρ θ)
    (h_match : ctxMatchesInputSpec s ctx)
    (h_wf : wfRegime R s)
    (_h_bounded : regimeBounded R) :
    consistentWithRegime predSat R ctx μ ρ θ := by
  rcases h_match with ⟨hctx_mem, hctx_vars, hctx_mem_hyg, hctx_vars_hyg_deep⟩
  have hctx_vars_hyg :
      ∀ x qt k, ctx.varEnv.lookup x = some qt → qtypGuardTag qt = some k →
        ¬ s.vars.hasKey x → k ∉ inputSpecTags s := by
    exact
      (deep_implies_shallow (P := fun env =>
        ∀ x qt k, env.lookup x = some qt → qtypGuardTag qt = some k →
          ¬ s.vars.hasKey x → k ∉ inputSpecTags s) (env := ctx.varEnv) hctx_vars_hyg_deep)
  simp only [consistentWithRegime]
  constructor
  · intro l qt k hlookup hguard hRdef
    -- From wfRegime: any tag interpreted by R must be a spec tag.
    have hk_in_tags : k ∈ inputSpecTags s := by
      have h_isSome : (R.lookup? k).isSome := by
        cases h : R.lookup? k with
        | none => exact False.elim (hRdef h)
        | some _b => simp
      exact h_wf.2.2 k h_isSome
    -- Tag hygiene in ctx forbids non-spec entries from reusing spec tags, so l must be a spec key.
    have hkey : s.locs.hasKey l := by
      by_contra hnot
      have : k ∉ inputSpecTags s := hctx_mem_hyg l qt k hlookup hguard hnot
      exact this hk_in_tags
    -- Recover the spec-qualified type at l and use the spec-indexed regime consistency.
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
        have hlookup_s' : s.locs.lookup l = some qt_s := by
          simpa [MemoryTypeEnv.lookup] using hlookup_s
        have hctx_lookup' : ctx.memEnv.lookup l = some qt_s := hctx_mem hlookup_s'
        have hqt : qt_s = qt := by
          have : some qt_s = some qt := by
            calc
              some qt_s = ctx.memEnv.lookup l := by
                symm
                exact hctx_lookup'
              _ = some qt := by
                exact hlookup
          exact Option.some.inj this
        have h_locs_forall := h_spec.1
        rw [List.forall_iff_forall_mem] at h_locs_forall
        have hmem' : (l, qt_s) ∈ s.locs.toList := by
          rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
          dsimp [MemoryTypeEnv.lookup] at hlookup_s'
          simpa using hlookup_s'
        have h_loc_regime : locsRegime predSat R μ θ (l, qt_s) :=
          h_locs_forall (l, qt_s) hmem'
        simpa [hqt] using h_loc_regime
  · intro x qt k hlookup hguard hRdef
    have hk_in_tags : k ∈ inputSpecTags s := by
      have h_isSome : (R.lookup? k).isSome := by
        cases h : R.lookup? k with
        | none => exact False.elim (hRdef h)
        | some _b => simp
      exact h_wf.2.2 k h_isSome
    have hkey : s.vars.hasKey x := by
      by_contra hnot
      have : k ∉ inputSpecTags s := hctx_vars_hyg x qt k hlookup hguard hnot
      exact this hk_in_tags
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
        have hlookup_s' : s.vars.lookup x = some qt_s := by
          simpa [VarTypeEnv.lookup] using hlookup_s
        have hctx_lookup' : ctx.varEnv.lookup x = some qt_s := hctx_vars hlookup_s'
        have hqt : qt_s = qt := by
          have : some qt_s = some qt := by
            calc
              some qt_s = ctx.varEnv.lookup x := by
                symm
                exact hctx_lookup'
              _ = some qt := by
                exact hlookup
          exact Option.some.inj this
        have h_vars_forall := h_spec.2
        rw [List.forall_iff_forall_mem] at h_vars_forall
        have hmem' : (x, qt_s) ∈ s.vars.toList := by
          rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
          dsimp [VarTypeEnv.lookup] at hlookup_s'
          simpa using hlookup_s'
        have h_var_regime : varsRegime predSat R μ ρ (x, qt_s) :=
          h_vars_forall (x, qt_s) hmem'
        simpa [hqt] using h_var_regime

-- Regime boundedness (imported from `FaultRobustness.lean`): tags at or above the initial
-- `nextTag` supply are outside the regime's domain (model faulty inputs only).
-- We restate it locally for convenience in this file.

-- Step theorem (context-driven, no input/output specs).
-- It assumes agreement on clean items in the initial context and preserves it
-- for the post-context, plus result agreement when the result is clean under R.
def StepFR
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat) : Prop :=
    PredSatLaws predSat →
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      regimeConsistentWithCtx ctx ctx.regime →
      regimeBounded ctx.regime →
      consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →
      consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
      agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } →  -- initial config₀ well-formed
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →  -- initial config₁ well-formed
        terminatesTo mode e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ →
        terminatesTo mode e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
        ∃ (θ₀' θ₁' : RealizationMap),
          wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
          wfTypeContext (ctxAfter ctx res) ∧
          wfConfig cf₀ ∧  -- final config₀ well-formed
          wfConfig cf₁ ∧  -- final config₁ well-formed
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧  -- preservation
          runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧  -- preservation
          regimeConsistentWithCtx (ctxAfter ctx res) ctx.regime ∧  -- regime consistency preserved
          consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
          consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
          agreeOnClean predSat ctx.regime (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
          resultAgreesIfClean predSat ctx.regime cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁

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
      StepFR mode ctxᵢ e res predSat


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
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
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
  | clean_ref _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩

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
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
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
  | clean_ref _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, _, hetyp⟩

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
      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ t ls, qt.etyp = ETyp.ref t ls := by
            intro ⟨t, ls, h⟩
            apply hnotref
            exact ⟨t, ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
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
      | clean_ref _hpoison2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
      | withPred_true_ref _k _htag _hregime hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.clean_ref hpoison (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
  | guard k htag hreg _ =>
      cases hagree with
      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
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
      | clean_ref _hpoison2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2
      | withPred_true_ref _k2 _htag2 _hregime2 hetyp1 hlookup1 hin hv1 hlookup2 hv2 =>
          exact agreeValueUnder.withPred_true_ref k htag hreg (hetyp.trans hetyp1) hlookup1 hin hv1 hlookup2 hv2

private lemma valueHasETyp_num_etyp {θ : RealizationMap} {n : Int} {t : ETyp} :
  valueHasETyp θ (Value.num n) t → t = ETyp.int := by
  intro h
  cases h
  rfl

private lemma typecheckDeref_etyp_int
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref ctx e fuel = .ok res → res.qualType.etyp = ETyp.int := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e fuel' with
      | error err =>
          simp [h_tc1] at h_typecheck
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt : result1.qualType with
          | mk etyp poisonRef predRef =>
              rw [h_qt] at h_typecheck
              simp at h_typecheck
              cases etyp <;> simp at h_typecheck
              -- only ref case can succeed
              rename_i t ls
              split at h_typecheck
              · -- t = ETyp.int (the only successful case)
                split at h_typecheck
                · -- ls.isEmpty - error case
                  contradiction
                · -- ls not empty - split on foldM result
                  split at h_typecheck
                  · -- foldM error case
                    contradiction
                  · -- foldM success case - now split on poisonRef
                    split at h_typecheck
                    · -- poisonRef = true
                      simp [pure, Except.pure] at h_typecheck
                      cases h_typecheck
                      rfl
                    · -- poisonRef = false - split on merged predicate
                      split at h_typecheck
                      · -- noPred case
                        simp [pure, Except.pure] at h_typecheck
                        cases h_typecheck
                        rfl
                      · -- guardOnly case (split on tag lookup)
                        split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · -- guardClosure case (split on tag lookup)
                        split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
              · -- t ≠ ETyp.int (error - contradiction)
                cases h_typecheck

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

-- Extract guard tag directly from a predicate (helper for deref foldM lemmas).
private def predGuardTag (p : Predicate) : Option Tag :=
  match p with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

-- fold function used by typecheckDeref (exposed for local reasoning)
private def derefFoldF (mem : MemoryTypeEnv) (acc : Bool × Option Predicate) (l : Loc) :
    Except String (Bool × Option Predicate) :=
  match mem[l]? with
  | some qt =>
      if qt.etyp = ETyp.int then
        Except.ok
          (joinPoison acc.1 qt.poison,
            match acc.2 with
            | none => some qt.pred
            | some p => some (joinPredicates p qt.pred))
      else
        throw
          (toString "Type mismatch in dereference at " ++ toString l ++ toString ": " ++
            toString (repr qt.etyp) ++ toString " ≠ int")
  | none =>
      throw
        (toString "Location " ++ toString l ++ toString " not found in memory environment")

private lemma predGuardTag_joinPredicates {p q : Predicate} {k : Tag} :
    predGuardTag (joinPredicates p q) = some k →
    predGuardTag p = some k ∧ predGuardTag q = some k := by
  cases p with
  | guardClosure k1 a1 b1 env1 =>
      cases q with
      | guardClosure k2 a2 b2 env2 =>
          intro h
          by_cases hbeq :
              beqPredicate (Predicate.guardClosure k1 a1 b1 env1)
                (Predicate.guardClosure k2 a2 b2 env2) = true
          · have hpq :
              Predicate.guardClosure k1 a1 b1 env1 = Predicate.guardClosure k2 a2 b2 env2 := by
              exact eq_of_beq (a := Predicate.guardClosure k1 a1 b1 env1)
                (b := Predicate.guardClosure k2 a2 b2 env2) hbeq
            cases hpq
            have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, hbeq] using h
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk1]⟩
          · by_cases htag : (k1 == k2) = true
            · have hk1 : k1 = k := by
                simpa [joinPredicates, predGuardTag, hbeq, htag] using h
              have hk12 : k1 = k2 := of_decide_eq_true htag
              have hk2 : k2 = k := by
                calc
                  k2 = k1 := hk12.symm
                  _ = k := hk1
              exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
            · simp [joinPredicates, predGuardTag, hbeq, htag] at h
      | guardOnly k2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
  | guardOnly k1 =>
      cases q with
      | guardClosure k2 a2 b2 env2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | guardOnly k2 =>
          intro h
          by_cases htag : (k1 == k2) = true
          · have hk1 : k1 = k := by
              simpa [joinPredicates, predGuardTag, beqPredicate, htag] using h
            have hk12 : k1 = k2 := of_decide_eq_true htag
            have hk2 : k2 = k := by
              calc
                k2 = k1 := hk12.symm
                _ = k := hk1
            exact ⟨by simp [predGuardTag, hk1], by simp [predGuardTag, hk2]⟩
          · simp [joinPredicates, predGuardTag, beqPredicate, htag] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
  | noPred =>
      cases q with
      | guardClosure _ _ _ _ =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
      | guardOnly _ =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h
      | noPred =>
          intro h
          simp [joinPredicates, predGuardTag, beqPredicate] at h

-- If foldlM returns joined poison = false, then the accumulator poison is false.
private lemma list_foldlM_derefFoldF_acc_false
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    joined = false →
    acc.1 = false := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold hjoin
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      simpa using hjoin
  | cons x xs ih =>
      intro acc joined pred? hfold hjoin
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- unfold derefFoldF to relate acc'.1 to acc.1
          cases hlookup : mem[x]? with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              by_cases h_etyp : qt.etyp = ETyp.int
              · simp [derefFoldF, hlookup, h_etyp] at hfx
                have hacc'_fst : acc'.1 = joinPoison acc.1 qt.poison := by
                  simpa using (congrArg Prod.fst hfx).symm
                -- apply IH on the tail to get acc'.1 = false
                have hacc'_false : acc'.1 = false := ih acc' joined pred? hfold hjoin
                -- now acc.1 must be false
                have hjoin' : joinPoison acc.1 qt.poison = false := by
                  simpa [hacc'_fst] using hacc'_false
                exact (joinPoison_eq_false hjoin').1
              · simp [derefFoldF, hlookup, h_etyp] at hfx

-- If foldlM returns joined poison = false, then every referenced cell is unpoisoned.
private lemma list_foldlM_derefFoldF_poison_false
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    joined = false →
    ∀ l ∈ xs, ∃ qt, mem[l]? = some qt ∧ qt.etyp = ETyp.int ∧ qt.poison = false := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold _hjoin l hl
      cases hl
  | cons x xs ih =>
      intro acc joined pred? hfold hjoin l hl
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- extract the head cell from hfx
          cases hlookup : mem[x]? with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              by_cases h_etyp : qt.etyp = ETyp.int
              · simp [derefFoldF, hlookup, h_etyp] at hfx
                -- acc' now is the expected pair
                have hacc' : acc'.1 = joinPoison acc.1 qt.poison := by
                  simpa using (congrArg Prod.fst hfx).symm
                -- Since final joined = false, the accumulator into the tail must be false.
                have hacc'_false : acc'.1 = false :=
                  list_foldlM_derefFoldF_acc_false mem xs acc' joined pred? hfold hjoin
                have hpoison_head : qt.poison = false := by
                  -- joinPoison acc.1 qt.poison = acc'.1 = false
                  have hjoin' : joinPoison acc.1 qt.poison = false := by simpa [hacc'] using hacc'_false
                  exact (joinPoison_eq_false hjoin').2
                rcases (List.mem_cons.mp hl) with rfl | hltail
                · exact ⟨qt, hlookup, h_etyp, hpoison_head⟩
                · -- apply IH to the tail
                  exact ih acc' joined pred? hfold hjoin l hltail
              · simp [derefFoldF, hlookup, h_etyp] at hfx

-- If foldlM succeeds, then every referenced cell has type int.
private lemma list_foldlM_derefFoldF_etyp_int
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    ∀ l ∈ xs, ∃ qt, mem[l]? = some qt ∧ qt.etyp = ETyp.int := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? hfold l hl
      cases hl
  | cons x xs ih =>
      intro acc joined pred? hfold l hl
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : mem[x]? with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              by_cases h_etyp : qt.etyp = ETyp.int
              · simp [derefFoldF, hlookup, h_etyp] at hfx
                rcases (List.mem_cons.mp hl) with rfl | hltail
                · exact ⟨qt, hlookup, h_etyp⟩
                · exact ih acc' joined pred? hfold l hltail
              · simp [derefFoldF, hlookup, h_etyp] at hfx

-- If foldlM returns a guard tag k, then every referenced cell predicate has tag k.
private lemma list_foldlM_derefFoldF_guardTag
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate) (k : Tag),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    predGuardTag (pred?.getD Predicate.noPred) = some k →
    (predGuardTag (acc.2.getD Predicate.noPred) = some k ∨ acc.2 = none) ∧
    (∀ l ∈ xs, ∃ qt, mem[l]? = some qt ∧ predGuardTag qt.pred = some k) := by
  intro xs
  induction xs with
  | nil =>
      intro acc joined pred? k hfold hguard
      simp [List.foldlM, pure, Except.pure] at hfold
      cases hfold
      constructor
      · left
        simpa using hguard
      · intro l hl; cases hl
  | cons x xs ih =>
      intro acc joined pred? k hfold hguard
      simp [List.foldlM, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem acc x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- extract head cell info
          cases hlookup : mem[x]? with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              by_cases h_etyp : qt.etyp = ETyp.int
              · simp [derefFoldF, hlookup, h_etyp] at hfx
                have hacc'_snd :
                    acc'.2 =
                      match acc.2 with
                      | none => some qt.pred
                      | some p => some (joinPredicates p qt.pred) := by
                  simpa using (congrArg Prod.snd hfx).symm
                -- apply IH to tail
                have ih' := ih acc' joined pred? k hfold hguard
                rcases ih' with ⟨hacc'_tag, htail⟩
                have hhead_tag : predGuardTag qt.pred = some k := by
                  -- acc'.2 is some predHead by construction
                  -- Use hacc'_tag to derive head tag
                  cases hacc : acc.2 with
                  | none =>
                      have hacc'_snd' : acc'.2 = some qt.pred := by
                        simpa [hacc] using hacc'_snd
                      -- acc'.2 = some qt.pred
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                            simp [hacc'_snd'] at hnone
                      simpa [hacc'_snd'] using hk
                  | some p =>
                      have hacc'_snd' : acc'.2 = some (joinPredicates p qt.pred) := by
                        simpa [hacc] using hacc'_snd
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                           simp [hacc'_snd'] at hnone
                      -- unfold acc'.2 and use joinPredicates lemma
                      have hpred : predGuardTag (joinPredicates p qt.pred) = some k := by
                        simpa [hacc'_snd'] using hk
                      exact (predGuardTag_joinPredicates hpred).2
                constructor
                · -- propagate tag to accumulator (or none)
                  cases hacc : acc.2 with
                  | none =>
                      right; rfl
                  | some p =>
                      -- acc'.2 = joinPredicates p qt.pred, so tag on acc'.2 gives tag on p
                      have hacc'_snd' : acc'.2 = some (joinPredicates p qt.pred) := by
                        simpa [hacc] using hacc'_snd
                      have hk : predGuardTag (acc'.2.getD Predicate.noPred) = some k := by
                        cases hacc'_tag with
                        | inl hk => exact hk
                        | inr hnone =>
                            simp [hacc'_snd'] at hnone
                      have hpred : predGuardTag (joinPredicates p qt.pred) = some k := by
                        simpa [hacc'_snd'] using hk
                      left
                      exact (predGuardTag_joinPredicates hpred).1
                · -- all elements: head + tail
                  intro l hl
                  rcases (List.mem_cons.mp hl) with rfl | hltail
                  · exact ⟨qt, hlookup, hhead_tag⟩
                  · exact htail l hltail
              · simp [derefFoldF, hlookup, h_etyp] at hfx

private lemma deref_foldM_poison_false
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hjoin : joined = false) (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem[l]? = some qt ∧ qt.etyp = ETyp.int ∧ qt.poison = false := by
  -- Convert to list fold and apply list lemma
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    -- lemma in Std.ExtTreeSet.Lemmas
    simpa using hl
  exact list_foldlM_derefFoldF_poison_false mem ls.toList (false, none) joined pred? hfold hjoin l hl'

private lemma deref_foldM_guardTag
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate) (k : Tag)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hguard : predGuardTag (pred?.getD Predicate.noPred) = some k)
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem[l]? = some qt ∧ predGuardTag qt.pred = some k := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  have haux :=
    list_foldlM_derefFoldF_guardTag mem ls.toList (false, none) joined pred? k hfold hguard
  exact (haux.2 l hl')

private lemma deref_foldM_etyp_int
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem[l]? = some qt ∧ qt.etyp = ETyp.int := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact list_foldlM_derefFoldF_etyp_int mem ls.toList (false, none) joined pred? hfold l hl'

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
  rcases hctx with ⟨hctx_mem, hctx_vars, _, _⟩
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
  intro mode μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstep mode e ctx predSat
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hR hRbound hregBounded hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R := ctx.regime with hRdef
  -- Use bridge lemma to derive consistentWithRegime from consistentRegimeSpec
  have hcwr₁ : consistentWithRegime predSat R ctx μ₁ ρ₁ θ₁ := by
    have hcrs₁' : consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ := by
      simpa [hRdef] using hcrs₁
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₁ ρ₁ θ₁ hcrs₁' hctx hRbound' hregBounded'
  have hcwr₂ : consistentWithRegime predSat R ctx μ₂ ρ₂ θ₂ := by
    have hcrs₂' : consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ := by
      simpa [hRdef] using hcrs₂
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₂ ρ₂ θ₂ hcrs₂' hctx hRbound' hregBounded'
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
    exact Nat.le_of_eq hR
  have hstepFR :=
    hstep' _hps μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ _hwf hric₁ hric₂ hreg hregBounded hcwr₁ hcwr₂ hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  rcases hstepFR with ⟨θ₁', θ₂', hθ₁ext, hθ₂ext, _hwf', _hwfcf₁', _hwfcf₂', _hric₁', _hric₂', _hreg', _hcwr₁', _hcwr₂', hagree_clean', hret_agree⟩
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
          | clean_eq_nonref_nonarrow _ _ _ hval =>
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
          | clean_ref _ _ _ _ hv1 _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ _ hval =>
              cases hval
              rfl
          | withPred_true_ref _ _ _ _ _ _ hv1 _ _ =>
              cases hv1
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
            | @clean_ref _t _ls l a₁ a₂ _qt _v₁ _v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁, ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂, ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k _t _ls l a₁ a₂ _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁, ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂, ?_⟩
                  exact And.intro hlookup2 hv2
            | clean_eq_nonref_nonarrow _ _ hnotref _ =>
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
      (clean_eq_nonref_nonarrow := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hagree)
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
        intro t ls l a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k t ls l a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
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
      (clean_eq_nonref_nonarrow := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hagree)
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
        intro t ls l a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k t ls l a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
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

private lemma typecheckVar_preserves_regime (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.regime' = ctx.regime := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck
  · repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · simp at h_typecheck

-- Transfer consistentWithRegime using monotoneStep
-- When Regime.monotoneStep R R', if consistentWithRegime holds for R, it holds for R'
-- (R' has fewer entries, so fewer constraints need to be checked)
private lemma consistentWithRegime_monotone
    (predSat : PredSat) (R R' : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (h_mono : Regime.monotoneStep R R')
    (h_cwr : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R' ctx μ ρ θ := by
  simp only [consistentWithRegime] at h_cwr ⊢
  constructor
  · -- Location regime consistency
    intro l qt k hlookup hguard hR'def
    -- R'.lookup? k ≠ none means R'.lookup? k = some b for some b
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        -- By monotoneStep.no_new_entries, R.lookup? k ≠ none since R'.lookup? k ≠ none
        have hRdef : R.lookup? k ≠ none := h_mono.2.2 k hR'def
        -- Get R.lookup? k = some b' for some b'
        cases hk : R.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            -- By monotoneStep.entries_preserved: R.lookup? k = some b' → R'.lookup? k = some b' ∨ R'.lookup? k = none
            have h := h_mono.2.1 k b' hk
            cases h with
            | inl h_eq =>
                -- R'.lookup? k = some b', and we have hk' : R'.lookup? k = some b
                -- So b = b', meaning hk : R.lookup? k = some b
                have hb_eq : b' = b := by
                  have : some b' = some b := h_eq.symm.trans hk'
                  exact Option.some.inj this
                have hk_b : R.lookup? k = some b := by rw [← hb_eq]; exact hk
                have h_locsR := h_cwr.1 l qt k hlookup hguard hRdef
                exact locsRegime_monotone h_mono hguard hk_b hk' h_locsR
            | inr h_none =>
                -- R'.lookup? k = none contradicts hk' : R'.lookup? k = some b
                simp [h_none] at hk'
  · -- Variable regime consistency (similar)
    intro x qt k hlookup hguard hR'def
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        have hRdef : R.lookup? k ≠ none := h_mono.2.2 k hR'def
        cases hk : R.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h := h_mono.2.1 k b' hk
            cases h with
            | inl h_eq =>
                have hb_eq : b' = b := by
                  have : some b' = some b := h_eq.symm.trans hk'
                  exact Option.some.inj this
                have hk_b : R.lookup? k = some b := by rw [← hb_eq]; exact hk
                have h_varsR := h_cwr.2 x qt k hlookup hguard hRdef
                exact varsRegime_monotone h_mono hguard hk_b hk' h_varsR
            | inr h_none =>
                simp [h_none] at hk'

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
    ∀ (res : TypeResult), typecheck ctxᵢ e m = .ok res → StepFR .ioFree ctxᵢ e res predSat

private lemma stepFR_literal
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext) (predSat : PredSat)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hpoison : res.qualType.poison = false)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hnotref : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFR mode ctx e res predSat := by
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
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
  --   regimeConsistentWithCtx ... ∧ consistentWithRegime ... ∧ consistentWithRegime ... ∧
  --   agreeOnClean ... ∧ resultAgreesIfClean ...
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- consistentWithRegime for run 0
    simpa [hctxAfter] using hcwr₀
  · -- consistentWithRegime for run 1
    simpa [hctxAfter] using hcwr₁
  · -- agreeOnClean for updated context (literal doesn't change context)
    simpa [hctxAfter] using hagree
  · -- resultAgreesIfClean
    intro _hclean
    have hval' : o₀ = o₁ := by
      simp [ho₀, ho₁]
    exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hval'

private lemma stepFR_var
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.var name) res predSat := by
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have htagR : tagEnvConsistentWithRegime ctxᵢ.tagEnv ctxᵢ.regime := hreg.1
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
  have hregime' : res.regime' = ctxᵢ.regime :=
    typecheckVar_preserves_regime ctxᵢ name res htc'
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- consistentWithRegime for run 0 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using hcwr₀
  · -- consistentWithRegime for run 1 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using hcwr₁
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
            qtypCleanUnder ctxᵢ.regime qt →
            agreeVarUnder predSat ctxᵢ.regime μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (name, qt) := by
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
            have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
              exact qtypCleanUnder.clean hpoison
            have hvar := hvar_agree_of_clean hclean_qt
            have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
              agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
            have hres_eq : res.qualType = qt := by
              cases qt with
              | mk etyp poison pred =>
                  cases hpred
                  simp [hres, hpc, joinPoison]
            have hres_agree :
                agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
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
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_eq : res.qualType = qt := by
                      cases qt with
                      | mk etyp poison pred =>
                          cases hpred
                          simp [hres, hpc, joinPoison]
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      simpa [hres_eq] using hval
                    simpa [hlookup₀, hlookup₁] using hres_agree
                | guard k' htag' hregime hnotfun_res =>
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      have hnotfun_qt : qt.etyp.isFunctionType = false := by
                        simpa [hres] using hnotfun_res
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
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
                        | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                            have htagRes : qtypGuardTag res.qualType = some k := by
                              simp [qtypGuardTag, hres, hpred]
                            have hetyp' : res.qualType.etyp = qt.etyp := by
                              simp [hres]
                            exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                              hlookup1 hin hv1 hlookup2 hv2
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
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
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
                        have hregime : ctxᵢ.regime.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          have hnotfun_qt : qt.etyp.isFunctionType = false := by
                            sorry  -- TODO: derive from context or add constraint
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow (by simp [hres, hpc]) hnotfun' hnotref' hEq
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
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
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
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
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
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      have hnotfun_qt : qt.etyp.isFunctionType = false := by
                        simpa [hres] using hnotfun_res
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                            intro ⟨t, ls, h⟩
                            apply hnotref
                            exact ⟨t, ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
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
                      | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
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
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
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
                        have hregime : ctxᵢ.regime.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          have hnotfun_qt : qt.etyp.isFunctionType = false := by
                            sorry  -- TODO: derive from context or add constraint
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
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
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
                                intro ⟨t, ls, h⟩
                                apply hnotref
                                exact ⟨t, ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
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
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.op e1 op e2) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckOp ctxᵢ e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime,
          h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctxᵢ e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext :=
    { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ res1 htc1'
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res2 htc2'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for binary op
  have hstruct₀ := terminatesTo_op_inv' e1 op e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, v₀2, ht₀_e1, ht₀_e2, h_evalop₀, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_op_inv' e1 op e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, v₁2, ht₁_e1, ht₁_e2, h_evalop₁, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, hres_agree1⟩
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
  -- Use regime_monotone to establish consistency with ctx'.regime = res1.regime'
  have h_mono := regime_monotone ctxᵢ res1
  have htagR_input : regimeConsistentWithCtx ctxᵢ ctxᵢ.regime := htagR
  have htagR1' : regimeConsistentWithCtx ctx' ctx'.regime := by
    have h := regimeConsistentWithCtx_of_typecheckResult ctxᵢ e1 fuel' res1 htagR_input h_mono htc1'
    simpa [ctx', ctxAfter] using h
  -- agreeOnClean from IH1 uses ctxᵢ.regime (input), need to transfer to ctx'.regime
  -- For now, use monotonicity-based transfer (smaller regime is more permissive)
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    -- agreeOnClean for smaller regime (ctx'.regime = res1.regime') follows from larger regime (ctxᵢ.regime)
    -- via monotonicity: fewer tags to check means fewer constraints
    sorry
  -- consistentWithRegime from IH1 uses (ctxAfter ctxᵢ res1).regime = res1.regime' = ctx'.regime
  -- So hcwr₀1 and hcwr₁1 directly give what we need
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hcwr₁1
  -- regimeBounded transfers via monotonicity (bounds are equal)
  have hRbound' : regimeBounded ctx'.regime := by
    have hctx'_regime : ctx'.regime = res1.regime' := by simp [ctx']
    rw [hctx'_regime]
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound h_mono
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
    hIH2 hpredlaws cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ v₀2 v₁2
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag, h_regime]
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    -- IH2 gives agreeOnClean predSat ctx'.regime ..., need to transfer to ctxᵢ.regime
    -- Since ctx'.regime = res1.regime' ⊆ ctxᵢ.regime (monotone), and agreeOnClean checks
    -- fewer tags for smaller regime, we need monotonicity lemma.
    sorry
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    -- Need to show regimeConsistentWithCtx for input regime ctxᵢ.regime
    -- htagR2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) ctx'.regime
    -- Use monotonicity: ctx'.regime ⊆ ctxᵢ.regime
    sorry
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
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
  -- hres_agree1 uses ctxᵢ.regime (from IH1)
  have hclean1 : qtypCleanUnder ctxᵢ.regime res1.qualType := qtypCleanUnder.clean hjoin_12.1
  -- hres_agree2 uses ctx'.regime (from IH2) - but since poison = false, regime doesn't matter
  have hclean2 : qtypCleanUnder ctx'.regime res2.qualType := qtypCleanUnder.clean hjoin_12.2
  have hagree_v1 :
      agreeValueUnder predSat ctxᵢ.regime cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 :=
    hres_agree1 hclean1
  have hagree_v2 :
      agreeValueUnder predSat ctx'.regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType v₀2 v₁2 :=
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
  exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq

-- World-free version of stepFRW_unaryop
private lemma stepFR_unaryop
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (op : UnaryOp) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.unaryop op e) res predSat := by
  have htc' : typecheckUnaryOp ctxᵢ op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctxᵢ op e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ res1 htc1'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for unaryop
  have hstruct₀ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', v₀', ht₀_e, h_evalop₀, hmem₀, hvar₀, _hnext₀, _hpure₀⟩
  have hstruct₁ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', v₁', ht₁_e, h_evalop₁, hmem₁, hvar₁, _hnext₁, _hpure₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e, hres_agree_e⟩
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime]
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    simpa [hctxAfter] using hreg'
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hcwr₀'
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hcwr₁'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
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
  have hclean1 : qtypCleanUnder ctxᵢ.regime res1.qualType := by
    exact qtypCleanUnder.clean hres1_poison
  have hagree_v :
      agreeValueUnder predSat ctxᵢ.regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType v₀' v₁' :=
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
  exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq

-- World-free version of stepFRW_newRef
private lemma stepFR_newRef
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.newRef e) res predSat := by
  -- Parse typecheck result
  have htc' : typecheckNewRef ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, l, htc1, hl, h_etyp1, h_etyp, h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ res1 htc1'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for newRef
  have hstruct₀ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', n₀, ht₀_e, ho₀, hmem₀, hnext₀, hvar₀, hpm₀⟩
  have hstruct₁ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', n₁, ht₁_e, ho₁, hmem₁, hnext₁, hvar₁, hpm₁⟩
  -- Apply IH for e
  have hstep_e :=
    hIH hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.num n₀) (Value.num n₁)
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean_e, hres_agree_e⟩
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
    · have hmem : l' ∈ updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩ :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have h_isSome : ((updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, res1.qualType.pred⟩)[l']?).isSome = true :=
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
  have hreg' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    simpa [regimeConsistentWithCtx, ctxAfter, h_tag, h_ntag] using htagR1
  -- Prove agreeOnClean
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' :=
    agreeOnClean_newRef_extend
      predSat ctxᵢ.regime ctxᵢ res1 res l ETyp.int
      cfg₀' cfg₁' cf₀ cf₁ n₀ n₁ cfg₀'.nextAddr cfg₁'.nextAddr θ₀1 θ₁1 θ₀' θ₁'
      h_mem h_etyp1 rfl rfl hmem₀ hmem₁ hvar₀ hvar₁ rfl rfl
      hθext₀' hθext₁' hwfcf₀1 hwfcf₁1 hagree_clean_e hres_agree_e
  -- Derive wfConfig for final configs
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  -- consistentWithRegime for extended realization maps
  -- Fresh location l gets a fresh address, regime doesn't constrain it (tag for l comes from res1, not in regime)
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    sorry -- TODO: Prove consistentWithRegime preserved for newRef (fresh loc outside regime)
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    sorry -- TODO: Prove consistentWithRegime preserved for newRef (fresh loc outside regime)
  refine ⟨θ₀', θ₁', ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀', hric₁', hreg', hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
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
    exact agreeValueUnder.clean_ref hpoison_res h_etyp hlookup1 hin1 ho₀ hlookup2 ho₁

-- World-free version of stepFRW_seq
private lemma stepFR_seq
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.seq e1 e2) res predSat := by
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
    e1 ctxᵢ res1 htc1'
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res htc2'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for seq
  have hstruct₀ := terminatesTo_seq_inv' e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, ht₀_e1, ht₀_e2, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_seq_inv' e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, ht₁_e1, ht₁_e2, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, hres_agree1⟩
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
  have htagR1' : regimeConsistentWithCtx ctx' ctx'.regime := by
    sorry -- TODO: Update for regime threading
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    sorry -- TODO: Prove consistentWithRegime for intermediate context
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    sorry -- TODO: Prove consistentWithRegime for intermediate context
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    sorry -- TODO: Update for regime threading
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
  -- Note: ctx'.regime = res1.regime' which may differ from ctxᵢ.regime
  -- For now, we need regime monotonicity to relate them
  have hregime_eq : ctx'.regime = ctxᵢ.regime := by
    simp only [hctx', updateCtxFromResult]
    sorry -- TODO: Requires regime monotonicity - res1.regime' = ctxᵢ.regime
  have hRbound' : regimeBounded ctx'.regime := by simpa [hregime_eq] using hRbound
  have hstep_e2 :=
    hIH2 hpredlaws cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter, hregime_eq] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    sorry -- TODO: Update for regime monotonicity
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    sorry -- TODO: Prove consistentWithRegime preservation
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    sorry -- TODO: Prove consistentWithRegime preservation
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
  · simpa [hctxAfter] using hwf2
  -- Since res is directly the result of e2, hres_agree2 gives us the result directly
  simpa [hregime_eq] using hres_agree2

-- World-free version of stepFRW_vlet
private lemma stepFR_vlet
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.vlet vname e1 e2) res predSat := by
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
    e1 ctxᵢ res1 htc1'
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' res2 htc2'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
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
    hIH1 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, hres_agree1⟩
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
  have hreg_ctx' : regimeConsistentWithCtx ctx' ctx'.regime := by
    -- ctx'.regime = res1.regime', need to derive from htagR1 and regime_monotone
    unfold regimeConsistentWithCtx at htagR1 ⊢
    constructor
    · -- tagEnvConsistentWithRegime ctx'.tagEnv ctx'.regime
      simp only [hctx']
      have hctxAfter_tagEnv : (ctxAfter ctxᵢ res1).tagEnv = res1.tagEnv' := by simp [ctxAfter]
      rw [← hctxAfter_tagEnv]
      -- htagR1.1 : tagEnvConsistentWithRegime (ctxAfter ctxᵢ res1).tagEnv ctxᵢ.regime
      -- Need to show for res1.regime' which is a subset of ctxᵢ.regime
      -- This follows from monotonicity: smaller regime has fewer constraints
      sorry
    · -- res1.regime'.bound ≤ ctx'.nextTag
      simp only [hctx']
      have hbound_eq : res1.regime'.bound = ctxᵢ.regime.bound := (regime_monotone ctxᵢ res1).1
      have hctxAfter_nextTag : (ctxAfter ctxᵢ res1).nextTag = res1.nextTag' := by simp [ctxAfter]
      rw [hbound_eq, ← hctxAfter_nextTag]
      exact htagR1.2
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
  -- ctx'.regime = res1.regime' (not ctxᵢ.regime), need monotonicity transfer
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    -- TODO: Properly implement using agreeOnClean_monotone
    -- The key insight is that for smaller regime (res1.regime' ⊆ ctxᵢ.regime),
    -- agreeOnClean is preserved because fewer tags need to be checked
    sorry
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
  -- ctx'.regime = res1.regime' (from hctx'), use regime_monotone for properties
  have h_mono_vlet := regime_monotone ctxᵢ res1
  have hRbound_ctx' : regimeBounded ctx'.regime := by
    have h : ctx'.regime = res1.regime' := by simp [hctx']
    rw [h]
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound h_mono_vlet
  -- Transfer consistentWithRegime from IH1 result to ctx'
  -- IH1 gives consistentWithRegime predSat (ctxAfter ctxᵢ res1).regime (ctxAfter ctxᵢ res1) ...
  -- Since ctx' = ctxAfter ctxᵢ res1 (structurally), these match
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
    -- cfg₀2 extends cfg₀1 with updated varEnv
    sorry -- TODO: Transfer from hcwr₀1 using ctx' structure
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    sorry -- TODO: Transfer from hcwr₁1 using ctx' structure
  have hstep_e2 :=
    hIH2 hpredlaws cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀1 θ₁1
      cfg₀3 cfg₁3 o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' hreg_ctx' hRbound_ctx' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcf₀3, hwfcf₁3, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, hres_agree2⟩
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
  -- ctx'.regime = res1.regime' (not ctxᵢ.regime)
  have hreg'' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    -- IH2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) ctx'.regime
    -- Need to transfer to ctxᵢ.regime using monotonicity
    sorry -- TODO: Use regime monotonicity
  -- Final agreeOnClean
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    -- IH2 gives agreeOnClean predSat ctx'.regime ..., need to transfer to ctxᵢ.regime
    sorry -- TODO: Use regime monotonicity to transfer from smaller to larger regime
  -- Final wfConfig
  have hwfcf₀_final : wfConfig cf₀ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
  -- Need consistentWithRegime for both runs
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    sorry -- TODO: Derive from hcwr₀2 with context/regime equality
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    sorry -- TODO: Derive from hcwr₁2 with context/regime equality
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, hwfcf₀_final, hwfcf₁_final, hric₀'', hric₁'', hreg'', hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
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
    have hclean2 : qtypCleanUnder ctxᵢ.regime res2.qualType := by
      cases hclean with
      | clean hpoison_res => exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k htag hreg hnotfun =>
          have htag' : qtypGuardTag res2.qualType = some k := by
            simpa [qtypGuardTag, h_ret_pred] using htag
          have hnotfun' : res2.qualType.etyp.isFunctionType = false := by
            simpa [h_ret_etyp] using hnotfun
          exact qtypCleanUnder.guard k htag' hreg hnotfun'
    have hagree2 : agreeValueUnder predSat ctxᵢ.regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      -- ctx'.regime = res1.regime' (not ctxᵢ.regime), need to handle regime mismatch
      -- hres_agree2 expects qtypCleanUnder ctx'.regime, but hclean2 uses ctxᵢ.regime
      -- For clean case (poison = false), regime doesn't matter
      have hclean2' : qtypCleanUnder ctx'.regime res2.qualType := by
        cases hclean2 with
        | clean hp => exact qtypCleanUnder.clean hp
        | guard k htag hreg _ =>
            -- For guard case, need to check if k is in ctx'.regime
            sorry -- TODO: Handle regime transfer for guard case
      have hagree2_ctx' := hres_agree2 hclean2'
      -- Transfer from ctx'.regime to ctxᵢ.regime
      sorry -- TODO: Transfer agreeValueUnder between regimes
    exact agreeValueUnder_transport_clean hclean h_ret_etyp h_ret_pred hpoison_imp hagree2

-- World-free version of stepFRW_fn
private lemma stepFR_fn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.fn x paramType body returnType) res predSat := by
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
    regime' := ctxᵢ.regime
  }
  have hres : res = res_expected := by
    have htc' := htcFn
    simp [typecheckFn] at htc'
    cases htc'
    rfl
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter, hres, res_expected]
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma
  have ⟨hcf₀, ho₀⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hcap :
      agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
    agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- consistentWithRegime for run 0 (fn doesn't change context)
    simpa [hctxAfter] using hcwr₀
  · -- consistentWithRegime for run 1 (fn doesn't change context)
    simpa [hctxAfter] using hcwr₁
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

-- World-free version of stepFRW_pfn
private lemma stepFR_pfn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.pfn x paramType body returnType) res predSat := by
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
        regime' := ctxᵢ.regime
      }
      have hres : res = res_expected := by
        have htc' := htcPfn
        simp [typecheckPfn, hbody] at htc'
        cases htc'
        rfl
      have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
        simp [ctxAfter, hres, res_expected]
      intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
      -- Use world-free inversion lemma
      have ⟨hcf₀, ho₀⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
      have ⟨hcf₁, ho₁⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
      subst hcf₀ hcf₁
      have hcap :
          agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
        agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      refine ⟨θ₀, θ₁, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · -- consistentWithRegime for run 0 (pfn doesn't change context)
        simpa [hctxAfter] using hcwr₀
      · -- consistentWithRegime for run 1 (pfn doesn't change context)
        simpa [hctxAfter] using hcwr₁
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

-- World-free version of ite fault-robustness
-- Key insight: if condition is clean, both runs take same branch
-- TODO: This proof needs to be updated to handle the regime-aware typecheckIf structure
private lemma stepFR_ite
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat := by
  sorry


-- Stub lemma for assignment (not yet proven)
private lemma stepFR_assign
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.assign e1 e2) res predSat := by
  sorry

-- World-free version of stepFRW_deref (simplified with sorry)
private lemma stepFR_deref
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.deref e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.deref e) res predSat := by
  classical
  -- Parse typecheck result
  have htc' : typecheckDeref ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag⟩ :=
    typecheckDeref_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctxᵢ e fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ res1 htc1'
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert deref evaluation (world-free)
  have hstruct₀ := terminatesTo_deref_inv' e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀', a₀', n₀, ht₀_e, hlookup₀, hv₀, hmem₀, hvar₀, hnext₀, hpm₀, hpm_e₀⟩
  have hstruct₁ := terminatesTo_deref_inv' e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁', a₁', n₁, ht₁_e, hlookup₁, hv₁, hmem₁, hvar₁, hnext₁, hpm₁, hpm_e₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.loc a₀') (Value.loc a₁')
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, hwf', hwfcfg₀', hwfcfg₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e_and_res⟩
  have hagree_clean_e := hagree_clean_e_and_res.1
  have hres_agree_e := hagree_clean_e_and_res.2
  -- Post-context is unchanged by deref (only result type changes)
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    sorry -- TODO: Prove context equality including regime'
  have hagree_clean :
      agreeOnClean predSat ctxᵢ.regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) ctxᵢ.regime := by
    simpa [hctxAfter] using hreg'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.deref e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.deref e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    sorry -- TODO: Prove consistentWithRegime preservation
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    sorry -- TODO: Prove consistentWithRegime preservation
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_⟩
  · simpa [hctxAfter] using hwf'
  -- Result agreement when clean: deref reads from a clean location
  intro hclean
  -- We need to show o₀ = o₁ (both are ints from the same logical location)
  -- First, show the argument type is ref int
  have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ETyp.int ls := by
    have htc'' := htc'
    simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        cases etyp <;> simp [hq] at htc''
        rename_i t ls
        by_cases ht : t = ETyp.int
        · subst ht; exact ⟨ls, rfl⟩
        · have : False := by simp [ht] at htc''
          exact (False.elim this)
  -- The reference itself must be unpoisoned if the deref result is clean
  have hres1_poison_false : res1.qualType.poison = false := by
    by_contra hbad
    rcases hres1_etyp with ⟨ls, hres1_etyp⟩
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        -- simplify typecheckDeref under poisonRef = true
        have h_etyp : etyp = ETyp.ref ETyp.int ls := by
          simpa [hq] using hres1_etyp
        have hpoison : poison = true := by
          cases poison
          · simp [hq] at hbad
          · rfl
        have htc'' := htc'
        simp [typecheckDeref, htc1_expr, hq, h_etyp, hpoison, bind, Except.bind, pure, Except.pure] at htc''
        by_cases hls : ls = ∅
        · -- Empty locset: typecheck would error, contradict success
          simp [hls] at htc''
        · -- ls ≠ ∅, so the deref branch returns poisoned result with noPred
          simp [hls] at htc''
          -- Case split on the foldM over locations via the outer match in htc''
          split at htc''
          · -- foldM error case
            cases htc''
          · -- foldM ok case
            rename_i v
            cases htc''
            cases hclean with
            | clean hpoison =>
                -- contradiction: clean requires poison = false
                simp at hpoison
            | guard k htag _ _ =>
                -- contradiction: guard tag absent when pred = noPred
                simp [qtypGuardTag] at htag
  have hres1_clean : qtypCleanUnder ctxᵢ.regime res1.qualType :=
    qtypCleanUnder.clean hres1_poison_false
  have hagree_ref :
      agreeValueUnder predSat ctxᵢ.regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType (Value.loc a₀') (Value.loc a₁') :=
    hres_agree_e hres1_clean
  -- Extract the logical location l from reference agreement
  rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
  have ⟨l, hθ₀l, hθ₁l, hlin⟩ :
      ∃ l, θ₀'.lookup l = some a₀' ∧ θ₁'.lookup l = some a₁' ∧ l ∈ ls0 := by
    cases hagree_ref with
    | @clean_ref t ls l a1 a2 qt v1 v2 _hetyp_poison hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have : ETyp.ref t ls = ETyp.ref ETyp.int ls0 := by
          calc
            ETyp.ref t ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ETyp.int ls0 := hres1_etyp0
        cases this
        -- Align addresses using hv1/hv2
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | @withPred_true_ref k t ls l a1 a2 qt v1 v2 _htag _hreg hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have : ETyp.ref t ls = ETyp.ref ETyp.int ls0 := by
          calc
            ETyp.ref t ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ETyp.int ls0 := hres1_etyp0
        cases this
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | clean_eq_nonref_nonarrow _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ETyp.int, ls0, hres1_etyp0⟩
    | withPred_true_eq _ _ _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ETyp.int, ls0, hres1_etyp0⟩
    | clean_internal_arrow _ hetyp _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | dirty_internal_arrow _ hisArrow _ _ =>
        exfalso
        -- res1.etyp is ref, so cannot be arrow
        have : res1.qualType.etyp.isArrow = false := by
          simp [hres1_etyp0, ETyp.isArrow]
        rw [hisArrow] at this
        cases this
    | clean_internal_parrow _ hetyp _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | dirty_internal_parrow _ hisParrow _ _ =>
        exfalso
        have : res1.qualType.etyp.isParrow = false := by
          simp [hres1_etyp0, ETyp.isParrow]
        rw [hisParrow] at this
        cases this
  -- Obtain the memory type for l from the context
  have hlookup_ctx : ∃ qt, (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
    -- Use runtime instantiation to show l is present, then pick its lookup
    have hcontains : (ctxAfter ctxᵢ res1).memEnv.contains l = true := by
      -- from runtimeInstantiatesCtx and θ₀' lookup
      have hctx : (ctxAfter ctxᵢ res1).memEnv.contains l ∧ cfg₀'.memory.contains a₀' :=
        (hric₀'.1 l a₀' hθ₀l)
      exact hctx.1
    have hmem : l ∈ (ctxAfter ctxᵢ res1).memEnv :=
      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : ((ctxAfter ctxᵢ res1).memEnv[l]?).isSome = true :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
    cases hlookup_l : (ctxAfter ctxᵢ res1).memEnv[l]? with
    | none =>
        simp [hlookup_l] at hlookup_isSome
    | some qt =>
        -- align lookup with lookup? in the map
        have hlookup_l' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
          simpa [MemoryTypeEnv.lookup] using hlookup_l
        exact ⟨qt, hlookup_l'⟩
  obtain ⟨qt, hlookup_ctx⟩ := hlookup_ctx
  -- Get agreement on the location from agreeOnClean (location is clean under ctxᵢ.regime)
  have hclean_loc : qtypCleanUnder ctxᵢ.regime qt := by
    -- Analyze typecheckDeref to obtain the fold result, then use hclean.
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        have h_etyp : etyp = ETyp.ref ETyp.int ls0 := by
          simpa [hq] using hres1_etyp0
        have h_poison : poison = false := by
          simpa [hq] using hres1_poison_false
        have htc'' := htc'
        simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
        by_cases hls : ls0 = ∅
        · simp [hls] at htc''; cases htc''
        · simp [hls] at htc''
          cases hfold :
              ls0.foldM (m := Except String) (false, none) (fun x l =>
                match res1.memEnv'[l]? with
                | some qt =>
                    if qt.etyp = ETyp.int then
                      pure
                        (joinPoison x.1 qt.poison,
                          match x.2 with
                          | none => some qt.pred
                          | some p => some (joinPredicates p qt.pred))
                    else
                      throw
                        (toString "Type mismatch in dereference at " ++ toString l ++ toString ": " ++
                          toString (repr qt.etyp) ++ toString " ≠ int")
                | none =>
                    throw
                      (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
          | error err =>
              have htc_bad : typecheckDeref ctxᵢ e (Nat.succ fuel') = Except.error err := by
                simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, hls,
                  bind, Except.bind, pure, Except.pure]
                erw [hfold]
              have htc_bad_false : False := by
                simp [htc_bad] at htc'
              cases htc_bad_false
          | ok v_3 =>
              have hfold_plain :
                  ls0.foldM (m := Except String) (false, none) (fun x l =>
                    match res1.memEnv'[l]? with
                    | some qt =>
                        if qt.etyp = ETyp.int then
                          pure
                            (joinPoison x.1 qt.poison,
                              match x.2 with
                              | none => some qt.pred
                              | some p => some (joinPredicates p qt.pred))
                        else
                          throw
                            (toString "Type mismatch in dereference at " ++ toString l ++ toString ": " ++
                              toString (repr qt.etyp) ++ toString " ≠ int")
                    | none =>
                        throw
                          (toString "Location " ++ toString l ++ toString " not found in memory environment")) =
                    Except.ok v_3 := by
                simpa using hfold
              erw [hfold_plain] at htc''
              have hfold' :
                  LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                    Except.ok v_3 := by
                simpa [LocSet.foldM, derefFoldF] using hfold
              have hlookup_ctx' : res1.memEnv'[l]? = some qt := by
                simpa [ctxAfter, MemoryTypeEnv.lookup] using hlookup_ctx
              cases hclean with
            | clean hpoison =>
                cases hpred : v_3.2.getD Predicate.noPred with
                | noPred =>
                    simp [pure, Except.pure] at htc''
                    simp [hpred] at htc''

                    cases htc''
                    have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                      simpa [hpoison]
                    have hjoined_false : v_3.1 = false :=
                      (joinPoison_eq_false hjoin').2
                    obtain ⟨qt', hlookup', _het, hpoison'⟩ :=
                      deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                    have hqt' : qt' = qt := by
                      have : some qt' = some qt := by
                        calc
                          some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                          _ = some qt := hlookup_ctx'
                      exact Option.some.inj this
                    have hpoison'' : qt.poison = false := by
                      simpa [hqt'] using hpoison'
                    exact qtypCleanUnder.clean hpoison''
                | guardOnly k =>
                    cases htagEnv : res1.tagEnv'[k]? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                          simpa [hpoison]
                        have hjoined_false : v_3.1 = false :=
                          (joinPoison_eq_false hjoin').2
                        obtain ⟨qt', hlookup', _het, hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hpoison'' : qt.poison = false := by
                          simpa [hqt'] using hpoison'
                        exact qtypCleanUnder.clean hpoison''
                    | some tagInfo =>
                        cases tagInfo with
                        | mk val deps =>
                            cases val with
                            | true =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                have hpc : ctxᵢ.pc = false := by
                                  simpa [hpoison]
                                -- regime consistency yields ctxᵢ.regime.lookup? k = some true
                                have htagEnv' :
                                    (ctxAfter ctxᵢ res1).tagEnv.get? k = some ⟨true, deps⟩ := by
                                  simpa [ctxAfter] using htagEnv
                                have hreg_k : ctxᵢ.regime.lookup? k = some true :=
                                  (hreg'.1 k deps htagEnv')
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred]
                                  simp [predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using htagqt
                                obtain ⟨qt'', hlookup'', het⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'[l]? := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  rw [← hqt'']
                                  simp [het]
                                exact qtypCleanUnder.guard k htagqt' hreg_k hnotfun'
                            | false =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                cases hpoison
                | guardClosure k a b env =>
                    -- same reasoning as guardOnly
                    cases htagEnv : res1.tagEnv'[k]? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                          simpa [hpoison]
                        have hjoined_false : v_3.1 = false :=
                          (joinPoison_eq_false hjoin').2
                        obtain ⟨qt', hlookup', _het, hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hpoison'' : qt.poison = false := by
                          simpa [hqt'] using hpoison'
                        exact qtypCleanUnder.clean hpoison''
                    | some tagInfo =>
                        cases tagInfo with
                        | mk val deps =>
                            cases val with
                            | true =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                have hpc : ctxᵢ.pc = false := by
                                  simpa [hpoison]
                                have htagEnv' :
                                    (ctxAfter ctxᵢ res1).tagEnv.get? k = some ⟨true, deps⟩ := by
                                  simpa [ctxAfter] using htagEnv
                                have hreg_k : ctxᵢ.regime.lookup? k = some true :=
                                  (hreg'.1 k deps htagEnv')
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred, predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using htagqt
                                obtain ⟨qt'', hlookup'', het⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'[l]? := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  rw [← hqt'']
                                  simp [het]
                                exact qtypCleanUnder.guard k htagqt' hreg_k hnotfun'
                            | false =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                cases hpoison
            | guard k htag hreg hnotfun =>
                -- merged predicate must carry tag k
                cases hpred : v_3.2.getD Predicate.noPred with
                | noPred =>
                    simp [hpred, pure, Except.pure] at htc''
                    rw [← htc''] at htag
                    -- res.pred is noPred, so qtypGuardTag is none: contradiction
                    simp [qtypGuardTag] at htag
                | guardOnly k' =>
                    -- tagEnv must be none, otherwise res.pred noPred
                    cases htagEnv : res1.tagEnv'[k']? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k' := by
                          simp [hpred, predGuardTag]
                        obtain ⟨qt', hlookup', htagqt⟩ :=
                          deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k' hfold' hguard l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have htagqt' : qtypGuardTag qt = some k := by
                          -- align k' with k using htag
                          simp [qtypGuardTag] at htag
                          rw [hqt', htag] at htagqt
                          simp [predGuardTag] at htagqt
                          simp [qtypGuardTag]
                          cases hqtpred : qt.pred
                            <;> simp [hqtpred] at htagqt
                            <;> simpa using htagqt
                        -- show not function
                        obtain ⟨qt'', hlookup'', het⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'[l]? := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                          rw [← hqt'']
                          simp [het]
                        exact qtypCleanUnder.guard k htagqt' hreg hnotfun'
                    | some val =>
                        simp [hpred, htagEnv, pure, Except.pure] at htc''
                        rcases hval : val with ⟨b, deps⟩; rcases hb : b
                          <;> simp [hval, hb] at htc''
                          <;> rw [← htc''] at htag
                          <;> simp [qtypGuardTag] at htag
                | guardClosure k' a b env =>
                    -- same as guardOnly
                    cases htagEnv : res1.tagEnv'[k']? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k' := by
                          simp [hpred, predGuardTag]
                        obtain ⟨qt', hlookup', htagqt⟩ :=
                          deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k' hfold' hguard l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'[l]? := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have htagqt' : qtypGuardTag qt = some k := by
                          have hk : k' = k := by
                            simpa [qtypGuardTag, hpred] using htag
                          simpa [hk, hqt'] using htagqt
                        obtain ⟨qt'', hlookup'', het⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'[l]? := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                          rw [← hqt'']
                          simp [het]
                        exact qtypCleanUnder.guard k htagqt' hreg hnotfun'
                    | some val =>
                        simp [hpred, htagEnv, pure, Except.pure] at htc''
                        rcases hval : val with ⟨b, deps⟩; rcases hb : b
                          <;> simp [hval, hb] at htc''
                          <;> rw [← htc''] at htag
                          <;> simp [qtypGuardTag] at htag
  have hagree_loc := (hagree_clean_e.1 l qt hlookup_ctx hclean_loc)
  have hEq : o₀ = o₁ := by
    -- Use the agreement on the location to show equality of stored ints.
    cases hagree_loc with
    | both_unrealized _ _ hnone0 hnone1 =>
        -- impossible: deref requires a realized location
        -- contradict θ₀'.lookup l = some a₀'
        rw [hθ₀l] at hnone0
        cases hnone0
    | agree_values _ _ a0 a1 m0 m1 hreal0 hreal1 hm0 hm1 hagree_val =>
        -- The addresses must match those from deref
        have ha0 : a0 = a₀' := by
          have : some a0 = some a₀' := by
            calc
              some a0 = θ₀'.lookup l := by symm; exact hreal0
              _ = some a₀' := by exact hθ₀l
          exact Option.some.inj this
        have ha1 : a1 = a₁' := by
          have : some a1 = some a₁' := by
            calc
              some a1 = θ₁'.lookup l := by symm; exact hreal1
              _ = some a₁' := by exact hθ₁l
          exact Option.some.inj this
        subst ha0; subst ha1
        have hvalEq : m0 = m1 := by
          -- Use the structure of agreeValueUnder on integer values
          cases hagree_val with
          | clean_eq_nonref_nonarrow _ _ _ hEq =>
              cases hEq
              rfl
          | withPred_true_eq _ _ _ _ _ hEq =>
              cases hEq
              rfl
          | clean_ref _ _ _ _ hv1 _ _ =>
              cases hv1
          | @withPred_true_ref k t ls l0 a1 a2 qt' v1 v2 _htag _hreg _hetyp _hlookup1 _hin hv1 _hlookup2 _hv2 =>
              cases hv1
          | clean_internal_arrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow _ hisArrow htyp1 _ =>
              -- Value.num can only have type int, so isArrow must be false.
              have hqte_int : qt.etyp = ETyp.int :=
                valueHasETyp_num_etyp htyp1
              have : qt.etyp.isArrow = false := by
                simp [hqte_int, ETyp.isArrow]
              rw [hisArrow] at this
              cases this
          | clean_internal_parrow _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_parrow _ hisParrow htyp1 _ =>
              -- Value.num can only have type int, so isParrow must be false.
              have hqte_int : qt.etyp = ETyp.int :=
                valueHasETyp_num_etyp htyp1
              have : qt.etyp.isParrow = false := by
                simp [hqte_int, ETyp.isParrow]
              rw [hisParrow] at this
              cases this
        -- Use memory lookup equalities
        have : n₀ = n₁ := by
          have : some n₀ = some n₁ := by
            calc
              some n₀ = cfg₀'.memory.lookup a0 := by symm; exact hlookup₀
              _ = some m0 := by simpa [hmem₀] using hm0
              _ = some m1 := by simp [hvalEq]
              _ = cfg₁'.memory.lookup a1 := by symm; simpa [hmem₁] using hm1
              _ = some n₁ := hlookup₁
          exact Option.some.inj this
        -- o₀ and o₁ are Value.num of these ints
        simp [hv₀, hv₁, this]
  -- Build agreement on the return value (int)
  have hres_etyp_int : res.qualType.etyp = ETyp.int :=
    typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
  have hnotref_res : ¬ ∃ t ls, res.qualType.etyp = ETyp.ref t ls := by
    intro hcontra
    rcases hcontra with ⟨t, ls, h_etyp⟩
    -- deref always returns int
    have : res.qualType.etyp = ETyp.ref t ls := h_etyp
    rw [hres_etyp_int] at this
    cases this
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    -- deref returns int
    simp [hres_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  cases hclean with
  | clean hpoison =>
      exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun_res hnotref_res hEq
  | guard k htag hreg hnotfun =>
      exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref_res hEq

-- Stub lemma for while loop (not yet proven)
private lemma stepFR_kwhile
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.kwhile e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.kwhile e1 e2) res predSat := by
  sorry

-- Helper lemma for the `.arrow` typing branch of `stepFR_app`.
--
-- This lemma is intentionally left unproven for now; it packages the application-specific
-- reasoning (inversion of `terminatesTo` for `app`, stepping `e2`/`e1`/body with IH, and
-- lifting agreement to `ctxAfter ctxᵢ res`) in a re-usable form.
private lemma stepFR_app_closure_closure_arrow_remaining
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (res2 res1 : TypeResult) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (htc2 : typecheck ctxᵢ e2 fuel' = .ok res2)
  (htc1 : typecheck (ctxAfter ctxᵢ res2) e1 fuel' = .ok res1)
  (harr :
    ∃ st1 st2 p p1 tcls results first rest,
      res1.qualType.etyp = ETyp.arrow st1 st2 p tcls ∧
        res1.qualType.poison = p1 ∧
          ¬ctxᵢ.pureCtx = true ∧
            tcls ≠ [] ∧
              isSubtype st1 res2.qualType = true ∧
                List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctxᵢ res2 fuel') tcls =
                    Except.ok results ∧
                  results = first :: rest ∧ joinTypeResults ctxᵢ first rest = Except.ok res) :
  StepFR .ioFree ctxᵢ (Expr.app e1 e2) res predSat := by
  have hIH2 :=
    IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel')) e2 ctxᵢ res2 htc2
  have hIH1 :=
    IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel')) e1 (ctxAfter ctxᵢ res2) res1 htc1
  intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hstruct₀ :=
    terminatesTo_app_inv' e1 e2
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have hstruct₁ :=
    terminatesTo_app_inv' e1 e2
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  -- We will step `e2` first (common to all app cases), then step `e1` in the post-`e2` context,
  -- and finally relate the body step to the `.arrow` typing spine `harr`.
  rcases hstruct₀ with hcl₀ | hpe₀
  · rcases hcl₀ with
      ⟨cfg₀2, v₀2, cfg₀1, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm₀1, ht₀_body, hcf₀_eq, hpm₀2, hpm₀_final⟩
    rcases hstruct₁ with hcl₁ | hpe₁
    · rcases hcl₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm₁1, ht₁_body, hcf₁_eq, hpm₁2, hpm₁_final⟩
      -- Step `e2` using IH.
      have hstep_e2 :=
        hIH2 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, harg_agree⟩
      -- Step `e1` using IH in the post-`e2` context.
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      have hwf_ctxAfter : wfTypeContext (ctxAfter ctxᵢ res2) := hwf2
      have htagR2' : regimeConsistentWithCtx (ctxAfter ctxᵢ res2) (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Update for regime threading
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
            cfg₁1 (Value.closure x₁ body₁ env₁) := by
        rw [← hcfg₁2_eq]
        exact ht₁_e1
      have hwfcfg₁2' :
          wfConfig { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        rw [← hcfg₁2_eq]
        exact hwfcfg₁2
      have hRbound' : regimeBounded (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Derive from hRbound with regime monotonicity
      have hagree2' : agreeOnClean predSat (ctxAfter ctxᵢ res2).regime (ctxAfter ctxᵢ res2)
          cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        sorry -- TODO: Derive from hagree2 with regime equality
      have hstep_e1 :=
        hIH1 hpredlaws cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf_ctxAfter hric₀2 hric₁2 htagR2' hRbound' hcwr₀2 hcwr₁2 hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, hwf3, hwfcfg₀3, hwfcfg₁3,
          hric₀3, hric₁3, htagR3, hcwr₀3_, hcwr₁3_, hagree3, hfun_agree⟩
      -- Remaining work: relate `ht₀_body`/`ht₁_body` and the `.arrow` typing spine `harr`,
      -- then lift agreement to `ctxAfter ctxᵢ res`.
      -- (This is the hard core of `stepFR_app` and will be filled next.)
      classical
      rcases harr with
        ⟨st1, st2, p, p1, tcls, results, first, rest,
          hetyp_arrow, hpoison1, hnotPure, htcls_ne, hsub, hmap, hresults, hjoin⟩
      -- The rest of the proof proceeds by:
      -- 1. extracting the specific closure-typing alternative that matches the runtime closures
      --    (using `hfun_agree` once we have `qtypCleanUnder ctxᵢ.regime res1.qualType`),
      -- 2. obtaining the corresponding body typing result from `hmap`,
      -- 3. stepping `body₀`/`body₁` using IH to get agreement for `o₀`/`o₁`,
      -- 4. lifting runtime/context invariants to `ctxAfter ctxᵢ res` (via `hjoin`).
      --
      -- These are split into small claims below.
      sorry
    · -- Run 1 produced a predicated closure (impossible for `.arrow` typing).
      rcases hpe₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, _evalCfg₁, ht₁_e2, ht₁_e1, _htoP₁, _ht₁_body, _hcf₁_eq, hpm₁2, _hpm₁_final⟩
      -- Step `e2` using IH (to obtain post-`e2` context instantiation for both runs).
      have hstep_e2 :=
        hIH2 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _harg_agree⟩
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      have htagR2' : regimeConsistentWithCtx (ctxAfter ctxᵢ res2) (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Update for regime threading
      have hRbound' : regimeBounded (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Prove regime boundedness preserved
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
      -- Step `e1` using IH (closure vs peClosure).
      have hRbound' : regimeBounded (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Derive from hRbound with regime monotonicity
      have hagree2' : agreeOnClean predSat (ctxAfter ctxᵢ res2).regime (ctxAfter ctxᵢ res2)
          cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        sorry -- TODO: Derive from hagree2 with regime equality
      have hstep_e1 :=
        hIH1 hpredlaws cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2' hRbound' hcwr₀2 hcwr₁2 hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, θ₁3, _hθext₀3, hθext₁3, _hwf3, _hwfcfg₀3, _hwfcfg₁3,
          _hric₀3, hric₁3, _htagR3, _hcwr₀3, _hcwr₁3, _hagree3, _hfun_agree⟩
      have hθ₁3wf : wfRealizationMap θ₁3 := hθext₁3.2 hθ₁2wf
      -- Convert world-free termination to world-indexed, then apply preservation to type the peClosure.
      let w_default := LeanProofs.defaultWorld
      have ht₁_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₁1 (Value.peClosure x₁ body₁ env₁) := by
        rcases ht₁_e1' with ⟨fuel₁, verbose₁, hpure₁⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
        exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
      have hric₁3_mem : runtimeInstantiatesCtx { (ctxAfter ctxᵢ res2) with memEnv := res1.memEnv' }
          cfg₁1.memory cfg₁1.varEnv θ₁3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter] using hric₁3
      have hv₁_fun_typed : valueHasETyp θ₁3 (Value.peClosure x₁ body₁ env₁) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 (ctxAfter ctxᵢ res2)
          fuel' res1
          cfg₁2.memory cfg₁1.memory cfg₁2.varEnv cfg₁1.varEnv θ₁2 θ₁3
          cfg₁2.nextAddr cfg₁1.nextAddr cfg₀2.pureMode cfg₁1.pureMode
          (Value.peClosure x₁ body₁ env₁) w_default w_default
          hwf2 htc1 hθ₁2wf hθ₁3wf hθext₁3 hric₁2 hric₁3_mem ht₁_e1_w).1
      -- But `harr` forces `res1.qualType.etyp` to be an arrow type, so this is impossible.
      rcases harr with ⟨st1, st2, p, _p1, tcls, _results, _first, _rest, hetyp_arrow, _⟩
      have hv_parr : valueHasETyp θ₁3 (Value.peClosure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := by
        simpa [hetyp_arrow] using hv₁_fun_typed
      cases hv_parr
  · -- Run 0 produced a predicated closure (impossible for `.arrow` typing).
    rcases hpe₀ with
      ⟨cfg₀2, v₀2, cfg₀1, x₀, body₀, env₀, _evalCfg₀, ht₀_e2, ht₀_e1, _htoP₀, _ht₀_body, _hcf₀_eq, hpm₀2, _hpm₀_final⟩
    rcases hstruct₁ with hcl₁ | hpe₁
    · rcases hcl₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, _evalCfg₁, ht₁_e2, ht₁_e1, _hpm₁1, _ht₁_body, _hcf₁_eq, hpm₁2, _hpm₁_final⟩
      -- Step `e2` to obtain post-`e2` instantiation.
      have hstep_e2 :=
        hIH2 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _harg_agree⟩
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      have htagR2' : regimeConsistentWithCtx (ctxAfter ctxᵢ res2) (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Update for regime threading
      have hRbound' : regimeBounded (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Prove regime boundedness preserved
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
            cfg₁1 (Value.closure x₁ body₁ env₁) := by
        rw [← hcfg₁2_eq]
        exact ht₁_e1
      have hwfcfg₁2' :
          wfConfig { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode } := by
        rw [← hcfg₁2_eq]
        exact hwfcfg₁2
      -- Step `e1` using IH (peClosure vs closure).
      have hagree2' : agreeOnClean predSat (ctxAfter ctxᵢ res2).regime (ctxAfter ctxᵢ res2)
          cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        sorry -- TODO: Derive from hagree2 with regime equality
      have hstep_e1 :=
        hIH1 hpredlaws cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.peClosure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2' hRbound' hcwr₀2 hcwr₁2 hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, _θ₁3, hθext₀3, _hθext₁3, _hwf3, _hwfcfg₀3, _hwfcfg₁3,
          hric₀3, _hric₁3, _htagR3, _hcwr₀3, _hcwr₁3, _hagree3, _hfun_agree⟩
      have hθ₀3wf : wfRealizationMap θ₀3 := hθext₀3.2 hθ₀2wf
      -- Convert world-free termination to world-indexed, then apply preservation to type the peClosure.
      let w_default := LeanProofs.defaultWorld
      have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₀2.memory, varEnv := cfg₀2.varEnv, nextAddr := cfg₀2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₀1 (Value.peClosure x₀ body₀ env₀) := by
        rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
        exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
      have hric₀3_mem : runtimeInstantiatesCtx { (ctxAfter ctxᵢ res2) with memEnv := res1.memEnv' }
          cfg₀1.memory cfg₀1.varEnv θ₀3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter] using hric₀3
      have hv₀_fun_typed : valueHasETyp θ₀3 (Value.peClosure x₀ body₀ env₀) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 (ctxAfter ctxᵢ res2)
          fuel' res1
          cfg₀2.memory cfg₀1.memory cfg₀2.varEnv cfg₀1.varEnv θ₀2 θ₀3
          cfg₀2.nextAddr cfg₀1.nextAddr cfg₀2.pureMode cfg₀1.pureMode
          (Value.peClosure x₀ body₀ env₀) w_default w_default
          hwf2 htc1 hθ₀2wf hθ₀3wf hθext₀3 hric₀2 hric₀3_mem ht₀_e1_w).1
      rcases harr with ⟨st1, st2, p, _p1, tcls, _results, _first, _rest, hetyp_arrow, _⟩
      have hv_bad : valueHasETyp θ₀3 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := by
        simpa [hetyp_arrow] using hv₀_fun_typed
      cases hv_bad
    · -- Both runs produced predicated closures; still impossible for `.arrow` typing (same argument).
      rcases hpe₁ with
        ⟨cfg₁2, v₁2, cfg₁1, x₁, body₁, env₁, _evalCfg₁, ht₁_e2, ht₁_e1, _htoP₁, _ht₁_body, _hcf₁_eq, hpm₁2, _hpm₁_final⟩
      -- Step `e2` to obtain post-`e2` instantiation.
      have hstep_e2 :=
        hIH2 hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀2 cfg₁2 v₀2 v₁2
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with
        ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hwf2, hwfcfg₀2, hwfcfg₁2,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _harg_agree⟩
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      have htagR2' : regimeConsistentWithCtx (ctxAfter ctxᵢ res2) (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Update for regime threading
      have hRbound' : regimeBounded (ctxAfter ctxᵢ res2).regime := by
        sorry -- TODO: Prove regime boundedness preserved
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
      -- Step `e1` using IH (peClosure vs peClosure) just to obtain θ₀3 for preservation.
      have hagree2' : agreeOnClean predSat (ctxAfter ctxᵢ res2).regime (ctxAfter ctxᵢ res2)
          cfg₀2.memory cfg₀2.varEnv θ₀2 cfg₁2.memory cfg₁2.varEnv θ₁2 := by
        sorry -- TODO: Derive from hagree2 with regime equality
      have hstep_e1 :=
        hIH1 hpredlaws cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀2 θ₁2
          cfg₀1 cfg₁1 (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2' hRbound' hcwr₀2 hcwr₁2 hagree2'
          cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
          ht₀_e1 ht₁_e1'
      rcases hstep_e1 with
        ⟨θ₀3, _θ₁3, hθext₀3, _hθext₁3, _hwf3, _hwfcfg₀3, _hwfcfg₁3,
          hric₀3, _hric₁3, _htagR3, _hcwr₀3, _hcwr₁3, _hagree3, _hfun_agree⟩
      have hθ₀3wf : wfRealizationMap θ₀3 := hθext₀3.2 hθ₀2wf
      let w_default := LeanProofs.defaultWorld
      have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1
          { memory := cfg₀2.memory, varEnv := cfg₀2.varEnv, nextAddr := cfg₀2.nextAddr, pureMode := cfg₀2.pureMode }
          cfg₀1 (Value.peClosure x₀ body₀ env₀) := by
        rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
        have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
        exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
      have hric₀3_mem : runtimeInstantiatesCtx { (ctxAfter ctxᵢ res2) with memEnv := res1.memEnv' }
          cfg₀1.memory cfg₀1.varEnv θ₀3 := by
        simpa [runtimeInstantiatesCtx, ctxAfter] using hric₀3
      have hv₀_fun_typed : valueHasETyp θ₀3 (Value.peClosure x₀ body₀ env₀) res1.qualType.etyp :=
        (preservation_valueW .ioFree e1 (ctxAfter ctxᵢ res2)
          fuel' res1
          cfg₀2.memory cfg₀1.memory cfg₀2.varEnv cfg₀1.varEnv θ₀2 θ₀3
          cfg₀2.nextAddr cfg₀1.nextAddr cfg₀2.pureMode cfg₀1.pureMode
          (Value.peClosure x₀ body₀ env₀) w_default w_default
          hwf2 htc1 hθ₀2wf hθ₀3wf hθext₀3 hric₀2 hric₀3_mem ht₀_e1_w).1
      rcases harr with ⟨st1, st2, p, _p1, tcls, _results, _first, _rest, hetyp_arrow, _⟩
      have hv_bad : valueHasETyp θ₀3 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := by
        simpa [hetyp_arrow] using hv₀_fun_typed
      cases hv_bad

-- Helper lemma for the remaining `peClosure` branch in `stepFR_app`.
-- This is the `.parrow` analogue of the `closure/closure` case.
private lemma stepFR_app_peClosure_remaining
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (res2 res1 : TypeResult) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (htc2 : typecheck ctxᵢ e2 fuel' = .ok res2)
  (htc1 : typecheck (ctxAfter ctxᵢ res2) e1 fuel' = .ok res1)
  (hparr :
    ∃ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
      (results : List TypeResult) (first : TypeResult) (rest : List TypeResult),
      res1.qualType.etyp = ETyp.parrow st1 st2 p tcls ∧
        res1.qualType.poison = p1 ∧
          tcls ≠ [] ∧
            isSubtype st1 res2.qualType = true ∧
              List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctxᵢ res2 fuel') tcls =
                  Except.ok results ∧
                results = first :: rest ∧ joinTypeResults ctxᵢ first rest = Except.ok res) :
  StepFR .ioFree ctxᵢ (Expr.app e1 e2) res predSat := by
  sorry

-- Function application case: reduces to helper lemmas for closure/closure and peClosure branches
private lemma stepFR_app
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.app e1 e2) res predSat := by
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
    { ctxᵢ with memEnv := res2.memEnv', tagEnv := res2.tagEnv', nextLoc := res2.nextLoc', nextTag := res2.nextTag', regime := res2.regime' }
  have htc1' : typecheck ctx' e1 fuel' = .ok res1 := by
    -- Note: htc1 uses ctxᵢ.regime but ctx' uses res2.regime'
    -- This requires showing regime equality, which needs regime monotonicity
    simp only [ctx', typecheck]
    sorry -- TODO: Requires regime monotonicity - res2.regime' = ctxᵢ.regime
  have htc1_after : typecheck (ctxAfter ctxᵢ res2) e1 fuel' = .ok res1 := by
    simpa [ctx', ctxAfter] using htc1'
  cases happ_cases with
  | inl harr =>
      exact stepFR_app_closure_closure_arrow_remaining
        ctxᵢ predSat e1 e2 fuel' res IH res2 res1 argEtyp argPoison argPred htc2' htc1_after harr
  | inr hparr =>
      exact stepFR_app_peClosure_remaining
        ctxᵢ predSat e1 e2 fuel' res IH res2 res1 argEtyp argPoison argPred htc2' htc1_after hparr

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
  intro fuel res htc
  -- Use strong induction on fuel, generalized over all e and ctxᵢ
  -- The key insight: we need IH to work for any I/O-free expression, not just our specific e
  revert e ctxᵢ res htc
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctxᵢ res htc
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
              regime' := ctxᵢ.regime
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
            exact stepFR_literal .ioFree ctxᵢ predSat Expr.unit res Value.unit hval hpoison hnotfun hnotref hctxAfter
        | num n =>
            simp [typecheck, typecheckExpr, typecheckInt] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.int, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
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
            exact stepFR_literal .ioFree ctxᵢ predSat (Expr.num n) res (Value.num n) hval hpoison hnotfun hnotref hctxAfter
        | bool b =>
            simp [typecheck, typecheckExpr, typecheckBool] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.bool, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
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
            exact stepFR_literal .ioFree ctxᵢ predSat (Expr.bool b) res (Value.bool b) hval hpoison hnotfun hnotref hctxAfter
        | str s =>
            simp [typecheck, typecheckExpr, typecheckString] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.string, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
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
            exact stepFR_literal .ioFree ctxᵢ predSat (Expr.str s) res (Value.str s) hval hpoison hnotfun hnotref hctxAfter
        | var name =>
            exact stepFR_var .ioFree ctxᵢ predSat name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                exact stepFR_op ctxᵢ predSat e1 e2 op fuel' res IH htc
        | unaryop uop e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                exact stepFR_unaryop ctxᵢ predSat e uop fuel' res IH htc
        | ite e1 e2 e3 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckIf] at htc
            | succ fuel' =>
                exact stepFR_ite ctxᵢ predSat e1 e2 e3 fuel' res IH htc
        | newRef e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                exact stepFR_newRef ctxᵢ predSat e fuel' res IH htc
        | assign e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckAssign] at htc
            | succ fuel' =>
                exact stepFR_assign ctxᵢ predSat e1 e2 fuel' res IH htc
        | deref e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckDeref] at htc
            | succ fuel' =>
                exact stepFR_deref ctxᵢ predSat e fuel' res IH htc
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                exact stepFR_seq ctxᵢ predSat e1 e2 fuel' res IH htc
        | kwhile e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckWhile] at htc
            | succ fuel' =>
                exact stepFR_kwhile ctxᵢ predSat e1 e2 fuel' res IH htc
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                exact stepFR_vlet ctxᵢ predSat vname e1 e2 fuel' res IH htc
        | fn name ty e1 ty2 =>
            exact stepFR_fn .ioFree ctxᵢ predSat name ty e1 ty2 fuel res htc
        | pfn name ty e1 ty2 =>
            exact stepFR_pfn .ioFree ctxᵢ predSat name ty e1 ty2 fuel res htc
        | app e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckApp] at htc
            | succ fuel' =>
                exact stepFR_app ctxᵢ predSat e1 e2 fuel' res IH htc
        | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            -- In `.ioFree` mode, I/O constructs cannot terminate, so StepFR is vacuous.
            intro hpredlaws μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
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
-- FaultRobustnessSpec specialized to ioFree mode (implied by FaultRobustnessSpec)
def FaultRobustnessSpec_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool),
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    ctx.regime.bound = ctx.nextTag →  -- regime bounded by initial tag supply
    wfRegime ctx.regime s →
    regimeBounded ctx.regime →
    wfRealizationMap θ₁ →  wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } →
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ →  consistentRegimeSpec predSat ctx.regime s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs predSat ctx.regime s ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo .ioFree e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
    terminatesTo .ioFree e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

-- FaultRobustnessSpec implies FaultRobustnessSpec_ioFree (by instantiating mode = .ioFree)
lemma FaultRobustnessSpec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) :
    FaultRobustnessSpec e s obs ctx predSat → FaultRobustnessSpec_ioFree e s obs ctx predSat := by
  intro h
  unfold FaultRobustnessSpec_ioFree
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm cf₁ cf₂ o₁ o₂
  exact h .ioFree μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm cf₁ cf₂ o₁ o₂

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

-- TypeSystemEnforcesFaultRobustness_spec implies TypeSystemEnforcesFaultRobustness_spec_ioFree
lemma TypeSystemEnforcesFaultRobustness_spec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
    TypeSystemEnforcesFaultRobustness_spec e s obs → TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs := by
  intro h his hos ctx hctx hwf hpc hte predSat hps htc
  exact FaultRobustnessSpec_implies_ioFree e s obs ctx predSat (h his hos ctx hctx hwf hpc hte predSat hps htc)

theorem TypeSystemEnforcesFaultRobustness_impl_IOFree :
  (∀ e ctxᵢ predSat, TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx hwf _hpc hte predSat hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstep e ctx predSat
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hR hRbound hregBounded hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R := ctx.regime with hRdef
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
    · exact Nat.le_of_eq hR
  -- Need consistentWithRegime for both runs (derived from bridge lemma)
  have hcwr₁ : consistentWithRegime predSat R ctx μ₁ ρ₁ θ₁ := by
    have hcrs₁' : consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ := by
      simpa [hRdef] using hcrs₁
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₁ ρ₁ θ₁ hcrs₁' hctx hRbound' hregBounded'
  have hcwr₂ : consistentWithRegime predSat R ctx μ₂ ρ₂ θ₂ := by
    have hcrs₂' : consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ := by
      simpa [hRdef] using hcrs₂
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₂ ρ₂ θ₂ hcrs₂' hctx hRbound' hregBounded'
  have hstep_fr := hstep' hps μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂ hθ₁ hθ₂ hwf hric₁ hric₂ hreg hregBounded hcwr₁ hcwr₂ hagree_clean a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  -- StepFR result structure: ∃ θ₁' θ₂', wfExtendsMap ∧ wfExtendsMap ∧ wfTypeContext ∧
  --   wfConfig ∧ wfConfig ∧ agreeOnClean ∧ resultAgreesIfClean
  rcases hstep_fr with ⟨θ₁', θ₂', hwfext₁, hwfext₂, _hwfctx', _hwfcfg₁', _hwfcfg₂', _hric₁', _hric₂', _hreg', _hcwr₁', _hcwr₂', hagree_clean', hret_agree⟩
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
          | clean_eq_nonref_nonarrow _ _ _ hval =>
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
          | clean_ref _ _ _ _ hv1 _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ _ hval =>
              cases hval
              rfl
          | withPred_true_ref _ _ _ _ _ _ hv1 _ _ =>
              cases hv1
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
            | @clean_ref _t _ls l a₁' a₂' _qt _v₁ _v₂ hpoison' hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k _t _ls l a₁' a₂' _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have href := Eq.trans (Eq.symm hetyp) hret_et
                cases href
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | clean_eq_nonref_nonarrow _ _ hnotref _ =>
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
