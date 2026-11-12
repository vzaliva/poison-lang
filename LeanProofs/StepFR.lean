/-
  StepFR.lean - Shared definitions and utility lemmas for fault-robustness proofs.

  Core definitions (StepFR, StepFRPost, resultAgreesIfClean, the single-run
  StepFRSingleRunFinalCleanPcTrue family, the *_IH_WithExprCtx induction
  hypotheses, etc.), the bridge lemma
  consistentRegimeSpec_implies_consistentWithRegime, and helper lemmas used by
  multiple stepFR_* case proofs. Imports ExternTagMeaning and TypecheckInduction,
  whose lemmas are thereby available to every per-operator case file.
-/
import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness
import LeanProofs.TypeSafety
import LeanProofs.Auxiliary
import LeanProofs.SemanticsProperties
import LeanProofs.RegimeConsistency
import LeanProofs.TagFrame
import LeanProofs.ExternTagMeaning
import LeanProofs.TypecheckInduction
import LeanProofs.ExternCallSteps
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

def resultAgreesIfClean (predSat : PredSat) (R : Regime) (μ₀ μ₁ : Memory)
  (θ₀ θ₁ : RealizationMap) (qt : QTyp) (o₀ o₁ : Value) : Prop :=
  qtypCleanUnder R qt →
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁

/-- Rewrite a configuration as an explicit record while preserving an arbitrary
    extern registry.  Used to put intermediate configurations into the shape
    expected by recursive IH calls. -/
lemma config_eq_of_registry (cfg : Config) (registry : ExternRegistry)
    (h : cfg.registry = registry) :
  cfg = { memory := cfg.memory, varEnv := cfg.varEnv,
          nextAddr := cfg.nextAddr, pureMode := cfg.pureMode, registry := registry } := by
  cases cfg with
  | mk _ _ _ _ _ =>
      simp only [Config.mk.injEq, true_and]
      exact h

-- When qt.poison = true and qt.pred = noPred, qtypCleanUnder is impossible,
-- so resultAgreesIfClean is vacuously true.
lemma resultAgreesIfClean_of_poison_noPred
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {o₀ o₁ : Value}
    (hp : qt.poison = true) (hpred : qt.pred = Predicate.noPred) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hcu
  cases hcu with
  | clean hpoison => simp [hp] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, hpred] at htag

/-- Tag-meaning facts at a typing boundary, without an expression spine.

    For ordinary source steps, this follows from `IsCanonicalExtension` (the
    extension facts) plus `PredSatLaws` on the extended meaning; the extended
    meaning adds only allocations of the run (`WithinLog`).

    For extern call boundaries inside `Expr.app`, the same bundle is meant to
    be produced from the boundary witness rather than from `IsCanonicalExtension`
    on a single source expression. -/
def BoundaryTagMeaningPost
    (ctx : TypeContext) (res : TypeResult) (predSat : PredSat) (tm tm' : TagMeaning) :
    Prop :=
  tm ⊑ tm' ∧
  TagMeaningBounded tm' res.nextTag' ∧
  wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
  QTypRespectsTagMeaning tm' res.qualType ∧
  PredSatLaws predSat tm' ∧
  WithinLog tm res.tagLog' tm'

namespace BoundaryTagMeaningPost

theorem extends_tm
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    tm ⊑ tm' :=
  h.1

theorem bounded
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    TagMeaningBounded tm' res.nextTag' :=
  h.2.1

theorem wfCtx
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    wfTagMeaningCtx tm' (ctxAfter ctx res) :=
  h.2.2.1

theorem respectsResult
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    QTypRespectsTagMeaning tm' res.qualType :=
  h.2.2.2.1

theorem laws
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    PredSatLaws predSat tm' :=
  h.2.2.2.2.1

theorem within
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat} {tm tm' : TagMeaning}
    (h : BoundaryTagMeaningPost ctx res predSat tm tm') :
    WithinLog tm res.tagLog' tm' :=
  h.2.2.2.2.2

theorem of_isCanonical_predSat
    {tm tm' : TagMeaning} {ctx : TypeContext} {e : Expr} {res : TypeResult}
    {predSat : PredSat}
    (hco : IsCanonicalExtension tm ctx e res tm') (hl : PredSatLaws predSat tm')
    (hw : WithinLog tm res.tagLog' tm') :
    BoundaryTagMeaningPost ctx res predSat tm tm' :=
  ⟨IsCanonicalExtension.extends_tm hco,
    IsCanonicalExtension.bounded hco,
    IsCanonicalExtension.wfCtx hco,
    IsCanonicalExtension.respectsResult hco,
    hl, hw⟩

end BoundaryTagMeaningPost

/-- The already-applied runtime post of `StepFR`.

    This factors the conclusion of the two-run step theorem so extern boundary
    contracts can return the same post without unfolding all of `StepFR` at
    their consumption sites. -/
def StepFRPost
    (ctx : TypeContext) (_e : Expr) (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (θ₀ θ₁ : RealizationMap)
  (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop :=
  ∃ (tm' : TagMeaning),
    BoundaryTagMeaningPost ctx res predSat tm tm' ∧
    PredSatLaws predSat tm' ∧
    QTypRespectsTagMeaning tm' res.qualType ∧
    ∃ (θ₀' θ₁' : RealizationMap),
      wfExtendsMap θ₀ θ₀' ∧
      wfExtendsMap θ₁ θ₁' ∧
      valueHasETyp θ₀' o₀ res.qualType.etyp ∧
      valueHasETyp θ₁' o₁ res.qualType.etyp ∧
      wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
      wfTypeContext (ctxAfter ctx res) ∧
      TagBoundedCtx (ctxAfter ctx res) ∧
      wfConfig cf₀ ∧
      wfConfig cf₁ ∧
      runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
      runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
      regimeConsistentWithCtx (ctxAfter ctx res) ∧
      consistentWithRegime predSat (ctxAfter ctx res).regime
        (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
      consistentWithRegime predSat (ctxAfter ctx res).regime
        (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
      agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime
        res.qualType cf₀.memory θ₀' o₀ ∧
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime
        res.qualType cf₁.memory θ₁' o₁ ∧
      resultAgreesIfClean predSat (ctxAfter ctx res).regime
        cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁ ∧
      ReservedDiscipline cf₀.registry res.declared' θ₀' ∧
      ReservedDiscipline cf₁.registry res.declared' θ₁'

-- Bridge lemma: connect spec-indexed consistency to context-indexed consistency
lemma consistentRegimeSpec_implies_consistentWithRegime
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (h_spec : consistentRegimeSpec predSat R s μ ρ θ)
    (h_ric : runtimeInstantiatesCtx ctx μ ρ θ)
    (h_trusted_init : trustedVarsClosureRegimeInit predSat R s ctx μ ρ θ)
    (h_input_wf : wfInputSpec s)
    (h_match : ctxMatchesInputSpec s ctx)
    (h_wf : wfRegime R s) :
    consistentWithRegime predSat R ctx μ ρ θ := by
  rcases h_match with ⟨hctx_mem, hctx_vars, hctx_mem_hyg, hctx_vars_hyg_deep⟩
  rcases h_trusted_init with ⟨htrusted_init⟩
  rcases h_input_wf with ⟨_hInputMem, _hInputVarsDeep, hInputVarsFirstOrder⟩
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
      exact h_wf.2 k h_isSome
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
    | some e_s =>
        let qt_s : QTyp := ⟨ETyp.int, e_s.poison, e_s.pred⟩
        have hlookup_s' : s.locs.lookup l = some qt_s := by
          simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_s, Option.map]; rfl
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
        have hmem' : (l, qt_s) ∈ memEnvToLocQTypList s.locs := by
          rw [memEnvToLocQTypList, List.mem_map]
          refine ⟨(l, e_s), (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).2 hlookup_s, ?_⟩
          rfl
        have h_loc_regime : locsRegime predSat R μ θ (l, qt_s) :=
          h_locs_forall (l, qt_s) hmem'
        simpa [hqt] using h_loc_regime
  constructor
  · intro x qt k hlookup hguard hRdef
    have hk_in_tags : k ∈ inputSpecTags s := by
      have h_isSome : (R.lookup? k).isSome := by
        cases h : R.lookup? k with
        | none => exact False.elim (hRdef h)
        | some _b => simp
      exact h_wf.2 k h_isSome
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
  · -- Third conjunct: closureCapturedVarsRegime for all variable-value pairs.
    intro x qt v hlookup hlookup_v
    by_cases hkey : s.vars.hasKey x
    · -- Critical input variable: `wfInputSpec` restricts `s.vars` to first-order types,
      -- so closureCapturedVarsRegime follows from runtime typing via the non-closure case.
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
          have hnon_s : nonClosureQTyp qt_s := hInputVarsFirstOrder x qt_s hlookup_s'
          have hnon : nonClosureQTyp qt := by simpa [hqt] using hnon_s
          rcases h_ric.2 hlookup with ⟨v', hlookup_v', hvet⟩
          have hv' : v' = v := by
            have : (some v' : Option Value) = some v := by
              rw [← hlookup_v', hlookup_v]
            exact Option.some.inj this
          subst hv'
          have hnotfun : qt.etyp.isFunctionType = false := by
            cases qt with
            | mk etyp p pred =>
                cases etyp <;>
                  simp [nonClosureQTyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnon ⊢
          refine closureCapturedVarsRegime.intro ?_
          refine deepValueQTypProperty.nonClosure ?_ ?_
          · intro xp bd rc hval
            subst hval
            generalize het : qt.etyp = et at hvet hnotfun
            cases hvet with
            | closure =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
            | closure_extern =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
          · intro xp bd rc hval
            subst hval
            generalize het : qt.etyp = et at hvet hnotfun
            cases hvet with
            | peClosure =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
            | peClosure_extern =>
                simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
    · exact htrusted_init x qt v hlookup hkey hlookup_v

-- Step theorem (context-driven, no input/output specs).
-- It assumes agreement on clean items in the initial context and preserves it
-- for the post-context, plus result agreement when the result is clean under R.
-- `fuel` is the fuel of the typing of `e`. The extern calls of the two runs are
-- constrained through `ExternStepPremises`: `P₀` and `P₁` are sets of steps,
-- closed under `SubStep`, that contain the two root steps.
def StepFR
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning)
  (fuel : Nat)
  (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    PredSatLaws predSat tm →
    TagFrame predSat tm res.tagLog' →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ → wfRealizationMap θ₁ →
      wfTypeContext ctx →
      TagBoundedCtx ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ → runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      regimeConsistentWithCtx ctx →
      consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →
      consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
      agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } →
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } →
        RegistryReservedWF registry μ₀ a₀ →
        RegistryReservedWF registry μ₁ a₁ →
        ReservedDiscipline registry ctx.declaredExternRefs θ₀ →
        ReservedDiscipline registry ctx.declaredExternRefs θ₁ →
        terminatesTo e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ →
        terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ →
        ∀ {P₀ P₁ : Step → Prop}, ExternStepPremises predSat P₀ P₁ →
        P₀ ⟨ctx, e, fuel, { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }⟩ →
        P₁ ⟨ctx, e, fuel, { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }⟩ →
        StepFRPost ctx e res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

-- Step theorem spec derived from typing (context-driven).
-- No input/output specs here; they are handled by the top-level FR statement
-- and the bridge lemma.
def TypeSystemEnforcesFaultRobustness_step_spec
  (e : Expr)
  (ctxᵢ : TypeContext)
  (predSat : PredSat)
  (tm : TagMeaning)
  (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheck ctxᵢ e fuel = .ok res →
      StepFR ctxᵢ e res predSat tm fuel (registry := registry)

lemma valueHasETyp_loc_inv {θ : RealizationMap} {a : Address} {e : ETyp}
  (h : valueHasETyp θ (Value.loc a) e) : ∃ ls l, e = ETyp.ref ls ∧ θ.lookup l = some a ∧ l ∈ ls := by
  cases h with
  | loc hlookup hin => exact ⟨_, _, rfl, hlookup, hin⟩


lemma VarTypeEnv_lookup_of_toCaptured_lookup
    (σ : VarTypeEnv) (x : Name) (qt : QTyp) :
    (VarTypeEnv.toCaptured σ).lookup x = some qt →
    σ.lookup x = some qt := by
  intro hlookup
  have hmem : (x, qt) ∈ VarTypeEnv.toCaptured σ :=
    List_lookup_some_mem x qt (VarTypeEnv.toCaptured σ) (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  exact VarTypeEnv_lookup_of_toCaptured_mem σ x qt hmem

/-- Build direct member `varsRegime` facts for the singleton closure captured env
created at lambda typing sites, from the enclosing `consistentWithRegime`. -/
lemma memberVarsRegimeEvidence_of_toCaptured
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ) :
  MemberVarsRegimeEvidence predSat R μ (VarTypeEnv.toCaptured ctx.varEnv) ρ := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  have hlookup_list :
      (VarTypeEnv.toCaptured ctx.varEnv).lookup y = some qt_y :=
    list_lookup_of_ofCaptured_lookup (VarTypeEnv.toCaptured ctx.varEnv) y qt_y hlookup_σ
  exact hcwr.2.1 y qt_y k_y
    (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookup_list)
    hguard hkR

/-- Build direct member `closureCapturedVarsRegime` facts for the singleton closure
captured env created at lambda typing sites, from the enclosing `consistentWithRegime`. -/
lemma memberCvcrEvidence_of_toCaptured
  (predSat : PredSat) (R : Regime) (ctx : TypeContext)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ) :
  MemberCvcrEvidence predSat R μ θ (VarTypeEnv.toCaptured ctx.varEnv) ρ := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  have hlookup_list :
      (VarTypeEnv.toCaptured ctx.varEnv).lookup y = some qt_y :=
    list_lookup_of_ofCaptured_lookup (VarTypeEnv.toCaptured ctx.varEnv) y qt_y hlookup_σ
  exact hcwr.2.2 y qt_y v_y
    (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookup_list)
    hlookup_ρ

lemma capturedVarsTypingProperty_of_toCaptured
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
  capturedVarsTypingProperty θ (VarTypeEnv.toCaptured ctx.varEnv) ρ := by
  refine ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv, ?_, ?_⟩
  · intro y qt hlookup_σ
    have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookup_σ
    let ⟨v, hv, _⟩ := hric.2 hlookup_ctx
    exact ⟨v, hv⟩
  · intro y qt v hlookup_σ hlookup_ρ
    have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookup_σ
    let ⟨v', hv', htyp⟩ := hric.2 hlookup_ctx
    rw [hlookup_ρ] at hv'
    cases hv'
    exact htyp

-- Unary preservation: a single run preserves the value at an inherited clean location.
inductive PreservesInheritedCleanLocOneRun
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) (l : Loc) : Prop where
  | both_unrealized (h_in : θ_in.lookup l = none) (h_out : θ_out.lookup l = none)
  | preserve_value (a : Address) (n : Int)
      (h_in : θ_in.lookup l = some a) (h_mem_in : μ_in.lookup a = some n)
      (h_out : θ_out.lookup l = some a) (h_mem_out : μ_out.lookup a = some n)

lemma PreservesInheritedCleanLocOneRun.trans
  {μ₀ μ₁ μ₂ : Memory} {θ₀ θ₁ θ₂ : RealizationMap} {l : Loc}
  (h₀₁ : PreservesInheritedCleanLocOneRun μ₀ μ₁ θ₀ θ₁ l)
  (h₁₂ : PreservesInheritedCleanLocOneRun μ₁ μ₂ θ₁ θ₂ l) :
  PreservesInheritedCleanLocOneRun μ₀ μ₂ θ₀ θ₂ l := by
  cases h₀₁ with
  | both_unrealized hnone₀ hnone₁ =>
      cases h₁₂ with
      | both_unrealized hnone₁' hnone₂ =>
          exact .both_unrealized hnone₀ hnone₂
      | preserve_value _ _ hsome₁ _ _ _ =>
          exact nomatch (hnone₁.symm.trans hsome₁)
  | preserve_value a n hθ₀ hm₀ hθ₁ hm₁ =>
      cases h₁₂ with
      | both_unrealized hnone₁ _ =>
          exact nomatch (hθ₁.symm.trans hnone₁)
      | preserve_value a' n' hθ₁' hm₁' hθ₂ hm₂ =>
          have ha : a' = a := Option.some.inj (hθ₁'.symm.trans hθ₁)
          have hn : n' = n := by
            rw [ha] at hm₁'
            exact Option.some.inj (hm₁'.symm.trans hm₁)
          subst ha
          subst hn
          exact .preserve_value a' n' hθ₀ hm₀ hθ₂ hm₂

inductive PreservesInheritedFinalCleanLocsOneRun
  (ctx : TypeContext) (res : TypeResult)
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) : Prop where
  | intro (hpres : ∀ l qt_in qt_out,
      ctx.memEnv.lookup l = some qt_in →
      res.memEnv'.lookup l = some qt_out →
      qtypCleanUnder res.regime' qt_out →
      PreservesInheritedCleanLocOneRun μ_in μ_out θ_in θ_out l)

lemma PreservesInheritedFinalCleanLocsOneRun.apply
  {ctx : TypeContext} {res : TypeResult}
  {μ_in μ_out : Memory} {θ_in θ_out : RealizationMap}
  (hpres :
    PreservesInheritedFinalCleanLocsOneRun ctx res μ_in μ_out θ_in θ_out)
  {l : Loc} {qt_in qt_out : QTyp}
  (hlookup_in : ctx.memEnv.lookup l = some qt_in)
  (hlookup_out : res.memEnv'.lookup l = some qt_out)
  (hclean_out : qtypCleanUnder res.regime' qt_out) :
  PreservesInheritedCleanLocOneRun μ_in μ_out θ_in θ_out l := by
  rcases hpres with ⟨hpres⟩
  exact hpres l qt_in qt_out hlookup_in hlookup_out hclean_out

lemma PreservesInheritedFinalCleanLocsOneRun.refl
  {ctx : TypeContext} {res : TypeResult}
  {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
  PreservesInheritedFinalCleanLocsOneRun ctx res μ μ θ θ := by
  refine ⟨?_⟩
  intro l _qt_in _qt_out _hlookup_in _hlookup_out _hclean_out
  cases hθ : θ.lookup l with
  | none =>
      exact .both_unrealized hθ hθ
  | some a =>
      have hcontains_a : μ.contains a = true := (hric.1 l a hθ).2
      have hmem : a ∈ μ := (ExtTreeMap.contains_iff_mem).1 hcontains_a
      have hisSome : μ[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      cases hlookup_mem_raw : μ[a]? with
      | none =>
          simp [hlookup_mem_raw] at hisSome
      | some n =>
          have hlookup_mem : μ.lookup a = some n := by
            simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hlookup_mem_raw]
          exact .preserve_value a n hθ hlookup_mem hθ hlookup_mem

lemma PreservesInheritedFinalCleanLocsOneRun.compose
  {ctx : TypeContext} {res1 res2 : TypeResult}
  {μ₀ μ₁ μ₂ : Memory} {θ₀ θ₁ θ₂ : RealizationMap}
  (hclean_back :
    ∀ l qt_in qt_out,
      ctx.memEnv.lookup l = some qt_in →
      res2.memEnv'.lookup l = some qt_out →
      qtypCleanUnder res2.regime' qt_out →
      ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid)
  (hpres₀₁ : PreservesInheritedFinalCleanLocsOneRun ctx res1 μ₀ μ₁ θ₀ θ₁)
  (hpres₁₂ : PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res2 μ₁ μ₂ θ₁ θ₂) :
  PreservesInheritedFinalCleanLocsOneRun ctx res2 μ₀ μ₂ θ₀ θ₂ := by
  refine ⟨?_⟩
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  rcases hclean_back l qt_in qt_out hlookup_in hlookup_out hclean_out with
    ⟨qt_mid, hlookup_mid, hclean_mid⟩
  have hpres_mid :
      PreservesInheritedCleanLocOneRun μ₀ μ₁ θ₀ θ₁ l :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctx) (res := res1) (μ_in := μ₀) (μ_out := μ₁) (θ_in := θ₀) (θ_out := θ₁)
      hpres₀₁ hlookup_in hlookup_mid hclean_mid
  have hpres_final :
      PreservesInheritedCleanLocOneRun μ₁ μ₂ θ₁ θ₂ l :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctxAfter ctx res1) (res := res2)
      (μ_in := μ₁) (μ_out := μ₂) (θ_in := θ₁) (θ_out := θ₂)
      hpres₁₂
      (by simpa [ctxAfter] using hlookup_mid)
      hlookup_out
      hclean_out
  exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_final

/-- If a location is absent from the input typing context and clean in the
    output, then the chosen witness map does not realize it.
    This captures the invariant that fresh clean locations arise only from
    extern typing summaries that the runtime never executes. -/
def FreshCleanLocsUnrealizedOneRun
  (ctx : TypeContext) (res : TypeResult)
  (θ_out : RealizationMap) : Prop :=
  ∀ l qt,
    ¬ ctx.memEnv.contains l →
    res.memEnv'.lookup l = some qt →
    qtypCleanUnder res.regime' qt →
    θ_out.lookup l = none

/-- When `ctxAfter ctx res = ctx`, the context is unchanged, so `res.memEnv' = ctx.memEnv`.
    Any location absent from `ctx.memEnv` is also absent from `res.memEnv'`,
    making the lookup hypothesis contradictory. -/
lemma FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq
  {ctx : TypeContext} {res : TypeResult} {θ : RealizationMap}
  (hctxAfter : ctxAfter ctx res = ctx) :
  FreshCleanLocsUnrealizedOneRun ctx res θ := by
  intro l _qt hnotContains hlookup _hclean
  have hmemEq : res.memEnv' = ctx.memEnv := by
    have := congrArg TypeContext.memEnv hctxAfter
    simpa [ctxAfter] using this
  rw [hmemEq] at hlookup
  exact absurd (memEnv_contains_of_lookup_some ctx.memEnv l _qt hlookup) hnotContains

lemma singleRunFinalCleanWitness_of_same_state_maskedReg_param
  {masked : Tag → Prop}
  {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
  {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
  {ctx : TypeContext} {res : TypeResult}
  {_predSat : PredSat} {tm : TagMeaning}
  {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  {cf : Config} {o : Value}
  {a : Address} {pm : Bool}
  {registry : ExternRegistry}
  (hctxAfter : ctxAfter ctx res = ctx)
  (hcf : cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry})
  (hvaltyp : valueHasETyp θ o res.qualType.etyp)
  (hctxCons : CtxCons ctx μ ρ θ)
  (hvalc : ValCons ctx.regime res.qualType μ θ o)
  (_hwfTm : wfTagMeaningCtx tm ctx)
  (_hwf : wfTypeContext ctx)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (_hreg : regimeConsistentWithCtxMasked masked ctx)
  (_hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none)
  (_hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx)
  (_hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry})
  (hrd : ReservedDiscipline registry ctx.declaredExternRefs θ) :
  ∃ (θ' : RealizationMap),
    wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
    PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
    FreshCleanLocsUnrealizedOneRun ctx res θ' ∧
    ReservedDiscipline cf.registry res.declared' θ' := by
  refine ⟨θ, ?_, hvaltyp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ hlookup => hlookup, fun hθwf => hθwf⟩
  · simpa [hctxAfter, hcf] using hric
  · simpa [hctxAfter, hcf] using hctxCons
  · simpa [hctxAfter, hcf] using hvalc
  · simpa [hcf] using (PreservesInheritedFinalCleanLocsOneRun.refl (ctx := ctx) (res := res) (ρ := ρ) hric)
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter
  · have hdecl : res.declared' = ctx.declaredExternRefs := by
      have := congrArg TypeContext.declaredExternRefs hctxAfter
      simpa [ctxAfter] using this
    rw [hcf, hdecl]
    exact hrd

def StepFRSingleRunFinalCleanPcTruePost
  (ctx : TypeContext)
  (res : TypeResult)
  (predSat : PredSat)
  {registry : ExternRegistry}
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (cf : Config) (o : Value)
  (_hθwf : wfRealizationMap θ)
  (_hwf : wfTypeContext ctx)
  (_hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (_hreg : regimeConsistentWithCtx ctx)
  (_hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (_a : Address) (pm : Bool)
  (_hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := _a, pureMode := pm, registry := registry}) :
  Prop :=
  ∃ (θ' : RealizationMap),
    wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
      cf.memory cf.varEnv θ' ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType
      cf.memory θ' o ∧
    PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
    FreshCleanLocsUnrealizedOneRun ctx res θ' ∧
    ReservedDiscipline cf.registry res.declared' θ'

def StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctx : TypeContext)
  (res : TypeResult)
  {registry : ExternRegistry}
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (cf : Config) (o : Value)
  (_hθwf : wfRealizationMap θ)
  (_hwf : wfTypeContext ctx)
  (_hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (_hreg : regimeConsistentWithCtxMasked masked ctx)
  (_hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none)
  (_hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx)
  (_hmasked_bounded : ∀ k, masked k → k < ctx.nextTag)
  (_hbnd : TagBoundedCtx ctx)
  (_hctxCons : CtxCons ctx μ ρ θ)
  (_a : Address) (pm : Bool)
  (_hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := _a, pureMode := pm, registry := registry}) :
  Prop :=
  ∃ (θ' : RealizationMap),
    wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
    PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
    FreshCleanLocsUnrealizedOneRun ctx res θ' ∧
    ReservedDiscipline cf.registry res.declared' θ'

def StepFRSingleRunTagMeaningPost
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
  ∃ (tm' : TagMeaning),
    IsCanonicalExtension tm ctx e res tm' ∧
    PredSatLaws predSat tm' ∧
    QTypRespectsTagMeaning tm' res.qualType ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    WithinLog tm res.tagLog' tm'

theorem StepFRSingleRunTagMeaningPost.to_boundary
    {ctx : TypeContext} {e : Expr} {res : TypeResult} {predSat : PredSat} {tm : TagMeaning}
    (h : StepFRSingleRunTagMeaningPost ctx e res predSat tm) :
    ∃ tm', BoundaryTagMeaningPost ctx res predSat tm tm' := by
  rcases h with ⟨tm', hcanon, hlaws, _, _, hw⟩
  exact ⟨tm', BoundaryTagMeaningPost.of_isCanonical_predSat hcanon hlaws hw⟩

def StepFRSingleRunFinalCleanPcTrue
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning)
  (fuel : Nat)
  (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    PredSatLaws predSat tm →
    TagFrame predSat tm res.tagLog' →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    TagBoundedCtx ctx →
    StepFRSingleRunTagMeaningPost ctx e res predSat tm ∧
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      (hθwf : wfRealizationMap θ) →
      (hwf : wfTypeContext ctx) →
      (hric : runtimeInstantiatesCtx ctx μ ρ θ) →
      (hreg : regimeConsistentWithCtx ctx) →
      (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) →
      ∀ (a : Address) (pm : Bool),
        (hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry}) →
        RegistryReservedWF registry μ a →
        ReservedDiscipline registry ctx.declaredExternRefs θ →
        terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry} cf o →
        ctx.pc = true →
        ∀ {P : Step → Prop}, ExternCallsMatchOn predSat P →
        P ⟨ctx, e, fuel, { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry}⟩ →
        StepFRSingleRunFinalCleanPcTruePost ctx res predSat
          (registry := registry) μ ρ θ cf o
          hθwf hwf hric hreg hcwr a pm hwfcfg

def StepFRSingleRunFinalCleanPcTrueMaskedRegParam
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning)
  (fuel : Nat)
  (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    PredSatLaws predSat tm →
    TagFrame predSat tm res.tagLog' →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    StepFRSingleRunTagMeaningPost ctx e res predSat tm ∧
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      (hθwf : wfRealizationMap θ) →
      (hwf : wfTypeContext ctx) →
      (hric : runtimeInstantiatesCtx ctx μ ρ θ) →
      (hreg : regimeConsistentWithCtxMasked masked ctx) →
      (hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none) →
      (hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx) →
      (hmasked_bounded : ∀ k, masked k → k < ctx.nextTag) →
      (hbnd : TagBoundedCtx ctx) →
      (hctxCons : CtxCons ctx μ ρ θ) →
      ∀ (a : Address) (pm : Bool),
        (hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry}) →
        RegistryReservedWF registry μ a →
        ReservedDiscipline registry ctx.declaredExternRefs θ →
        terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry} cf o →
        ctx.pc = true →
        ∀ {P : Step → Prop}, ExternCallsMatchOn predSat P →
        P ⟨ctx, e, fuel, { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry}⟩ →
        StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
          masked CtxCons ValCons ctx res (registry := registry) μ ρ θ cf o
          hθwf hwf hric hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg

-- Helper lemmas: transport predicate-based properties across qualified types
-- that differ only in irrelevant fields (e.g. poison), but share the same predicate.

private lemma qtypGuardTag_of_pred_eq {qt qt' : QTyp}
  (hpred : qt.pred = qt'.pred) :
  qtypGuardTag qt = qtypGuardTag qt' := by
  cases qt with
  | mk et p pred =>
    cases qt' with
    | mk et' p' pred' =>
      -- qtypGuardTag depends only on the predicate field
      simp [qtypGuardTag] at hpred ⊢
      cases hpred
      rfl

lemma qtypPredHolds_transport_pred
  {predSat : PredSat} {qt qt' : QTyp} {μ : Memory} {v : Value}
  (hpred : qt.pred = qt'.pred) :
  qtypPredHolds predSat qt μ v → qtypPredHolds predSat qt' μ v := by
  intro h
  cases h with
  | noPred_ok hnp =>
      refine qtypPredHolds.noPred_ok (qt := qt') ?_
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.noPred := by exact hnp
  | guardClosure_ok hclos hsat =>
      rename_i k arg_name pred_body var_env
      refine qtypPredHolds.guardClosure_ok (qt := qt') (k := k) (arg_name := arg_name)
        (pred_body := pred_body) (var_env := var_env) ?_ hsat
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardClosure k arg_name pred_body var_env := by exact hclos
  | guardOnly_ok hgo hsat =>
      rename_i k
      refine qtypPredHolds.guardOnly_ok (qt := qt') (k := k) ?_ hsat
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := by exact hgo

lemma qtypPredHolds_transport_pred_not
  {predSat : PredSat} {qt qt' : QTyp} {μ : Memory} {v : Value}
  (hpred : qt.pred = qt'.pred) :
  (¬ qtypPredHolds predSat qt μ v) → (¬ qtypPredHolds predSat qt' μ v) := by
  intro hnot hholds
  -- Transport back to `qt` and contradict.
  have hback : qtypPredHolds predSat qt μ v :=
    qtypPredHolds_transport_pred (predSat := predSat) (qt := qt') (qt' := qt) (μ := μ) (v := v) (by simp [hpred]) hholds
  exact hnot hback

lemma predSat_mem_noPred_compat
  {predSat : PredSat} {tm : TagMeaning}
  (hpredlaws : PredSatLaws predSat tm)
  (θ : RealizationMap) :
  ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
  intro k μ μ' v
  exact
    hpredlaws.mem_monotone (k := k) (pred := Predicate.noPred) (fuel := 0) (μ := μ) (μ' := μ') (v := v)
      (deps := LocSet.empty) (θ := θ) (by simp [extractDepsFromPred, pure, Except.pure])
      (by intro l hl; cases hl)

lemma qtypPredHolds_mem_compat_of_predSatLaws
  {predSat : PredSat} {tm : TagMeaning}
  (hpredlaws : PredSatLaws predSat tm)
  (θ : RealizationMap) (μ μ' : Memory) :
  ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v := by
  have hPredSat_mem :
      ∀ (k : Tag) (μ₀ μ₁ : Memory) (v : Value), predSat k μ₀ v ↔ predSat k μ₁ v := by
    intro k μ₀ μ₁ v
    exact predSat_mem_noPred_compat hpredlaws θ k μ₀ μ₁ v
  intro qt v
  constructor <;> intro h
  · cases h with
    | noPred_ok hp =>
        exact qtypPredHolds.noPred_ok hp
    | guardClosure_ok hp hs =>
        exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem _ _ _ v).1 hs)
    | guardOnly_ok hp hs =>
        exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem _ _ _ v).1 hs)
  · cases h with
    | noPred_ok hp =>
        exact qtypPredHolds.noPred_ok hp
    | guardClosure_ok hp hs =>
        exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem _ _ _ v).2 hs)
    | guardOnly_ok hp hs =>
        exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem _ _ _ v).2 hs)

lemma not_qtypCleanUnder_of_poison_true_noPred
  {R : Regime} {qt : QTyp}
  (hpoison : qt.poison = true)
  (hpred : qt.pred = Predicate.noPred) :
  ¬ qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison' =>
      simp [hpoison] at hpoison'
  | guard _ htag _ _ =>
      simp [qtypGuardTag, hpred] at htag


-- Monotonicity of capturedVarsRegimeProperty under Regime.monotoneStep.
private lemma capturedVarsRegimeProperty_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  have hkR : R.lookup? k_x ≠ none := fun habs => h_mono.2 k_x hkR' habs
  have hvr_R := h x qt_x k_x hlook hguard hkR
  obtain ⟨b, hb⟩ : ∃ b, R.lookup? k_x = some b := by
    cases h_eq : R.lookup? k_x with
    | none => exact absurd h_eq hkR
    | some b => exact ⟨b, rfl⟩
  cases h_mono.1 k_x b hb with
  | inl hk'_eq => exact varsRegime_monotone h_mono hguard hk'_eq hvr_R
  | inr hk'_none => exact absurd hk'_none hkR'

/-- Extended-regime variant: a captured var's guard tag that is defined in `R'` must be old
    (`¬ newTags`), so `.2` of `monotoneStepExt` still yields `R.lookup? k_x ≠ none`.  The
    `hfresh` discharge at use sites comes from `closureEnvBoundedInCtx`/`TagBoundedCtx`
    (captured-var tags are `< nextTag` while `newTags = fun k => nextTag ≤ k`). -/
private lemma capturedVarsRegimeProperty_monotoneExt
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {newTags : Tag → Prop}
  (h_mono : Regime.monotoneStepExt R R' newTags)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (hfresh : ∀ x qt_x k_x, σcap.lookup x = some qt_x → qtypGuardTag qt_x = some k_x → ¬ newTags k_x)
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  have hkR : R.lookup? k_x ≠ none := by
    rcases h_mono.2 k_x hkR' with h2 | h2
    · exact h2
    · exact absurd h2 (hfresh x qt_x k_x hlook hguard)
  have hvr_R := h x qt_x k_x hlook hguard hkR
  obtain ⟨b, hb⟩ : ∃ b, R.lookup? k_x = some b := by
    cases h_eq : R.lookup? k_x with
    | none => exact absurd h_eq hkR
    | some b => exact ⟨b, rfl⟩
  cases h_mono.1 k_x b (hfresh x qt_x k_x hlook hguard) hb with
  | inl hk'_eq =>
      exact varsRegime_monotoneExt h_mono hguard (hfresh x qt_x k_x hlook hguard) hk'_eq hvr_R
  | inr hk'_none => exact absurd hk'_none hkR'

section RegimeTransport
variable {predSat : PredSat} {R R' : Regime} {μ : Memory}

lemma closureCapturedVarsRegime_monotone
  {qt : QTyp} {θ : RealizationMap} {v : Value}
  (h_mono : Regime.monotoneStep R R')
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R' qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ => ⟨capturedVarsRegimeProperty_monotone h_mono hP, hT⟩)
        hdeep)

-- Extended-regime (monotoneStepExt) deep transport of the closure-captured regime/typing
-- property.  At each closure level the per-variable freshness `¬ newTags k_x` is discharged
-- from the existing deep type bound `etypClosuresFullBounded qt.etyp B` (captured guard tags
-- are `< B`, while `newTags k → B ≤ k`).
private lemma deepValueQTypProperty_capturedVarsRegime_monotoneExt
    {θ : RealizationMap} {newTags : Tag → Prop} {B : Tag}
    (h_mono : Regime.monotoneStepExt R R' newTags)
    (hnewB : ∀ k, newTags k → B ≤ k)
    {qt : QTyp} {v : Value}
    (hdeep : deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R μ σcap ρcap ∧ capturedVarsTypingProperty θ σcap ρcap) qt v) :
    etypClosuresFullBounded qt.etyp B →
    deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R' μ σcap ρcap ∧ capturedVarsTypingProperty θ σcap ρcap) qt v := by
  induction hdeep with
  | nonClosure hv hpe => intro _; exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem hPT _hrec _hbody ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2
        simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      refine .closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem
        ⟨capturedVarsRegimeProperty_monotoneExt h_mono ?_ hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
        _hbody
      intro x qt_x k_x hlook hg hnt
      exact absurd (hnewB k_x hnt) (Nat.not_le.2
        (CapturedEnvFullBounded_guardTag_lt hσbound (List_lookup_some_mem x qt_x σcap hlook) hg))
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2
        simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      refine .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem
        ⟨capturedVarsRegimeProperty_monotoneExt h_mono ?_ hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
      intro x qt_x k_x hlook hg hnt
      exact absurd (hnewB k_x hnt) (Nat.not_le.2
        (CapturedEnvFullBounded_guardTag_lt hσbound (List_lookup_some_mem x qt_x σcap hlook) hg))
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem hPT _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2
        simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      refine .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem
        ⟨capturedVarsRegimeProperty_monotoneExt h_mono ?_ hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
      intro x qt_x k_x hlook hg hnt
      exact absurd (hnewB k_x hnt) (Nat.not_le.2
        (CapturedEnvFullBounded_guardTag_lt hσbound (List_lookup_some_mem x qt_x σcap hlook) hg))
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2
        simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      refine .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem
        ⟨capturedVarsRegimeProperty_monotoneExt h_mono ?_ hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
      intro x qt_x k_x hlook hg hnt
      exact absurd (hnewB k_x hnt) (Nat.not_le.2
        (CapturedEnvFullBounded_guardTag_lt hσbound (List_lookup_some_mem x qt_x σcap hlook) hg))

/-- Extended-regime variant of `closureCapturedVarsRegime_monotone`: transports closure-captured
    regime consistency across a `monotoneStepExt` step, discharging captured-tag freshness from
    the deep type bound `etypClosuresFullBounded qt.etyp B`. -/
lemma closureCapturedVarsRegime_monotoneExt
    {qt : QTyp} {θ : RealizationMap} {v : Value} {newTags : Tag → Prop} {B : Tag}
    (h_mono : Regime.monotoneStepExt R R' newTags)
    (hnewB : ∀ k, newTags k → B ≤ k)
    (hbound : etypClosuresFullBounded qt.etyp B)
    (h : closureCapturedVarsRegime predSat R qt μ θ v) :
    closureCapturedVarsRegime predSat R' qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_capturedVarsRegime_monotoneExt h_mono hnewB hdeep hbound)

-- Lookup-back transport helpers used by both the `ite` and join transport proofs.
lemma varsRegime_transport_active_lookup_back
  {ρ : VarEnv}
  {entry : Name × QTyp} {k : Tag} {b : Bool}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  (hguard : qtypGuardTag entry.snd = some k)
  (hreg' : R'.lookup? k = some b)
  (h : varsRegime predSat R μ ρ entry) :
  varsRegime predSat R' μ ρ entry := by
  cases h with
  | noPred_ok hpred =>
      rw [hpred] at hguard
      cases hguard
  | guardOnly_ok k' hgo =>
      exact varsRegime.guardOnly_ok entry k' hgo
  | withPred_ok k' arg_name pred_body var_env v b' hclos hreg hvar hcons =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag entry.snd := by simp [qtypGuardTag, hclos]
            _ = some k := hguard
        exact Option.some.inj this
      have hreg_back : R.lookup? k = some b := hlookup_back k b hreg'
      have hb_eq : b' = b := by
        have : some b' = some b := by
          calc
            some b' = R.lookup? k' := by symm; exact hreg
            _ = R.lookup? k := by simp [hk_eq]
            _ = some b := hreg_back
        exact Option.some.inj this
      have hreg'' : R'.lookup? k' = some b' := by
        simp [hk_eq, hb_eq] at hreg' ⊢
        exact hreg'
      exact varsRegime.withPred_ok entry k' arg_name pred_body var_env v b' hclos hreg'' hvar hcons

private lemma capturedVarsRegimeProperty_transport_lookup_back
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  cases hkR'some : R'.lookup? k_x with
  | none =>
      exact (hkR' hkR'some).elim
  | some b =>
      have hkR : R.lookup? k_x ≠ none := by
        intro hnone
        have hback := hlookup_back k_x b hkR'some
        simp [hnone] at hback
      have hvr_R := h x qt_x k_x hlook hguard hkR
      exact
        varsRegime_transport_active_lookup_back
          (predSat := predSat) (R := R) (R' := R')
          (μ := μ) (ρ := ρcap) (entry := (x, qt_x))
          hlookup_back hguard hkR'some hvr_R

lemma closureCapturedVarsRegime_transport_lookup_back
  {qt : QTyp} {θ : RealizationMap} {v : Value}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R' qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ =>
          ⟨capturedVarsRegimeProperty_transport_lookup_back
            (predSat := predSat) (R := R) (R' := R') (μ := μ)
            hlookup_back hP, hT⟩)
        hdeep)

lemma memberVarsRegimeEvidence_transport_lookup_back
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R' μ σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR'
  cases hkR'some : R'.lookup? k_y with
  | none =>
      exact (hkR' hkR'some).elim
  | some b =>
      have hkR : R.lookup? k_y ≠ none := by
        intro hnone
        have hback := hlookup_back k_y b hkR'some
        simp [hnone] at hback
      have hvr_R :
          varsRegime predSat R μ ρcap (y, qt_y) :=
        h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
      exact
        varsRegime_transport_active_lookup_back
          (predSat := predSat) (R := R) (R' := R')
          (μ := μ) (ρ := ρcap) (entry := (y, qt_y))
          hlookup_back hguard hkR'some hvr_R

lemma memberCvcrEvidence_transport_lookup_back
  {θ : RealizationMap}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R' μ θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_transport_lookup_back
      (predSat := predSat) (R := R) (R' := R') (μ := μ)
      hlookup_back (h y qt_y v_y hlookup_σ hlookup_ρ)

-- Transport closureCapturedVarsRegime across qt.etyp equality.
lemma closureCapturedVarsRegime_transport_etyp
  {qt qt' : QTyp} {θ : RealizationMap} {v : Value}
  (hetyp : qt.etyp = qt'.etyp)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt' μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure xp body ρcap σcap st1 st2 p tcls hval hetyp_eq hmem hP hrec hbody =>
          exact .closure xp body ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hmem hP hrec hbody
      | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp_eq hmem hP hrec =>
          exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls
            hval (hetyp ▸ hetyp_eq) hmem hP hrec
      | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp_eq hpure hmem hP hrec =>
          exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hpure hmem hP hrec
      | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp_eq hmem hP hrec =>
          exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls
            hval (hetyp ▸ hetyp_eq) hmem hP hrec

end RegimeTransport

-- Weaken closureCapturedVarsRegime when the closure list grows (superset).
-- Used when joining type results: mergeFnTClosures produces a superset.

-- Weaken with different inner poison (joinETyps changes p to joinPoison p1 p2).
private lemma closureCapturedVarsRegime_weaken_fnTClosures'
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List FnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.arrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure xp body ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hmem_src hP hrec hbody =>
          have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .closure xp body ρcap σcap st1 st2 p' tcls' hval rfl (hmem _ hmem_src) hP hrec hbody
      | closure_extern id xp y argTyp retSpec effects ρcap σcap _p tcls_src hval hetyp_eq hmem_src hP hrec =>
          have heq_arg : argTyp = st1 := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.1).symm
          have heq_ret : parseReturnType retSpec = st2 := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.1).symm
          have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p' tcls'
            hval (by simp [heq_arg, heq_ret]) (hmem _ hmem_src) hP hrec
      | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_eq_parr _ _ =>
          exfalso
          simp at hetyp_eq_parr
      | peClosure_extern _id _xp _y _argTyp _retSpec _ρcap _σcap _p _tcls _hval hetyp_eq_parr _hmem _hP _hrec =>
          exfalso
          simp at hetyp_eq_parr

-- Analogous for parrow/PFnTClosure.

-- Weaken parrow with different inner poison (joinETyps changes p).
private lemma closureCapturedVarsRegime_weaken_pFnTClosures'
  {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List PFnTClosure} {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨ETyp.parrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | intro hdeep =>
      refine .intro ?_
      cases hdeep with
      | nonClosure hv hpe => exact .nonClosure hv hpe
      | closure _ _ _ _ _ _ _ _ _ hetyp_eq_arr _ _ =>
          exfalso
          simp at hetyp_eq_arr
      | closure_extern _id _xp _y _argTyp _retSpec _effects _ρcap _σcap _p _tcls _hval hetyp_eq_arr _hmem _hP _hrec =>
          exfalso
          simp at hetyp_eq_arr
      | peClosure xp body pbody ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hpure hmem_src hP hrec =>
          have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .peClosure xp body pbody ρcap σcap st1 st2 p' tcls' hval rfl hpure (hmem _ hmem_src) hP hrec
      | peClosure_extern id xp y argTyp retSpec ρcap σcap _p tcls_src hval hetyp_eq hmem_src hP hrec =>
          have heq_arg : argTyp = st1 := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.1).symm
          have heq_ret : parseReturnType retSpec = st2 := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.1).symm
          have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
          subst heq_tcls
          exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p' tcls'
            hval (by simp [heq_arg, heq_ret]) (hmem _ hmem_src) hP hrec

-- Single-step: transport closureCapturedVarsRegime across one joinETyps application.
lemma closureCapturedVarsRegime_joinETyps_step
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegime predSat R ⟨etyp1, p1, pr1⟩ μ θ v) :
  closureCapturedVarsRegime predSat R
    ⟨joinETyps etyp1 resEtyp p1 resPoison,
      joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases etyp1 with
  | int | bool | unit | string =>
      simp [joinETyps]
      exact closureCapturedVarsRegime_transport_etyp (by simp) hcap
  | ref ls =>
      cases resEtyp with
      | ref ls2 =>
          simp only [beqETypSignature] at hcompat
          cases hcap with
          | intro hdeep =>
              cases hdeep with
              | nonClosure hv hpe => exact .intro (.nonClosure hv hpe)
              | closure _ _ _ _ _ _ _ _ _ hetyp_arr _ _ => exfalso; exact ETyp.noConfusion hetyp_arr
              | closure_extern _ _ _ _ _ _ _ _ _ _ _ hetyp_arr _ _ _ => exfalso; exact ETyp.noConfusion hetyp_arr
              | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_parr _ _ => exfalso; exact ETyp.noConfusion hetyp_parr
              | peClosure_extern _ _ _ _ _ _ _ _ _ _ hetyp_parr _ _ _ => exfalso; exact ETyp.noConfusion hetyp_parr
      | _ => simp [beqETypSignature] at hcompat
  | arrow st1 st2 p tcls =>
      have hisArrow : resEtyp.isArrow := by
        cases resEtyp with
        | arrow => rfl
        | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_arrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisArrow hcompat
      have hcap' :=
        closureCapturedVarsRegime_weaken_fnTClosures'
          (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegime_transport_etyp heq.symm hcap'
  | parrow st1 st2 p tcls =>
      have hisParrow : resEtyp.isParrow := by
        cases resEtyp with
        | parrow => rfl
        | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_parrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisParrow hcompat
      have hcap' :=
        closureCapturedVarsRegime_weaken_pFnTClosures'
          (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegime_transport_etyp heq.symm hcap'

-- Single-step: transport closureCapturedVarsRegime from the RIGHT argument of joinETyps.
lemma closureCapturedVarsRegime_joinETyps_step_right
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegime predSat R ⟨resEtyp, resPoison, resPred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R
    ⟨joinETyps etyp1 resEtyp p1 resPoison,
      joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases hcap with
  | intro hdeep =>
      cases hdeep with
      | nonClosure hv hpe =>
          exact .intro (.nonClosure hv hpe)
      | closure x body ρcap σcap st1r st2r pr tclr hval hetyp_r htcl hP hrec hbody =>
          have hetyp_r' : resEtyp = ETyp.arrow st1r st2r pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.closure x body ρcap σcap st1l st2l pr tclr
                    hval rfl htcl hP hrec hbody))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l st2l (joinPoison pl pr) (mergeFnTClosures tclsl tclr),
                      resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_fnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := st2l) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergeFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergeFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.arrow st1l st2l pl tclsl) (ETyp.arrow st1l st2l pr tclr)
                    p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join
          | parrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
      | closure_extern id x y argTyp retSpec effects ρcap σcap pr tclr hval hetyp_r htcl hP hrec =>
          have hetyp_r' : resEtyp = ETyp.arrow argTyp (parseReturnType retSpec) pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l (parseReturnType retSpec) pr tclr,
                      resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.closure_extern id x y st1l retSpec effects ρcap σcap pr tclr
                    hval rfl htcl hP hrec))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l (parseReturnType retSpec) (joinPoison pl pr)
                      (mergeFnTClosures tclsl tclr), resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_fnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := parseReturnType retSpec) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergeFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergeFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.arrow st1l (parseReturnType retSpec) pl tclsl)
                    (ETyp.arrow st1l (parseReturnType retSpec) pr tclr) p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join
          | parrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
      | peClosure x body pbody ρcap σcap st1r st2r pr tclr hval hetyp_r hpure htcl hP hrec =>
          have hetyp_r' : resEtyp = ETyp.parrow st1r st2r pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
          | parrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.peClosure x body pbody ρcap σcap st1l st2l pr tclr
                    hval rfl hpure htcl hP hrec))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l st2l (joinPoison pl pr) (mergePFnTClosures tclsl tclr),
                      resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_pFnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := st2l) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergePFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergePFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.parrow st1l st2l pl tclsl) (ETyp.parrow st1l st2l pr tclr)
                    p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join
      | peClosure_extern id x y argTyp retSpec ρcap σcap pr tclr hval hetyp_r htcl hP hrec =>
          have hetyp_r' : resEtyp = ETyp.parrow argTyp (parseReturnType retSpec) pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
          | parrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l (parseReturnType retSpec) pr tclr,
                      resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.peClosure_extern id x y st1l retSpec ρcap σcap pr tclr
                    hval rfl htcl hP hrec))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l (parseReturnType retSpec) (joinPoison pl pr)
                      (mergePFnTClosures tclsl tclr), resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_pFnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := parseReturnType retSpec) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergePFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergePFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.parrow st1l (parseReturnType retSpec) pl tclsl)
                    (ETyp.parrow st1l (parseReturnType retSpec) pr tclr) p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join

-- Extract closureCapturedVarsRegime evidence from valueConsistentWithRegime.
lemma valueConsistentWithRegime_closureCapturedVarsRegime
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ θ v := by
  cases h with
  | noTag _ hcap => exact hcap
  | guardOnly_ok _k _ hcap => exact hcap
  | notInRegime _k _ _ hcap => exact hcap
  | inRegimeTrue _k _ _ _ hcap => exact hcap
  | inRegimeFalse _k _ _ _ hcap => exact hcap

private def capturedVarsRegimePropertyMasked
    (masked : Tag → Prop) (predSat : PredSat) (R : Regime) (μ : Memory)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ (x : Name) (qt_x : QTyp) (k_x : Tag),
    σcap.lookup x = some qt_x →
    qtypGuardTag qt_x = some k_x →
    R.lookup? k_x ≠ none →
    masked k_x ∨ varsRegime predSat R μ ρcap (x, qt_x)

def closureCapturedVarsRegimeMasked
    (masked : Tag → Prop) (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop :=
  deepValueQTypProperty
    (fun σcap ρcap =>
      capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap ∧
      capturedVarsTypingProperty θ σcap ρcap)
    qt v

def consistentWithRegimeMasked
    (masked : Tag → Prop) (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l qt k, ctx.memEnv.lookup l = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     masked k ∨ locsRegime predSat R μ θ (l, qt)) ∧
  (∀ x qt k, ctx.varEnv.lookup x = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     masked k ∨ varsRegime predSat R μ ρ (x, qt)) ∧
  (∀ x qt v, ctx.varEnv.lookup x = some qt →
     ρ.lookup x = some v →
     closureCapturedVarsRegimeMasked masked predSat R qt μ θ v)

inductive valueConsistentWithRegimeMasked
    (masked : Tag → Prop) (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | noTag
      (htag : qtypGuardTag qt = none)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v
  | guardOnly_ok (k : Tag)
      (hgo : qt.pred = Predicate.guardOnly k)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v
  | maskedTag (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hmasked : masked k)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v
  | notInRegime (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hknone : R.lookup? k = none)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v
  | inRegimeFalse (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hkfalse : R.lookup? k = some false)
      (hnot : ¬ qtypPredHolds predSat qt μ v)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v
  | inRegimeTrue (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hktrue : R.lookup? k = some true)
      (hholds : qtypPredHolds predSat qt μ v)
      (hcap : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v

lemma closureCapturedVarsRegimeMasked_transport_etyp
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hetyp : qt.etyp = qt'.etyp)
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R qt' μ θ v := by
  cases h with
  | nonClosure hv hpe =>
      exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp_eq hmem hP hrec hbody =>
      exact .closure xp body ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hmem hP hrec hbody
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp_eq hmem hP hrec =>
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls
        hval (hetyp ▸ hetyp_eq) hmem hP hrec
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp_eq hpure hmem hP hrec =>
      exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval (hetyp ▸ hetyp_eq) hpure hmem hP hrec
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp_eq hmem hP hrec =>
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls
        hval (hetyp ▸ hetyp_eq) hmem hP hrec

lemma valueConsistentWithRegimeMasked_closureCapturedVarsRegime
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : valueConsistentWithRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R qt μ θ v := by
  cases h with
  | noTag _ hcap => exact hcap
  | guardOnly_ok _ _ hcap => exact hcap
  | maskedTag _ _ _ hcap => exact hcap
  | notInRegime _ _ _ hcap => exact hcap
  | inRegimeFalse _ _ _ _ hcap => exact hcap
  | inRegimeTrue _ _ _ _ hcap => exact hcap

private lemma capturedVarsRegimePropertyMasked_unmask
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ : Memory}
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (hmasked_none : ∀ k, masked k → R.lookup? k = none)
  (h :
    capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R μ σcap ρcap := by
  intro x qt_x k_x hlookup hguard hRdef
  specialize h x qt_x k_x hlookup hguard hRdef
  rcases h with hmasked | hvars
  · exact False.elim (hRdef (hmasked_none k_x hmasked))
  · exact hvars

private lemma closureCapturedVarsRegimeMasked_unmask
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hmasked_none : ∀ k, masked k → R.lookup? k = none)
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ θ v := by
  exact
    .intro <|
      deepValueQTypProperty_mono
        (fun _ _ hP =>
          ⟨capturedVarsRegimePropertyMasked_unmask
              (masked := masked) (predSat := predSat)
              (R := R) (μ := μ) hmasked_none hP.1,
            hP.2⟩)
        h

lemma consistentWithRegimeMasked_unmask
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  (hmasked_none : ∀ k, masked k → R.lookup? k = none)
  (h : consistentWithRegimeMasked masked predSat R ctx μ ρ θ) :
  consistentWithRegime predSat R ctx μ ρ θ := by
  rcases h with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    specialize hlocs l qt k hlookup hguard hRdef
    rcases hlocs with hmasked | hloc
    · exact False.elim (hRdef (hmasked_none k hmasked))
    · exact hloc
  · intro x qt k hlookup hguard hRdef
    specialize hvars x qt k hlookup hguard hRdef
    rcases hvars with hmasked | hvar
    · exact False.elim (hRdef (hmasked_none k hmasked))
    · exact hvar
  · intro x qt v hlookup hρ
    exact closureCapturedVarsRegimeMasked_unmask
      (masked := masked) (predSat := predSat)
      (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
      hmasked_none
      (hclos x qt v hlookup hρ)

lemma valueConsistentWithRegimeMasked_unmask
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hmasked_none : ∀ k, masked k → R.lookup? k = none)
  (h : valueConsistentWithRegimeMasked masked predSat R qt μ θ v) :
  valueConsistentWithRegime predSat R qt μ θ v := by
  cases h with
  | noTag htag hcap =>
      exact valueConsistentWithRegime.noTag htag
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)
  | guardOnly_ok k hgo hcap =>
      exact valueConsistentWithRegime.guardOnly_ok k hgo
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)
  | maskedTag k htag hmasked hcap =>
      exact valueConsistentWithRegime.notInRegime k htag
        (hmasked_none k hmasked)
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)
  | notInRegime k htag hknone hcap =>
      exact valueConsistentWithRegime.notInRegime k htag hknone
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)
  | inRegimeFalse k htag hkfalse hnot hcap =>
      exact valueConsistentWithRegime.inRegimeFalse k htag hkfalse hnot
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)
  | inRegimeTrue k htag hktrue hholds hcap =>
      exact valueConsistentWithRegime.inRegimeTrue k htag hktrue hholds
        (closureCapturedVarsRegimeMasked_unmask
          (masked := masked) (predSat := predSat)
          (R := R) (qt := qt) (μ := μ) (θ := θ) (v := v)
          hmasked_none hcap)

private lemma capturedVarsRegimeProperty_to_masked
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ : Memory}
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap := by
  intro x qt_x k_x hlookup hguard hRdef
  exact Or.inr (h x qt_x k_x hlookup hguard hRdef)

private lemma closureCapturedVarsRegime_to_masked
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R qt μ θ v := by
  cases h with
  | intro hdeep =>
      exact
        deepValueQTypProperty_mono
          (fun _ _ hP => ⟨capturedVarsRegimeProperty_to_masked hP.1, hP.2⟩)
          hdeep

lemma consistentWithRegime_to_masked
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
  (h : consistentWithRegime predSat R ctx μ ρ θ) :
  consistentWithRegimeMasked masked predSat R ctx μ ρ θ := by
  rcases h with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    exact Or.inr (hlocs l qt k hlookup hguard hRdef)
  · intro x qt k hlookup hguard hRdef
    exact Or.inr (hvars x qt k hlookup hguard hRdef)
  · intro x qt v hlookup hρ
    exact closureCapturedVarsRegime_to_masked (masked := masked) (hclos x qt v hlookup hρ)

lemma valueConsistentWithRegime_to_masked
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  valueConsistentWithRegimeMasked masked predSat R qt μ θ v := by
  cases h with
  | noTag htag hcap =>
      exact valueConsistentWithRegimeMasked.noTag htag
        (closureCapturedVarsRegime_to_masked (masked := masked) hcap)
  | guardOnly_ok k hgo hcap =>
      exact valueConsistentWithRegimeMasked.guardOnly_ok k hgo
        (closureCapturedVarsRegime_to_masked (masked := masked) hcap)
  | notInRegime k htag hknone hcap =>
      exact valueConsistentWithRegimeMasked.notInRegime k htag hknone
        (closureCapturedVarsRegime_to_masked (masked := masked) hcap)
  | inRegimeTrue k htag hktrue hholds hcap =>
      exact valueConsistentWithRegimeMasked.inRegimeTrue k htag hktrue hholds
        (closureCapturedVarsRegime_to_masked (masked := masked) hcap)
  | inRegimeFalse k htag hkfalse hnot hcap =>
      exact valueConsistentWithRegimeMasked.inRegimeFalse k htag hkfalse hnot
        (closureCapturedVarsRegime_to_masked (masked := masked) hcap)

-- For guard-closure predicates, `valueConsistentWithRegime` determines the same
-- predicate-consistency obligation needed by `varsRegime.withPred_ok`.
lemma valueConsistentWithRegime_guardClosure_consistency
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv} {b : Bool}
  (hvalc : valueConsistentWithRegime predSat R qt μ θ v)
  (hpred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
  (hreg : R.lookup? k = some b) :
  (b = true → qtypPredHolds predSat qt μ v) ∧
  (b = false → ¬ qtypPredHolds predSat qt μ v) := by
  cases hvalc with
  | noTag htag _ =>
      have : qtypGuardTag qt = some k := by
        simp [qtypGuardTag, hpred]
      simp [this] at htag
  | guardOnly_ok k' hgo _ =>
      simp [hpred] at hgo
  | notInRegime k' htag hnone _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have : R.lookup? k = none := by simpa [hk_eq] using hnone
      simp [this] at hreg
  | inRegimeTrue k' htag hk hholds _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hk_true : R.lookup? k = some true := by simpa [hk_eq] using hk
      constructor
      · intro hbtrue
        have hb_eq_true : b = true := by
          have : some b = some true := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some true := hk_true
          exact Option.some.inj this
        subst hb_eq_true
        exact hholds
      · intro hbfalse
        have hb_eq_true : b = true := by
          have : some b = some true := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some true := hk_true
          exact Option.some.inj this
        have : true = false := hb_eq_true.symm.trans hbfalse
        cases this
  | inRegimeFalse k' htag hk hnot _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hk_false : R.lookup? k = some false := by simpa [hk_eq] using hk
      constructor
      · intro hbtrue
        have hb_eq_false : b = false := by
          have : some b = some false := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some false := hk_false
          exact Option.some.inj this
        have : false = true := hb_eq_false.symm.trans hbtrue
        cases this
      · intro hbfalse
        have hb_eq_false : b = false := by
          have : some b = some false := by
            calc
              some b = R.lookup? k := by symm; exact hreg
              _ = some false := hk_false
          exact Option.some.inj this
        subst hb_eq_false
        exact hnot

lemma varsRegime_of_valueConsistentWithRegimeMasked_active
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ : Memory}
  {θ : RealizationMap} {ρ : VarEnv}
  {x : Name} {qt : QTyp} {v : Value} {k : Tag}
  (hlookup : ρ.lookup x = some v)
  (hguard : qtypGuardTag qt = some k)
  (hRdef : R.lookup? k ≠ none)
  (hvalc : valueConsistentWithRegimeMasked masked predSat R qt μ θ v) :
  masked k ∨ varsRegime predSat R μ ρ (x, qt) := by
  cases hpred : qt.pred with
  | noPred =>
      simp [qtypGuardTag, hpred] at hguard
  | guardOnly k0 =>
      exact Or.inr (varsRegime.guardOnly_ok (x, qt) k0 hpred)
  | guardClosure k0 arg_name pred_body var_env =>
      have hk0_eq : k0 = k := by
        have htag0 : qtypGuardTag qt = some k0 := by
          simp [qtypGuardTag, hpred]
        have : some k0 = some k := by
          calc
            some k0 = qtypGuardTag qt := by symm; exact htag0
            _ = some k := hguard
        exact Option.some.inj this
      cases hlookupR : R.lookup? k0 with
      | none =>
          have : R.lookup? k = none := by simpa [hk0_eq] using hlookupR
          exact False.elim (hRdef this)
      | some b =>
          cases hvalc with
          | noTag htag _ =>
              have : qtypGuardTag qt = some k0 := by simp [qtypGuardTag, hpred]
              simp [this] at htag
          | guardOnly_ok k' hgo _ =>
              simp [hpred] at hgo
          | maskedTag k' htag hmasked _ =>
              have hk_eq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by simp [htag]
                    _ = some k := hguard
                exact Option.some.inj this
              exact Or.inl (by simpa [hk_eq] using hmasked)
          | notInRegime k' htag hnone _ =>
              have hk_eq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by simp [htag]
                    _ = some k := hguard
                exact Option.some.inj this
              have : R.lookup? k = none := by simpa [hk_eq] using hnone
              exact False.elim (hRdef this)
          | inRegimeTrue k' htag hk hholds _ =>
              have hk_eq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by simp [htag]
                    _ = some k := hguard
                exact Option.some.inj this
              have hk_true : R.lookup? k0 = some true := by simpa [hk0_eq, hk_eq] using hk
              exact Or.inr <|
                varsRegime.withPred_ok (x, qt) k0 arg_name pred_body var_env v true
                  hpred hk_true hlookup
                  ⟨fun _ => hholds, fun hbfalse _ =>
                    by cases hbfalse⟩
          | inRegimeFalse k' htag hk hnot _ =>
              have hk_eq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by simp [htag]
                    _ = some k := hguard
                exact Option.some.inj this
              have hk_false : R.lookup? k0 = some false := by simpa [hk0_eq, hk_eq] using hk
              have hcons :
                  (false = true → qtypPredHolds predSat qt μ v) ∧
                  (false = false → ¬ qtypPredHolds predSat qt μ v) := by
                constructor
                · intro hbtrue
                  cases hbtrue
                · intro _
                  exact hnot
              exact Or.inr <|
                varsRegime.withPred_ok (x, qt) k0 arg_name pred_body var_env v false
                  hpred hk_false hlookup
                  hcons

-- Transport `varsRegime` across a memory change when predicate truth is preserved.
lemma varsRegime_transport_predHolds
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {ρ : VarEnv} {entry : Name × QTyp}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (h : varsRegime predSat R μ ρ entry) :
  varsRegime predSat R μ' ρ entry := by
  cases h with
  | noPred_ok hnp =>
      exact varsRegime.noPred_ok entry hnp
  | guardOnly_ok k hgo =>
      exact varsRegime.guardOnly_ok entry k hgo
  | withPred_ok k arg_name pred_body var_env v b hclos hreg hvar hcons =>
      exact varsRegime.withPred_ok entry k arg_name pred_body var_env v b hclos hreg hvar
        ⟨fun hbtrue => (hpred_compat _ v).1 (hcons.1 hbtrue),
         fun hbfalse hholds => hcons.2 hbfalse ((hpred_compat _ v).2 hholds)⟩

lemma memberVarsRegimeEvidence_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R' μ σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR'
  have hkR : R.lookup? k_y ≠ none := fun hnone => h_mono.2 k_y hkR' hnone
  have hvr_R :
      varsRegime predSat R μ ρcap (y, qt_y) :=
    h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  cases hRk : R.lookup? k_y with
  | none =>
      exact (hkR hRk).elim
  | some b =>
      cases h_mono.1 k_y b hRk with
      | inl hkR'_eq =>
          exact varsRegime_monotone h_mono hguard hkR'_eq hvr_R
      | inr hkR'_none =>
          exact (hkR' hkR'_none).elim

private lemma memberVarsRegimeEvidence_transport_μ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R μ' σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  exact
    varsRegime_transport_predHolds hpred_compat
      (h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR)

-- Transport capturedVarsRegimeProperty across memory change given a predicate iff.
private lemma capturedVarsRegimeProperty_transport_predHolds
  {predSat : PredSat} {R : Regime} {μ μ' : Memory}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
  capturedVarsRegimeProperty predSat R μ' σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR
  have hvr := h x qt_x k_x hlook hguard hkR
  cases hvr with
  | noPred_ok hnp => exact varsRegime.noPred_ok _ hnp
  | guardOnly_ok k hgo => exact varsRegime.guardOnly_ok _ k hgo
  | withPred_ok k arg_name pred_body var_env v b hclos hreg hvar hconsist =>
      exact varsRegime.withPred_ok _ k arg_name pred_body var_env v b hclos hreg hvar
        ⟨fun hbtrue => (hpred_compat _ v).1 (hconsist.1 hbtrue),
         fun hbfalse hholds => hconsist.2 hbfalse ((hpred_compat _ v).2 hholds)⟩

-- Transport closureCapturedVarsRegime across memory change given a predicate iff.
lemma closureCapturedVarsRegime_transport_μ
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ μ' : Memory} {θ : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ' θ v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hT⟩ => ⟨capturedVarsRegimeProperty_transport_predHolds hpred_compat hP, hT⟩)
        hdeep)

-- Monotonicity of valueHasETyp under θ extension.
private lemma valueHasETyp_extends'
  {θ₀ θ₁ : RealizationMap} {v : Value} {t : ETyp} :
  θ₀.extendsMap θ₁ →
  valueHasETyp θ₀ v t →
  valueHasETyp θ₁ v t := by
  intro hExt hval
  induction hval generalizing θ₁ with
  | num n => exact valueHasETyp.num n
  | bool b => exact valueHasETyp.bool b
  | unit => exact valueHasETyp.unit
  | str s => exact valueHasETyp.str s
  | loc hlookup hin => exact valueHasETyp.loc (hExt _ _ hlookup) hin
  | closure htcl henv hcover ih =>
      refine valueHasETyp.closure (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure hpure htcl henv hcover ih =>
      refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | closure_extern htcl henv hcover ih =>
      refine valueHasETyp.closure_extern (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure_extern htcl henv hcover ih =>
      refine valueHasETyp.peClosure_extern (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt

-- Transport closureCapturedVarsRegime across both memory and θ (map extension).
-- The regime property is insensitive to θ; the typing property is monotone
-- under θ extension via valueHasETyp_extends'.
lemma closureCapturedVarsRegime_transport_μ_θ
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ μ' : Memory} {θ θ' : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (hθ : θ.extendsMap θ')
  (h : closureCapturedVarsRegime predSat R qt μ θ v) :
  closureCapturedVarsRegime predSat R qt μ' θ' v := by
  cases h with
  | intro hdeep =>
      exact .intro (deepValueQTypProperty_mono
        (fun σcap ρcap ⟨hP, hnd, hcover, htyp⟩ =>
          ⟨capturedVarsRegimeProperty_transport_predHolds hpred_compat hP,
           hnd, hcover,
           fun y qt_y v_y hσ hρ => valueHasETyp_extends' hθ (htyp y qt_y v_y hσ hρ)⟩)
        hdeep)

lemma memberCvcrEvidence_monotone
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R' μ θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_monotone h_mono
      (h y qt_y v_y hlookup_σ hlookup_ρ)

private lemma memberCvcrEvidence_transport_μ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {θ : RealizationMap}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R μ' θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact
    closureCapturedVarsRegime_transport_μ hpred_compat
      (h y qt_y v_y hlookup_σ hlookup_ρ)

-- Transport MemberCvcrEvidence across both μ and θ (extends).
-- The θ transport requires recursing through deepValueQTypProperty to update
-- capturedVarsTypingProperty via valueHasETyp_extends at every nesting level.
private lemma memberCvcrEvidence_transport_μ_θ
  {predSat : PredSat} {R : Regime} {μ μ' : Memory} {θ θ' : RealizationMap}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (hθ : θ.extendsMap θ')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R μ' θ' σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat hθ
    (h y qt_y v_y hlookup_σ hlookup_ρ)

private lemma capturedVarsRegimePropertyMasked_transport_lookup_back
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap) :
  capturedVarsRegimePropertyMasked masked predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  cases hkR'some : R'.lookup? k_x with
  | none =>
      exact (hkR' hkR'some).elim
  | some b =>
      have hkR : R.lookup? k_x ≠ none := by
        intro hnone
        have hback := hlookup_back k_x b hkR'some
        simp [hnone] at hback
      have hmasked_or_hvr := h x qt_x k_x hlook hguard hkR
      cases hmasked_or_hvr with
      | inl hmasked =>
          exact Or.inl hmasked
      | inr hvr =>
          exact Or.inr <|
            varsRegime_transport_active_lookup_back
              (predSat := predSat) (R := R) (R' := R')
              (μ := μ) (ρ := ρcap) (entry := (x, qt_x))
              hlookup_back hguard hkR'some hvr

lemma closureCapturedVarsRegimeMasked_transport_lookup_back
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hlookup_back : ∀ k b, R'.lookup? k = some b → R.lookup? k = some b)
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R' qt μ θ v := by
  exact
    deepValueQTypProperty_mono
      (fun σcap ρcap ⟨hP, hT⟩ =>
        ⟨capturedVarsRegimePropertyMasked_transport_lookup_back
            (masked := masked) (predSat := predSat) (R := R) (R' := R')
            (μ := μ) hlookup_back hP,
          hT⟩)
      h

private lemma capturedVarsRegimePropertyMasked_monotone
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime} {μ : Memory}
  (h_mono : Regime.monotoneStep R R')
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap) :
  capturedVarsRegimePropertyMasked masked predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  have hkR : R.lookup? k_x ≠ none := fun hnone => h_mono.2 k_x hkR' hnone
  have hmasked_or_hvr := h x qt_x k_x hlook hguard hkR
  cases hmasked_or_hvr with
  | inl hmasked =>
      exact Or.inl hmasked
  | inr hvr =>
      cases hRk : R.lookup? k_x with
      | none =>
          exact (hkR hRk).elim
      | some b =>
          cases h_mono.1 k_x b hRk with
          | inl hkR'_eq =>
              exact Or.inr (varsRegime_monotone h_mono hguard hkR'_eq hvr)
          | inr hkR'_none =>
              exact (hkR' hkR'_none).elim

lemma closureCapturedVarsRegimeMasked_monotone
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (h_mono : Regime.monotoneStep R R')
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R' qt μ θ v := by
  exact
    deepValueQTypProperty_mono
      (fun σcap ρcap ⟨hP, hT⟩ =>
        ⟨capturedVarsRegimePropertyMasked_monotone
            (masked := masked) (predSat := predSat) (R := R) (R' := R')
            (μ := μ) h_mono hP,
          hT⟩)
      h

private lemma capturedVarsRegimePropertyMasked_transport_predHolds
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ μ' : Memory}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (h : capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap) :
  capturedVarsRegimePropertyMasked masked predSat R μ' σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR
  have hmasked_or_hvr := h x qt_x k_x hlook hguard hkR
  cases hmasked_or_hvr with
  | inl hmasked =>
      exact Or.inl hmasked
  | inr hvr =>
      exact Or.inr (varsRegime_transport_predHolds hpred_compat hvr)

lemma closureCapturedVarsRegimeMasked_transport_μ
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ μ' : Memory} {θ : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R qt μ' θ v := by
  exact
    deepValueQTypProperty_mono
      (fun σcap ρcap ⟨hP, hT⟩ =>
        ⟨capturedVarsRegimePropertyMasked_transport_predHolds
            (masked := masked) (predSat := predSat) (R := R)
            hpred_compat hP,
          hT⟩)
      h

lemma closureCapturedVarsRegimeMasked_transport_μ_θ
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ μ' : Memory} {θ θ' : RealizationMap} {v : Value}
  (hpred_compat : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ v ↔ qtypPredHolds predSat qt μ' v)
  (hθ : θ.extendsMap θ')
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R qt μ' θ' v := by
  exact
    deepValueQTypProperty_mono
      (fun σcap ρcap ⟨hP, hnd, hcover, htyp⟩ =>
        ⟨capturedVarsRegimePropertyMasked_transport_predHolds
            (masked := masked) (predSat := predSat) (R := R)
            hpred_compat hP,
          hnd, hcover,
          fun y qt_y v_y hσ hρ => valueHasETyp_extends' hθ (htyp y qt_y v_y hσ hρ)⟩)
      h

private lemma valueConsistentWithRegimeMasked_transport_pred'
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hpred : qt.pred = qt'.pred)
  (hcap_tr :
    closureCapturedVarsRegimeMasked masked predSat R qt μ θ v →
      closureCapturedVarsRegimeMasked masked predSat R qt' μ θ v) :
  valueConsistentWithRegimeMasked masked predSat R qt μ θ v →
  valueConsistentWithRegimeMasked masked predSat R qt' μ θ v := by
  intro h
  cases h with
  | noTag htag hcap =>
      refine valueConsistentWithRegimeMasked.noTag ?_ (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | guardOnly_ok k hgo hcap =>
      refine valueConsistentWithRegimeMasked.guardOnly_ok k ?_ (hcap_tr hcap)
      calc
        qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := hgo
  | maskedTag k htag hmasked hcap =>
      refine valueConsistentWithRegimeMasked.maskedTag k ?_ hmasked (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | notInRegime k htag hknone hcap =>
      refine valueConsistentWithRegimeMasked.notInRegime k ?_ hknone (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | inRegimeTrue k htag hktrue hholds hcap =>
      refine valueConsistentWithRegimeMasked.inRegimeTrue k ?_ hktrue ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred
          (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hholds
  | inRegimeFalse k htag hkfalse hnot hcap =>
      refine valueConsistentWithRegimeMasked.inRegimeFalse k ?_ hkfalse ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred_not
          (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hnot

lemma valueConsistentWithRegimeMasked_transport_pred
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hpred : qt.pred = qt'.pred)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  valueConsistentWithRegimeMasked masked predSat R qt μ θ v →
  valueConsistentWithRegimeMasked masked predSat R qt' μ θ v := by
  intro h
  exact
    valueConsistentWithRegimeMasked_transport_pred'
      (masked := masked) (predSat := predSat) (R := R)
      (qt := qt) (qt' := qt') (μ := μ) (θ := θ) (v := v)
      hpred
      (fun hcap => closureCapturedVarsRegimeMasked_transport_etyp hetyp hcap)
      h

lemma valueConsistentWithRegime_transport_pred
  {predSat : PredSat} {R : Regime} {qt qt' : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hpred : qt.pred = qt'.pred)
  (hetyp : qt.etyp = qt'.etyp := by rfl) :
  valueConsistentWithRegime predSat R qt μ θ v →
  valueConsistentWithRegime predSat R qt' μ θ v := by
  intro h
  have hcap_tr : ∀ hcap : closureCapturedVarsRegime predSat R qt μ θ v,
      closureCapturedVarsRegime predSat R qt' μ θ v :=
    fun hcap => closureCapturedVarsRegime_transport_etyp hetyp hcap
  cases h with
  | noTag htag hcap =>
      refine valueConsistentWithRegime.noTag (predSat := predSat) (R := R) (qt := qt') ?_
        (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | guardOnly_ok k hgo hcap =>
      refine valueConsistentWithRegime.guardOnly_ok (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ (hcap_tr hcap)
      calc qt'.pred = qt.pred := by simp [hpred]
        _ = Predicate.guardOnly k := hgo
  | notInRegime k htag hknone hcap =>
      refine valueConsistentWithRegime.notInRegime (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hknone (hcap_tr hcap)
      have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
      simpa [hEq.symm] using htag
  | inRegimeTrue k htag hktrue hholds hcap =>
      refine valueConsistentWithRegime.inRegimeTrue (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hktrue ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hholds
  | inRegimeFalse k htag hkfalse hnot hcap =>
      refine valueConsistentWithRegime.inRegimeFalse (predSat := predSat) (R := R)
        (qt := qt') (μ := μ) (v := v) k ?_ hkfalse ?_ (hcap_tr hcap)
      · have hEq := qtypGuardTag_of_pred_eq (qt := qt) (qt' := qt') hpred
        simpa [hEq.symm] using htag
      · exact qtypPredHolds_transport_pred_not (predSat := predSat) (qt := qt) (qt' := qt')
          (μ := μ) (v := v) hpred hnot

-- Helper: when valueHasETyp holds and etyp is not a function type, the value
-- is neither a closure nor a peClosure.
private lemma nonClosure_of_nonFunctionType
  {θ : RealizationMap} {v : Value} {etyp : ETyp}
  (hvet : valueHasETyp θ v etyp)
  (hnotfun : etyp.isFunctionType = false) :
  (∀ xp bd rc, v ≠ Value.closure xp bd rc) ∧
  (∀ xp bd rc, v ≠ Value.peClosure xp bd rc) := by
  constructor
  · intro xp bd rc h; subst h
    cases hvet with
    | closure => simp [ETyp.isFunctionType, ETyp.isArrow] at hnotfun
    | closure_extern => simp [ETyp.isFunctionType, ETyp.isArrow] at hnotfun
  · intro xp bd rc h; subst h
    cases hvet with
    | peClosure => simp [ETyp.isFunctionType, ETyp.isParrow] at hnotfun
    | peClosure_extern => simp [ETyp.isFunctionType, ETyp.isParrow] at hnotfun

-- Helper: construct closureCapturedVarsRegime for non-closure values using
-- valueHasETyp evidence.
lemma closureCapturedVarsRegime_nonClosure_of_nonFunctionType
  {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hvet : valueHasETyp θ v qt.etyp)
  (hnotfun : qt.etyp.isFunctionType = false) :
  closureCapturedVarsRegime predSat R qt μ θ v :=
  let ⟨hnc, hnpe⟩ := nonClosure_of_nonFunctionType hvet hnotfun
  .intro (.nonClosure hnc hnpe)

lemma closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  (hvet : valueHasETyp θ v qt.etyp)
  (hnotfun : qt.etyp.isFunctionType = false) :
  closureCapturedVarsRegimeMasked masked predSat R qt μ θ v :=
  let ⟨hnc, hnpe⟩ := nonClosure_of_nonFunctionType hvet hnotfun
  .nonClosure hnc hnpe

lemma ret_eq_of_agreeValueUnder_nonref
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  (¬ ∃ ls, qt.etyp = ETyp.ref ls) →
  qt.etyp.isFunctionType = false →
  qt.poison = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hnotref hnotfun hpoison hret_agree
  cases hret_agree with
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | clean_internal_arrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
  | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | clean_internal_parrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
      exact hnotref ⟨_, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩

lemma agreeValueUnder_nonref_eq_of_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  (¬ ∃ ls, qt.etyp = ETyp.ref ls) →
  qt.etyp.isFunctionType = false →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ →
  o₀ = o₁ := by
  intro hclean hnotref hnotfun hagree
  cases hagree with
  | clean_eq_nonref_nonarrow _ _ _ hval => exact hval
  | withPred_true_eq _ _ _ _ _ hval => exact hval
  | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | clean_internal_arrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
  | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
      exfalso
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | clean_internal_parrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
      exact hnotref ⟨_, hetyp⟩
  | withPred_true_ref _ _ _ hetyp _ _ _ _ =>
      exfalso
      exact hnotref ⟨_, hetyp⟩

lemma agreeValueUnder_transport_clean
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {qt qt2 : QTyp} {o₀ o₁ : Value} :
  qtypCleanUnder R qt →
  qt.etyp = qt2.etyp →
  (qt.poison = false → qt2.poison = false) →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt2 o₀ o₁ →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hclean hetyp hpoison_imp hagree
  cases hclean with
  | clean hpoison =>
      have hpoison2 : qt2.poison = false := hpoison_imp hpoison
      cases hagree with
      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ hbody =>
          have hetyp' := hetyp.trans hetyp1
          -- Need to show internal poison is clean for qt
          -- qt.poison = false (from hpoison), qt.etyp = qt2.etyp (from hetyp)
          -- qt2 has clean_internal_arrow, so its internal poison is clean
          -- Since qt.etyp = qt2.etyp, qt's internal poison is also clean
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ hbody
      | clean_internal_arrow_extern hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow_extern hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
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
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
      | clean_internal_parrow_extern hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow_extern hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
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
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
          have hnotfun' : qt.etyp.isFunctionType = false := by
            simpa [hetyp.symm] using hnotfun
          have hnotref' : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
            intro ⟨ls, h⟩
            apply hnotref
            exact ⟨ls, by simpa [hetyp] using h⟩
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun' hnotref' hEq
      | clean_internal_arrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ hbody =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ hbody
      | clean_internal_arrow_extern hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_arrow_extern hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
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
      | clean_internal_parrow hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
      | clean_internal_parrow_extern hclean_int hetyp1 htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ =>
          have hetyp' := hetyp.trans hetyp1
          have hclean_int_qt : internalPoisonClean qt := by
            simp only [internalPoisonClean]
            simp only [hetyp]
            exact hclean_int
          exact agreeValueUnder.clean_internal_parrow_extern hclean_int_qt hetyp' htcl hmatch hcap
            hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂
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

lemma valueHasETyp_num_etyp {θ : RealizationMap} {n : Int} {t : ETyp} :
  valueHasETyp θ (Value.num n) t → t = ETyp.int := by
  intro h
  cases h
  rfl


def predGuardTag (p : Predicate) : Option Tag :=
  match p with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none


lemma predGuardTag_joinPredicates {p q : Predicate} {k : Tag} :
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
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_fst : acc'.1 = joinPoison acc.1 qt.poison := by
                simpa using (congrArg Prod.fst hfx).symm
              have hacc'_false : acc'.1 = false := ih acc' joined pred? hfold hjoin
              have hjoin' : joinPoison acc.1 qt.poison = false := by
                simpa [hacc'_fst] using hacc'_false
              exact (joinPoison_eq_false hjoin').1

-- If foldlM returns joined poison = false, then every referenced cell is unpoisoned.
private lemma list_foldlM_derefFoldF_poison_false
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    joined = false →
    ∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.poison = false := by
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
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc' : acc'.1 = joinPoison acc.1 qt.poison := by
                  simpa using (congrArg Prod.fst hfx).symm
              have hacc'_false : acc'.1 = false :=
                list_foldlM_derefFoldF_acc_false mem xs acc' joined pred? hfold hjoin
              have hpoison_head : qt.poison = false := by
                have hjoin' : joinPoison acc.1 qt.poison = false := by simpa [hacc'] using hacc'_false
                exact (joinPoison_eq_false hjoin').2
              rcases (List.mem_cons.mp hl) with heq | hltail
              · subst heq
                exact ⟨qt, hlookup, hpoison_head⟩
              · exact ih acc' joined pred? hfold hjoin l hltail

-- If foldlM succeeds, then every referenced cell has type int.
private lemma list_foldlM_derefFoldF_etyp_int
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    ∀ l ∈ xs, ∃ qt, mem.lookup l = some qt := by
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
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · exact ⟨qt, hlookup⟩
              · exact ih acc' joined pred? hfold l hltail

-- If foldlM returns a guard tag k, then every referenced cell predicate has tag k.
private lemma list_foldlM_derefFoldF_guardTag
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (acc : Bool × Option Predicate) (joined : Bool) (pred? : Option Predicate) (k : Tag),
    List.foldlM (derefFoldF mem) acc xs = Except.ok (joined, pred?) →
    predGuardTag (pred?.getD Predicate.noPred) = some k →
    (predGuardTag (acc.2.getD Predicate.noPred) = some k ∨ acc.2 = none) ∧
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ predGuardTag qt.pred = some k) := by
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
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_snd :
                    acc'.2 =
                      match acc.2 with
                      | none => some qt.pred
                      | some p => some (joinPredicates p qt.pred) := by
                simpa using! (congrArg Prod.snd hfx).symm
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
              · intro l hl
                rcases (List.mem_cons.mp hl) with rfl | hltail
                · exact ⟨qt, hlookup, hhead_tag⟩
                · exact htail l hltail

lemma deref_foldM_poison_false
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hjoin : joined = false) (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ qt.poison = false := by
  -- Convert to list fold and apply list lemma
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    -- lemma in Std.ExtTreeSet.Lemmas
    simpa using hl
  exact list_foldlM_derefFoldF_poison_false mem ls.toList (false, none) joined pred? hfold hjoin l hl'

lemma deref_foldM_guardTag
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate) (k : Tag)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (hguard : predGuardTag (pred?.getD Predicate.noPred) = some k)
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ predGuardTag qt.pred = some k := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  have haux :=
    list_foldlM_derefFoldF_guardTag mem ls.toList (false, none) joined pred? k hfold hguard
  exact (haux.2 l hl')

lemma deref_foldM_etyp_int
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact list_foldlM_derefFoldF_etyp_int mem ls.toList (false, none) joined pred? hfold l hl'

-- If l is not in ctx.memEnv and runtimeInstantiatesCtx holds, then θ.lookup l = none
-- (contrapositive of runtimeInstantiatesCtx's first conjunct)
lemma theta_not_contains_if_not_in_memEnv
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (l : Loc) :
  runtimeInstantiatesCtx ctx μ ρ θ →
  ¬ ctx.memEnv.contains l →
  θ.lookup l = none := by
  intro hric hnotContains
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  have ⟨hcontains, _⟩ := hric.1 l a ha
  exact hnotContains hcontains

lemma wfExtendsMap_trans {θ₀ θ₁ θ₂ : RealizationMap} :
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
lemma agreeOnCriticalAndTrusted_implies_agreeOnClean
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
      | some e_s =>
          let qt_s : QTyp := ⟨ETyp.int, e_s.poison, e_s.pred⟩
          have hlookup_s' : s.locs.lookup l = some qt_s := by
            simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_s, Option.map]; rfl
          have hctx_lookup' : ctx.memEnv.lookup l = some qt_s := hctx_mem hlookup_s'
          have hqt : qt_s = qt := by
            have : some qt_s = some qt := by
              calc
                some qt_s = ctx.memEnv.lookup l := by
                  symm
                  exact hctx_lookup'
                _ = some qt := by
                  exact hctx_lookup
            exact Option.some.inj this
          have hclean_s : qtypCleanUnder R qt_s := by
            simpa [hqt] using hclean
          have hlocEntry : agreeLocUnder predSat R μ₀ μ₁ θ₀ θ₁ (l, qt_s) :=
            hcrit_locs l qt_s hlookup_s' hclean_s
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
          have hclean_s : qtypCleanUnder R qt_s := by
            simpa [hqt] using hclean
          have hvarEntry : agreeVarUnder predSat R μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (x, qt_s) :=
            hcrit_vars x qt_s hlookup_s hclean_s
          simpa [hqt] using hvarEntry
    · -- Trusted variable: use trusted-input agreement.
      exact htrusted_vars x qt hctx_lookup hkey hclean

lemma agreeValueUnder_of_agreeVarUnder
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

lemma valueHasETyp_extends
  {θ₀ θ₁ : RealizationMap} {v : Value} {t : ETyp} :
  θ₀.extendsMap θ₁ →
  valueHasETyp θ₀ v t →
  valueHasETyp θ₁ v t := by
  intro hExt hval
  induction hval generalizing θ₁ with
  | num n =>
      exact valueHasETyp.num n
  | bool b =>
      exact valueHasETyp.bool b
  | unit =>
      exact valueHasETyp.unit
  | str s =>
      exact valueHasETyp.str s
  | loc hlookup hin =>
      exact valueHasETyp.loc (hExt _ _ hlookup) hin
  | closure htcl henv hcover ih =>
      refine valueHasETyp.closure (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure hpure htcl henv hcover ih =>
      refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | closure_extern htcl henv hcover ih =>
      refine valueHasETyp.closure_extern (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt
  | peClosure_extern htcl henv hcover ih =>
      refine valueHasETyp.peClosure_extern (htcl := htcl) (hcover := hcover) ?_
      intro y qt v hlookupT hlookupV
      exact ih y qt v hlookupT hlookupV hExt

private lemma capturedVarsTypingProperty_extends
    {θ θ' : RealizationMap} {σcap : CapturedVarEnv} {ρcap : VarEnv}
    (hθ : θ.extendsMap θ')
    (h : capturedVarsTypingProperty θ σcap ρcap) :
    capturedVarsTypingProperty θ' σcap ρcap := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro y qt v hσ hρ
  exact valueHasETyp_extends hθ (h.2.2 y qt v hσ hρ)

lemma agreeValueUnder_clean_extends
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
  (∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₀ v₁ := by
  intro hpred_compat₀ hpred_compat₁ hclean hθ₀ hθ₁ hagree
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₁ v₂ _ =>
      qtypCleanUnder R qt →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
          (∀ (qt : QTyp) (v : Value),
            qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
            θ₀.extendsMap θ₀' →
              θ₁.extendsMap θ₁' →
                agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₁ v₂
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₁ ρcap₂ _ =>
      (∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v) →
        (∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) →
          θ₀.extendsMap θ₀' →
            θ₁.extendsMap θ₁' →
              agreeCapturedEnv predSat R μ₀' μ₁' θ₀' θ₁' σcap ρcap₁ ρcap₂
  have htransport : motive₁ qt v₀ v₁ hagree :=
    agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref_nonarrow := by
        intro qt v₁ v₂ hpoison hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hagree)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ hbody ihCap
          _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          (capturedVarsTypingProperty_extends hθ₀ htyping₁)
          (capturedVarsTypingProperty_extends hθ₁ htyping₂)
          hv₁ hv₂ hbody)
      (clean_internal_arrow_extern := by
        intro id x y argTyp argPoison argPred retSpec effects p tcls qt tcl σcap argQt cap memberCap ρcap₁ ρcap₂ v₁ v₂
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ ihCap
          _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_arrow_extern hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          (capturedVarsTypingProperty_extends hθ₀ htyping₁)
          (capturedVarsTypingProperty_extends hθ₁ htyping₂)
          hv₁ hv₂)
      (dirty_internal_arrow := by
        intro qt v₁ v₂ hdirty hisArrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_arrow hdirty hisArrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₁ ρcap₂ v₁ v₂ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ ihCap
          _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          (capturedVarsTypingProperty_extends hθ₀ htyping₁)
          (capturedVarsTypingProperty_extends hθ₁ htyping₂)
          hv₁ hv₂)
      (clean_internal_parrow_extern := by
        intro id x y argTyp argPoison argPred retSpec p tcls qt tcl σcap argQt cap memberCap ρcap₁ ρcap₂ v₁ v₂
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₁ hmemberCvcr₁ hmemberVars₂ hmemberCvcr₂ htyping₁ htyping₂ hv₁ hv₂ ihCap
          _hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_internal_parrow_extern hclean_internal hetyp htcl hmatch
          (ihCap hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₀ hmemberVars₁)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₀ hθ₀ hmemberCvcr₁)
          (memberVarsRegimeEvidence_transport_μ hpred_compat₁ hmemberVars₂)
          (memberCvcrEvidence_transport_μ_θ hpred_compat₁ hθ₁ hmemberCvcr₂)
          (capturedVarsTypingProperty_extends hθ₀ htyping₁)
          (capturedVarsTypingProperty_extends hθ₁ htyping₂)
          hv₁ hv₂)
      (dirty_internal_parrow := by
        intro qt v₁ v₂ hdirty hisParrow htyp1 htyp2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.dirty_internal_parrow hdirty hisParrow
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2))
      (clean_ref := by
        intro ls l a₁ a₂ qt v₁ v₂ hpoison hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.clean_ref hpoison hetyp (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (withPred_true_eq := by
        intro k qt v₁ v₂ htag hregime hnotfun hnotref hagree _hclean _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeValueUnder.withPred_true_eq k htag hregime hnotfun hnotref hagree)
      (withPred_true_ref := by
        intro k ls l a₁ a₂ qt v₁ v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 _hclean _hpred_compat₀ _hpred_compat₁ hθ₀ hθ₁
        exact agreeValueUnder.withPred_true_ref k htag hregime hetyp
          (hθ₀ _ _ hlookup1) hin hv1 (hθ₁ _ _ hlookup2) hv2)
      (nil := by
        intro ρcap₁ ρcap₂ _hpred_compat₀ _hpred_compat₁ _hθ₀ _hθ₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hclean hlookup1 hlookup2 htyp1 htyp2 hagree htail ihAgree ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_clean hclean hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihAgree hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      (cons_dirty := by
        intro x qt σcap ρcap₁ ρcap₂ v₁ v₂ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihTail
          hpred_compat₀ hpred_compat₁ hθ₀ hθ₁
        exact agreeCapturedEnv.cons_dirty hdirty hlookup1 hlookup2
          (valueHasETyp_extends hθ₀ htyp1) (valueHasETyp_extends hθ₁ htyp2)
          (ihTail hpred_compat₀ hpred_compat₁ hθ₀ hθ₁))
      hagree
  exact htransport hclean hpred_compat₀ hpred_compat₁ hθ₀ hθ₁

-- Explicit memory-transport interface (with predicate-compatibility witnesses):
-- a call-site wrapper around `agreeValueUnder_clean_extends`.
lemma agreeValueUnder_clean_extends_transport_mem
  {predSat : PredSat} {R : Regime} {μ₀ μ₁ μ₀' μ₁' : Memory}
  {θ₀ θ₁ θ₀' θ₁' : RealizationMap} {qt : QTyp} {v₀ v₁ : Value}
  (_hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v)
  (_hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
    qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v) :
  qtypCleanUnder R qt →
  θ₀.extendsMap θ₀' →
  θ₁.extendsMap θ₁' →
  agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
  agreeValueUnder predSat R μ₀' μ₁' θ₀' θ₁' qt v₀ v₁ := by
  intro hclean hθ₀ hθ₁ hagree
  exact agreeValueUnder_clean_extends _hpred_compat₀ _hpred_compat₁ hclean hθ₀ hθ₁ hagree

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
        obtain ⟨v₀, hlookup₀, htyp₀⟩ := hvars₀ hctx_lookup
        obtain ⟨v₁, hlookup₁, htyp₁⟩ := hvars₁ hctx_lookup
        have hagreeVal : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
          agreeValueUnder_of_agreeVarUnder hvarEntry hlookup₀ hlookup₁
        exact agreeCapturedEnv.cons_clean hclean hlookup₀ hlookup₁ htyp₀ htyp₁ hagreeVal (ih hσlookup_tail)
      · have hctx_lookup : ctx.varEnv.lookup x = some qt :=
          hσlookup x qt (by simp)
        obtain ⟨v₀, hlookup₀, htyp₀⟩ := hvars₀ hctx_lookup
        obtain ⟨v₁, hlookup₁, htyp₁⟩ := hvars₁ hctx_lookup
        exact agreeCapturedEnv.cons_dirty hclean hlookup₀ hlookup₁ htyp₀ htyp₁ (ih hσlookup_tail)

lemma agreeCapturedEnv_of_agreeOnClean
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

private lemma agreeCapturedEnv_lookup_typed
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  {y : Name} {qt : QTyp}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
  (hlookup : σcap.lookup y = some qt) :
  ∃ v₀ v₁,
    ρcap₀.lookup y = some v₀ ∧
    valueHasETyp θ₀ v₀ qt.etyp ∧
    ρcap₁.lookup y = some v₁ ∧
    valueHasETyp θ₁ v₁ qt.etyp := by
  revert y qt hlookup
  induction σcap generalizing ρcap₀ ρcap₁ with
  | nil =>
      intro y qt hlookup
      cases hcap with
      | nil =>
          simp [CapturedVarEnv.lookup_eq, List.lookup] at hlookup
  | cons entry σtail ih =>
      intro y qt hlookup
      rcases entry with ⟨x, qtHead⟩
      cases hcap with
      | cons_clean hclean hlookup₀ hlookup₁ htyp₀ htyp₁ _hagree htail =>
          by_cases hyx : y == x
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            have hyx' : y = x := beq_iff_eq.mp hyx
            subst hyx'
            cases hlookup
            exact ⟨_, _, hlookup₀, htyp₀, hlookup₁, htyp₁⟩
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            exact ih (hcap := htail) hlookup
      | cons_dirty hdirty hlookup₀ hlookup₁ htyp₀ htyp₁ htail =>
          by_cases hyx : y == x
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            have hyx' : y = x := beq_iff_eq.mp hyx
            subst hyx'
            cases hlookup
            exact ⟨_, _, hlookup₀, htyp₀, hlookup₁, htyp₁⟩
          · simp [CapturedVarEnv.lookup_eq, List.lookup, hyx] at hlookup
            exact ih (hcap := htail) hlookup

lemma agreeCapturedEnv_ofCaptured_lookup_typed_left
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁) :
  ∀ y qt, (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
    ∃ v, ρcap₀.lookup y = some v ∧ valueHasETyp θ₀ v qt.etyp := by
  intro y qt hlookup
  have hlist : σcap.lookup y = some qt :=
    list_lookup_of_ofCaptured_lookup σcap y qt hlookup
  rcases agreeCapturedEnv_lookup_typed hcap hlist with ⟨v₀, _v₁, hlookup₀, htyp₀, _hlookup₁, _htyp₁⟩
  exact ⟨v₀, hlookup₀, htyp₀⟩

lemma agreeCapturedEnv_ofCaptured_lookup_typed_right
  {predSat : PredSat} {R : Regime}
  {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
  {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
  (hcap : agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁) :
  ∀ y qt, (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
    ∃ v, ρcap₁.lookup y = some v ∧ valueHasETyp θ₁ v qt.etyp := by
  intro y qt hlookup
  have hlist : σcap.lookup y = some qt :=
    list_lookup_of_ofCaptured_lookup σcap y qt hlookup
  rcases agreeCapturedEnv_lookup_typed hcap hlist with ⟨_v₀, v₁, _hlookup₀, _htyp₀, hlookup₁, htyp₁⟩
  exact ⟨v₁, hlookup₁, htyp₁⟩

lemma RealizationMap_lookup_update_ne
  {θ : RealizationMap} {l l' : Loc} {addr : Address} :
  l' ≠ l →
  (θ.update l addr).lookup l' = θ.lookup l' := by
  intro hne
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [RealizationMap.update, RealizationMap.lookup, ExtTreeMap.getElem?_insert, hcmp]

lemma Memory_lookup_update_ne
  {μ : Memory} {a a' : Address} {v : Int} :
  a ≠ a' →
  (Memory.update μ a' v).lookup a = μ.lookup a := by
  intro hne
  have hcmp : compare a' a ≠ Ordering.eq := by
    intro hcmp
    have : a' = a := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [Memory.update, Memory.lookup, ExtTreeMap.getElem?_insert, hcmp]

lemma Memory_contains_of_lookup {μ : Memory} {a : Address} {n : Int} :
  Memory.lookup μ a = some n →
  μ.contains a = true := by
  intro hlookup
  have hisSome : μ[a]?.isSome = true := by
    have h' : μ[a]? = some n := by
      simpa [Memory.lookup, ExtTreeMap.get?_eq_getElem?] using hlookup
    simp [h']
  have hmem : a ∈ μ := (ExtTreeMap.mem_iff_isSome_getElem?).2 hisSome
  exact (ExtTreeMap.contains_iff_mem).2 hmem

lemma Memory_lookup_some_of_contains {μ : Memory} {a : Address} :
  μ.contains a = true →
  ∃ n, Memory.lookup μ a = some n := by
  intro hcontains
  have hmem : a ∈ μ := (ExtTreeMap.contains_iff_mem).1 hcontains
  have hisSome : μ[a]?.isSome = true := (ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
  cases hlookup : μ[a]? with
  | none =>
      simp [hlookup] at hisSome
  | some n =>
      exact ⟨n, by simp [Memory.lookup, ExtTreeMap.get?_eq_getElem?, hlookup]⟩

lemma agreeOnClean_newRef_extend
  (predSat : PredSat) (R : Regime) (ctxᵢ : TypeContext)
  (res1 res : TypeResult) (l : Loc) (etyp : ETyp)
  (cfg₀' cfg₁' cf₀ cf₁ : Config) (n₀ n₁ : Int) (a₀_new a₁_new : Address)
  (θ₀1 θ₁1 θ₀' θ₁' : RealizationMap)
  (h_mem :
      res.memEnv' =
        updateMemEnv res1.memEnv' l
          ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison,
            if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩)
  (h_etyp1 : res1.qualType.etyp = etyp)
  (h_etyp_int : etyp = ETyp.int)
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
  (hqtypPredHolds_mem₀ :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v)
  (hqtypPredHolds_mem₁ :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v)
  (hagree_clean_e :
      agreeOnClean predSat R (ctxAfter ctxᵢ res1)
        cfg₀'.memory cfg₀'.varEnv θ₀1 cfg₁'.memory cfg₁'.varEnv θ₁1)
  (hres_agree_e :
      resultAgreesIfClean predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁)) :
  agreeOnClean predSat R (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
  let storedQt : QTyp :=
    ⟨etyp, joinPoison ctxᵢ.pc res1.qualType.poison,
      if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  constructor
  · intro l' qt hlookup hclean
    by_cases h_eq : l' = l
    · subst l'
      have hqt : qt = storedQt := by
        have hlookup' : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
          simp only [updateMemEnv, storedQt, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?,
            Std.ExtTreeMap.getElem?_insert_self, Option.map, h_etyp_int]
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
            have hpc_false : ctxᵢ.pc = false := by
              cases hpc : ctxᵢ.pc with
              | false => exact rfl
              | true =>
                  simp [storedQt, qtypGuardTag, hpc] at htag
            have htag' : qtypGuardTag res1.qualType = some k := by
              simpa [qtypGuardTag, storedQt, hpc_false] using htag
            have hnotfun' : res1.qualType.etyp.isFunctionType = false := by
              simpa [storedQt, h_etyp1] using hnotfun
            exact qtypCleanUnder.guard k htag' hreg hnotfun'
      have hagree_res1 :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 res1.qualType (Value.num n₀) (Value.num n₁) :=
        hres_agree_e hclean_res1
      have hagree_stored_old :
          agreeValueUnder predSat R cfg₀'.memory cfg₁'.memory θ₀1 θ₁1 storedQt (Value.num n₀) (Value.num n₁) := by
        refine agreeValueUnder_transport_clean hclean ?_ ?_ hagree_res1
        · simp [storedQt, h_etyp1]
        · intro hpoison
          have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
            simpa [storedQt] using hpoison
          exact (joinPoison_eq_false hjoin).2
      have hagree_stored :
          agreeValueUnder predSat R cf₀.memory cf₁.memory θ₀' θ₁' storedQt (Value.num n₀) (Value.num n₁) :=
        agreeValueUnder_clean_extends_transport_mem
          hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree_stored_old
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
            agreeValueUnder_clean_extends_transport_mem
              hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree
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
          agreeValueUnder_clean_extends_transport_mem
            hqtypPredHolds_mem₀ hqtypPredHolds_mem₁ hclean hθext₀'.1 hθext₁'.1 hagree
        refine agreeVarUnder.agree_values x qt v0 v1 ?_ ?_ hagree'
        · simpa [hvar₀] using hlook0
        · simpa [hvar₁] using hlook1

lemma var_valueHasETyp_of_typecheck
  (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (x : Name) (res : TypeResult) (o : Value)
  (htc : typecheckVar ctx x = .ok res)
  (hwfθ : wfRealizationMap θ)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (hlookup : ρ.lookup x = some o) :
  valueHasETyp θ o res.qualType.etyp := by
  cases hlookup_ctx : ctx.varEnv.lookup x with
  | none =>
      simp [typecheckVar, hlookup_ctx] at htc
  | some qt =>
      obtain ⟨v, hv, htyp⟩ := var_has_correct_type ctx μ ρ θ x qt hwfθ hric hlookup_ctx
      have heq : v = o := Option.some.inj (hv.symm.trans hlookup)
      have hetyp : res.qualType.etyp = qt.etyp := by
        simp only [typecheckVar, hlookup_ctx] at htc
        (split at htc; try split at htc);
          repeat (first | split at htc | simp [pure, Except.pure] at htc | cases htc | rfl)
      rw [← heq, hetyp]; exact htyp

-- ============================================================================
-- Extended-regime (monotoneStepExt) transport: Masked variants.
-- Generic deep-bounded transport + Masked mirrors of the non-masked `*_monotoneExt` lemmas.
-- ============================================================================

/-- Generic: transport a deep captured-env property across closure nesting, supplying at each
    level the captured-env bound `CapturedEnvFullBounded σcap B` extracted from the deep type
    bound `etypClosuresFullBounded qt.etyp B`. -/
private lemma deepValueQTypProperty_mono_bounded
    {P P' : CapturedVarEnv → VarEnv → Prop} {B : Tag}
    (hPP : ∀ σcap ρcap, CapturedEnvFullBounded σcap B → P σcap ρcap → P' σcap ρcap)
    {qt : QTyp} {v : Value}
    (hdeep : deepValueQTypProperty P qt v) :
    etypClosuresFullBounded qt.etyp B → deepValueQTypProperty P' qt v := by
  induction hdeep with
  | nonClosure hv hpe => intro _; exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem hP _hrec _hbody ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2; simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      exact .closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem (hPP σcap ρcap hσbound hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
        _hbody
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem hP _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2; simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem
        (hPP σcap ρcap hσbound hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem hP _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2; simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem
        (hPP σcap ρcap hσbound hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem hP _hrec ih =>
      intro hbound
      have hσbound : CapturedEnvFullBounded σcap B := by
        have hb2 := hbound; rw [hetyp] at hb2; simp only [etypClosuresFullBounded] at hb2
        simpa using hb2 _ hmem
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem
        (hPP σcap ρcap hσbound hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (CapturedEnvFullBounded_member_etypClosures hσbound (List_lookup_some_mem x qt_x σcap hs)))

private lemma capturedVarsRegimePropertyMasked_monotoneExt
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime} {μ : Memory}
  {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags) (hnewB : ∀ k, newTags k → B ≤ k)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (hσbound : CapturedEnvFullBounded σcap B)
  (h : capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap) :
  capturedVarsRegimePropertyMasked masked predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hguard hkR'
  have hknew : ¬ newTags k_x := fun h2 => absurd (hnewB k_x h2) (Nat.not_le.2
    (CapturedEnvFullBounded_guardTag_lt hσbound (List_lookup_some_mem x qt_x σcap hlook) hguard))
  have hkR : R.lookup? k_x ≠ none := by
    rcases h_mono.2 k_x hkR' with h2 | h2
    · exact h2
    · exact absurd h2 hknew
  cases h x qt_x k_x hlook hguard hkR with
  | inl hmasked => exact Or.inl hmasked
  | inr hvr =>
      cases hRk : R.lookup? k_x with
      | none => exact (hkR hRk).elim
      | some b =>
          cases h_mono.1 k_x b hknew hRk with
          | inl hkR'_eq => exact Or.inr (varsRegime_monotoneExt h_mono hguard hknew hkR'_eq hvr)
          | inr hkR'_none => exact (hkR' hkR'_none).elim

lemma closureCapturedVarsRegimeMasked_monotoneExt
  {masked : Tag → Prop} {predSat : PredSat} {R R' : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value} {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags) (hnewB : ∀ k, newTags k → B ≤ k)
  (hbound : etypClosuresFullBounded qt.etyp B)
  (h : closureCapturedVarsRegimeMasked masked predSat R qt μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R' qt μ θ v :=
  deepValueQTypProperty_mono_bounded
    (fun _σcap _ρcap hσbound hPT =>
      ⟨capturedVarsRegimePropertyMasked_monotoneExt h_mono hnewB hσbound hPT.1, hPT.2⟩)
    h hbound

private lemma memberVarsRegimeEvidence_monotoneExt
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags) (hnewB : ∀ k, newTags k → B ≤ k)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (hσbound : CapturedEnvFullBounded σcap B)
  (h : MemberVarsRegimeEvidence predSat R μ σcap ρcap) :
  MemberVarsRegimeEvidence predSat R' μ σcap ρcap := by
  intro y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR'
  have hknew : ¬ newTags k_y := fun h2 => absurd (hnewB k_y h2)
    (Nat.not_le.2 (ofCaptured_guardTag_lt_of_fullBounded hσbound hlookup_σ hguard))
  have hkR : R.lookup? k_y ≠ none := by
    rcases h_mono.2 k_y hkR' with h2 | h2
    · exact h2
    · exact absurd h2 hknew
  have hvr_R := h y qt_y k_y v_y hlookup_σ hlookup_ρ hguard hkR
  cases hRk : R.lookup? k_y with
  | none => exact (hkR hRk).elim
  | some b =>
      cases h_mono.1 k_y b hknew hRk with
      | inl hkR'_eq => exact varsRegime_monotoneExt h_mono hguard hknew hkR'_eq hvr_R
      | inr hkR'_none => exact (hkR' hkR'_none).elim

/-- Extended-regime variant of `memberCvcrEvidence_monotone`: the captured env's
    nested closure tags are below `B`, so freshness (`¬ newTags`) is discharged per member. -/
private lemma memberCvcrEvidence_monotoneExt
  {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
  {newTags : Tag → Prop} {B : Tag}
  (h_mono : Regime.monotoneStepExt R R' newTags) (hnewB : ∀ k, newTags k → B ≤ k)
  {σcap : CapturedVarEnv} {ρcap : VarEnv}
  (hσbound : CapturedEnvFullBounded σcap B)
  (h : MemberCvcrEvidence predSat R μ θ σcap ρcap) :
  MemberCvcrEvidence predSat R' μ θ σcap ρcap := by
  intro y qt_y v_y hlookup_σ hlookup_ρ
  exact closureCapturedVarsRegime_monotoneExt h_mono hnewB
    (etypClosuresFullBounded_of_ofCaptured_lookup hσbound hlookup_σ)
    (h y qt_y v_y hlookup_σ hlookup_ρ)

lemma consistentWithRegimeMasked_monotoneExt
    (masked : Tag → Prop) (predSat : PredSat) (R R' : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) {newTags : Tag → Prop}
    (h_mono : Regime.monotoneStepExt R R' newTags)
    (hnewB : ∀ k, newTags k → ctx.nextTag ≤ k)
    (htag : TagBoundedCtx ctx)
    (h_cwr : consistentWithRegimeMasked masked predSat R ctx μ ρ θ) :
    consistentWithRegimeMasked masked predSat R' ctx μ ρ θ := by
  simp only [consistentWithRegimeMasked] at h_cwr ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hR'def
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        have hknew : ¬ newTags k := fun hnew => absurd (hnewB k hnew)
          (Nat.not_le.2 (TagBoundedCtx_memEnv_guardTag_lt htag hlookup hguard))
        have hRdef : R.lookup? k ≠ none := by
          rcases h_mono.2 k hR'def with hRne | hnew
          · exact hRne
          · exact absurd hnew hknew
        cases h_cwr.1 l qt k hlookup hguard hRdef with
        | inl hmasked => exact Or.inl hmasked
        | inr hloc => exact Or.inr (locsRegime_monotoneExt h_mono hguard hknew hk' hloc)
  · intro x qt k hlookup hguard hR'def
    cases hk' : R'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        have hknew : ¬ newTags k := fun hnew => absurd (hnewB k hnew)
          (Nat.not_le.2 (TagBoundedCtx_varEnv_guardTag_lt htag hlookup hguard))
        have hRdef : R.lookup? k ≠ none := by
          rcases h_mono.2 k hR'def with hRne | hnew
          · exact hRne
          · exact absurd hnew hknew
        cases h_cwr.2.1 x qt k hlookup hguard hRdef with
        | inl hmasked => exact Or.inl hmasked
        | inr hvars => exact Or.inr (varsRegime_monotoneExt h_mono hguard hknew hk' hvars)
  · intro x qt v hlookup hρ
    exact closureCapturedVarsRegimeMasked_monotoneExt h_mono hnewB
      (TagBoundedCtx_varEnv_etypClosures htag hlookup) (h_cwr.2.2 x qt v hlookup hρ)

lemma opEType_ne_ref (op : Op) (et1 et2 : ETyp) (ls : LocSet) :
  opEType? op et1 et2 ≠ some (ETyp.ref ls) := by
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?]

lemma opEType_implies_nonfun (op : Op) (et1 et2 result : ETyp) :
  opEType? op et1 et2 = some result →
  et1.isFunctionType = false ∧ et2.isFunctionType = false ∧ result.isFunctionType = false := by
  intro h
  cases op <;> cases et1 <;> cases et2 <;> simp [opEType?] at h <;> cases h <;>
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]

lemma opUnaryEType_ne_ref (op : UnaryOp) (et1 : ETyp) (ls : LocSet) :
  opUnaryEType? op et1 ≠ some (ETyp.ref ls) := by
  cases op
  cases et1 <;> simp [opUnaryEType?]

lemma opUnaryEType_implies_nonfun (op : UnaryOp) (et1 result : ETyp) :
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
      | ref ls =>
          cases h
      | arrow st1 st2 p tcls =>
          cases h
      | parrow st1 st2 p tcls =>
          cases h

-- When evalOp succeeds and OpEType fixes the result type, the value has that type
lemma valueHasETyp_of_evalOp
  (op : Op) (v1 v2 v : Value) (θ : RealizationMap) (t1 t2 result_etyp : ETyp)
  (hop : OpEType op t1 t2 result_etyp)
  (heval : LeanPoison.evalOp op v1 v2 = some v) :
  valueHasETyp θ v result_etyp := by
  cases hop <;> simp only [LeanPoison.evalOp] at heval <;> cases v1 <;> cases v2 <;> simp at heval <;> cases heval
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.num _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.bool _
  · exact valueHasETyp.num _

-- When evalUnaryOp succeeds and opUnaryEType? fixes the result type, the value has that type
lemma valueHasETyp_of_evalUnaryOp
  (op : UnaryOp) (v1 v : Value) (θ : RealizationMap) (t1 result_etyp : ETyp)
  (hop : opUnaryEType? op t1 = some result_etyp)
  (heval : LeanPoison.evalUnaryOp op v1 = some v) :
  valueHasETyp θ v result_etyp := by
  (cases op; simp [opUnaryEType?] at hop)
  cases t1 <;> simp at hop
  cases hop
  simp only [LeanPoison.evalUnaryOp] at heval
  cases v1 <;> simp at heval
  cases heval
  exact valueHasETyp.bool _

section StepFR_IH_Abbrevs
variable (predSat : PredSat) (tm : TagMeaning) (fuel : Nat)

  abbrev StepFR_IH_WithExprCtx
      (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
      (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    let _tmAnchor := tm
    ∀ m < fuel, ∀ {tmᵢ : TagMeaning} (e : Expr) (ctxᵢ : TypeContext),
      CtxReach ctxᵢ →
      CanUse e →
      wfTagMeaningCtx tmᵢ ctxᵢ →
      TagBoundedCtx ctxᵢ →
      ∀ (res : TypeResult), typecheck ctxᵢ e m = .ok res →
        StepFR ctxᵢ e res predSat tmᵢ m (registry := registry)

  abbrev StepFRSingleRunFinalCleanPcTrue_IH_WithExprCtx
      (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
      (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    let _tmAnchor := tm
    ∀ m < fuel, ∀ {tmᵢ : TagMeaning} (e : Expr) (ctxᵢ : TypeContext),
      CtxReach ctxᵢ →
      CanUse e →
      wfTagMeaningCtx tmᵢ ctxᵢ →
      TagMeaningBounded tmᵢ ctxᵢ.nextTag →
      ∀ (res : TypeResult),
        typecheck ctxᵢ e m = .ok res →
        StepFRSingleRunFinalCleanPcTrue ctxᵢ e res predSat tmᵢ m (registry := registry)

  abbrev StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_WithExprCtx
      (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
      (masked : Tag → Prop)
      (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
      (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
      (registry : ExternRegistry := emptyExternRegistry) : Prop :=
    let _tmAnchor := tm
    ∀ m < fuel, ∀ {tmᵢ : TagMeaning} (e : Expr) (ctx : TypeContext),
      CtxReach ctx →
      CanUse e →
      wfTagMeaningCtx tmᵢ ctx →
      TagMeaningBounded tmᵢ ctx.nextTag →
      ∀ (res : TypeResult),
        typecheck ctx e m = .ok res →
        StepFRSingleRunFinalCleanPcTrueMaskedRegParam
          masked CtxCons ValCons ctx e res predSat tmᵢ m (registry := registry)

lemma agreeValueUnder_clean_transport_by_cleanBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ σcap ρcap)
    (hmemberCvcr₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₁ θ₁ σcap ρcap) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
  have hrec :
      (qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁) :=
    agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := fun qt v₀ v₁ _ =>
        qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁)
      (motive_2 := fun σcap ρcap₀ ρcap₁ _ =>
        agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
      (clean_eq_nonref_nonarrow := by
        intro qt v₀ v₁ hpoison hnotfun hnotref heq _hclean
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ hbody ihcap
          _hclean
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁ hbody)
      (clean_internal_arrow_extern := by
        intro id x y argTyp argPoison argPred retSpec effects p tcls qt tcl σcap argQt cap memberCap ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          _hclean
        exact agreeValueUnder.clean_internal_arrow_extern hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hclean
        exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          _hclean
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (clean_internal_parrow_extern := by
        intro id x y argTyp argPoison argPred retSpec p tcls qt tcl σcap argQt cap memberCap ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          _hclean
        exact agreeValueUnder.clean_internal_parrow_extern hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (dirty_internal_parrow := by
        intro qt v₀ v₁ hdirty_internal hisParrow htyp1 htyp2 _hclean
        exact agreeValueUnder.dirty_internal_parrow hdirty_internal hisParrow htyp1 htyp2)
      (clean_ref := by
        intro ls l a₀ a₁ qt v₀ v₁ hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁ _hclean
        exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁)
      (withPred_true_eq := by
        intro k qt v₀ v₁ htag _hreg hnotfun hnotref heq hclean
        cases hclean with
        | clean hpoison =>
            exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq
        | guard k' htag' hk'R' _hnotfun' =>
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag'
                  _ = some k := htag
              exact Option.some.inj this
            have hreg : R'.lookup? k = some true := by
              simpa [hk] using hk'R'
            exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref heq)
      (withPred_true_ref := by
        intro k ls l a₀ a₁ qt v₀ v₁ htag _hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁ hclean
        cases hclean with
        | clean hpoison =>
            exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁
        | guard k' htag' hk'R' _hnotfun' =>
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag'
                  _ = some k := htag
              exact Option.some.inj this
            have hreg : R'.lookup? k = some true := by
              simpa [hk] using hk'R'
            exact agreeValueUnder.withPred_true_ref k htag hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁)
      (nil := by
        intro ρcap₀ ρcap₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ _hcleanR hlookup1 hlookup2 htyp1 htyp2 hagree htail ihagree ihtail
        by_cases hcleanR' : qtypCleanUnder R' qt
        · exact agreeCapturedEnv.cons_clean hcleanR' hlookup1 hlookup2 htyp1 htyp2 (ihagree hcleanR') ihtail
        · exact agreeCapturedEnv.cons_dirty hcleanR' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      (cons_dirty := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihtail
        have hdirty' : ¬ qtypCleanUnder R' qt := by
          intro hcleanR'
          exact hdirty (h_clean_back qt hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      hagree
  exact hrec hclean

lemma applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound
  {α : Type}
  (applyOne : α → Tag × Loc → TypecheckM TypeResult)
  (base : Loc)
  (hmono : ∀ item cursor result,
    base ≤ cursor.2 → applyOne item cursor = .ok result → base ≤ result.nextLoc')
  {xs : List α} {cursor : Tag × Loc} {results : List TypeResult} {y : TypeResult}
  (hbase : base ≤ cursor.2)
  (hthread : applyClosuresThreaded applyOne xs cursor = .ok results)
  (hmem : y ∈ results) :
  ∃ x, x ∈ xs ∧ ∃ cursor', base ≤ cursor'.2 ∧ applyOne x cursor' = .ok y := by
  induction xs generalizing cursor results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      cases hmem
  | cons x xs ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne x cursor with
      | error _ =>
          simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne xs (first.nextTag', first.nextLoc') with
          | error _ =>
              simp [hrest] at hthread
          | ok rest =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              simp at hmem
              cases hmem with
              | inl hy =>
                  subst hy
                  exact ⟨x, by simp, cursor, hbase, hfirst⟩
              | inr hy =>
                  have hbase' : base ≤ first.nextLoc' := hmono x cursor first hbase hfirst
                  rcases ih hbase' hrest hy with ⟨x', hx', cursor', hcursor', happly⟩
                  exact ⟨x', by simp [hx'], cursor', hcursor', happly⟩


lemma PExpr_toExpr_of_toPExpr?_some : ∀ (e : Expr) (pe : PExpr),
    Expr.toPExpr? e = some pe → PExpr.toExpr pe = e
  | .unit, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .num n, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .bool b, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .str s, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .var x, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .op e1 o e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h
          subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .unaryop o e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .ite e1 e2 e3, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          cases h3 : Expr.toPExpr? e3 with
          | none => simp [h1, h2, h3] at h
          | some pe3 =>
            simp [h1, h2, h3] at h; subst h; simp [PExpr.toExpr]
            exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1,
                   PExpr_toExpr_of_toPExpr?_some e2 pe2 h2,
                   PExpr_toExpr_of_toPExpr?_some e3 pe3 h3⟩
  | .deref e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .vlet x e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .app e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .newRef _, _, h => by simp [Expr.toPExpr?] at h
  | .assign _ _, _, h => by simp [Expr.toPExpr?] at h
  | .seq _ _, _, h => by simp [Expr.toPExpr?] at h
  | .fn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .pfn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externVal _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externFn _ _ _ _ _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externPfn _ _ _ _ _ _ _, _, h => by simp [Expr.toPExpr?] at h


-- ═══════════════════════════════════════════════════════════════════════════
-- Structural canonical-extension threading: boundary adapters.
--
-- These wrap the `typecheck_preserves_predSatLaws` induction
-- (in `TypecheckInduction.lean`) into `StepFRSingleRunTagMeaningPost`,
-- obtaining a `tm'` witness for each subexpression.
-- ═══════════════════════════════════════════════════════════════════════════


theorem StepFRSingleRunTagMeaningPost.of_typecheck_preserves
    (predSat : PredSat)
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (hframe : TagFrame predSat tm res.tagLog')
    (htc : typecheck ctx e fuel = .ok res) :
    StepFRSingleRunTagMeaningPost ctx e res predSat tm := by
  rcases typecheck_preserves_predSatLaws predSat tm ctx e fuel res
      h_wf h_bounded hframe htc with
    ⟨tm', hcanon, hlaws', hw⟩
  exact
    ⟨tm', hcanon, hlaws',
      IsCanonicalExtension.respectsResult hcanon,
      IsCanonicalExtension.wfCtx hcanon, hw⟩

theorem StepFRSingleRunTagMeaningPost.refl_of_ctxAfter_eq
    {predSat : PredSat}
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr} {res : TypeResult}
    (h_laws : PredSatLaws predSat tm)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (hctxAfter : ctxAfter ctx res = ctx)
    (h_resp : QTypRespectsTagMeaning tm res.qualType) :
    StepFRSingleRunTagMeaningPost ctx e res predSat tm := by
  have h_wf_after : wfTagMeaningCtx tm (ctxAfter ctx res) := by
    simpa [hctxAfter] using h_wf
  have h_next : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter
    simpa [ctxAfter] using h
  have h_bounded_res : TagMeaningBounded tm res.nextTag' := by
    simpa [h_next] using h_bounded
  exact
    ⟨tm,
      IsCanonicalExtension.refl h_bounded_res h_wf_after h_resp,
      h_laws,
      h_resp,
      h_wf_after,
      WithinLog.refl tm res.tagLog'⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Shared clean-under backward-transport infrastructure
-- The clean-under backward transports used by multiple StepFR* files
-- (`cleanUnder_of_monotoneExt`, `agreeValueUnder_clean_transport_by_cleanBack_ext`).
-- ═══════════════════════════════════════════════════════════════════════════


/-- Extended-regime (monotoneStepExt) backward clean-under transport.
    Freshness for qt's guard tag is discharged from `qtypPredTagBounded qt B`. -/
lemma cleanUnder_of_monotoneExt {R R' : Regime} {qt : QTyp} {newTags : Tag → Prop} {B : Tag} :
    Regime.monotoneStepExt R R' newTags → (∀ k, newTags k → B ≤ k) → qtypPredTagBounded qt B →
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro h_mono hnewB hqtbound h_clean
  cases h_clean with
  | clean hpoison => exact qtypCleanUnder.clean hpoison
  | guard k htag hkR' hnotfun =>
      have hknew : ¬ newTags k := fun hnew => absurd (hnewB k hnew)
        (Nat.not_le.2 (qtypGuardTag_lt_of_predTagBounded hqtbound htag))
      have hRdef : R.lookup? k ≠ none := by
        rcases h_mono.2 k (by simp [hkR']) with hRne | hnew
        · exact hRne
        · exact absurd hnew hknew
      cases hkR : R.lookup? k with
      | none => exact (hRdef hkR).elim
      | some b =>
          cases h_mono.1 k b hknew hkR with
          | inl hkR'_preserved =>
              have hb : b = true := Option.some.inj (hkR'_preserved.symm.trans hkR')
              subst hb
              exact qtypCleanUnder.guard k htag hkR hnotfun
          | inr hkR'_none => simp [hkR'_none] at hkR'


/-- Extended-regime (`monotoneStepExt`) variant of `agreeValueUnder_clean_transport_by_cleanBack`.
    Rather than the four unbounded member-transport hypotheses and a `cleanBack` hypothesis,
    it threads a closure-tag bound `etypClosuresFullBounded qt.etyp B` through the recursion:
    every nested captured environment is fully bounded, so the bounded member transports
    (`memberVarsRegimeEvidence_monotoneExt`, `memberCvcrEvidence_monotoneExt`) and the bounded
    `cleanBack` (`cleanUnder_of_monotoneExt`) apply.  Used by the `ite`/`vlet` two-run proofs to
    transport clean agreement across an extern-extended regime step. -/
lemma agreeValueUnder_clean_transport_by_cleanBack_ext
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value} {newTags : Tag → Prop} {B : Tag}
    (h_mono : Regime.monotoneStepExt R R' newTags)
    (hnewB : ∀ k, newTags k → B ≤ k)
    (hbound : etypClosuresFullBounded qt.etyp B) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
  have hrec :
      (etypClosuresFullBounded qt.etyp B → qtypCleanUnder R' qt →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁) :=
    agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := fun qt v₀ v₁ _ =>
        etypClosuresFullBounded qt.etyp B → qtypCleanUnder R' qt →
          agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁)
      (motive_2 := fun σcap ρcap₀ ρcap₁ _ =>
        CapturedEnvFullBounded σcap B →
          agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
      (clean_eq_nonref_nonarrow := by
        intro qt v₀ v₁ hpoison hnotfun hnotref heq _hqb _hclean
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ hbody ihcap
          hqb _hclean
        have hcapbound : CapturedEnvFullBounded σcap B := by
          have hb := hqb; rw [hetyp] at hb
          have hb2 := hb tcl htcl; rw [hmatch] at hb2; exact hb2
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch (ihcap hcapbound)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₀)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₁)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁ hbody)
      (clean_internal_arrow_extern := by
        intro id x y argTyp argPoison argPred retSpec effects p tcls qt tcl σcap argQt cap memberCap ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          hqb _hclean
        have hcapbound : CapturedEnvFullBounded σcap B := by
          have hb := hqb; rw [hetyp] at hb
          have hb2 := hb tcl htcl; rw [hmatch] at hb2; exact hb2
        exact agreeValueUnder.clean_internal_arrow_extern hclean_internal hetyp htcl hmatch (ihcap hcapbound)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₀)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₁)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hqb _hclean
        exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          hqb _hclean
        have hcapbound : CapturedEnvFullBounded σcap B := by
          have hb := hqb; rw [hetyp] at hb
          have hb2 := hb tcl htcl; rw [hmatch.2] at hb2; exact hb2
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch (ihcap hcapbound)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₀)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₁)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (clean_internal_parrow_extern := by
        intro id x y argTyp argPoison argPred retSpec p tcls qt tcl σcap argQt cap memberCap ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ ihcap
          hqb _hclean
        have hcapbound : CapturedEnvFullBounded σcap B := by
          have hb := hqb; rw [hetyp] at hb
          have hb2 := hb tcl htcl; rw [hmatch] at hb2; exact hb2
        exact agreeValueUnder.clean_internal_parrow_extern hclean_internal hetyp htcl hmatch (ihcap hcapbound)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₀)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₀)
          (memberVarsRegimeEvidence_monotoneExt h_mono hnewB hcapbound hmemberVars₁)
          (memberCvcrEvidence_monotoneExt h_mono hnewB hcapbound hmemberCvcr₁)
          htyping₀ htyping₁
          hv₀ hv₁)
      (dirty_internal_parrow := by
        intro qt v₀ v₁ hdirty_internal hisParrow htyp1 htyp2 _hqb _hclean
        exact agreeValueUnder.dirty_internal_parrow hdirty_internal hisParrow htyp1 htyp2)
      (clean_ref := by
        intro ls l a₀ a₁ qt v₀ v₁ hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁ _hqb _hclean
        exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁)
      (withPred_true_eq := by
        intro k qt v₀ v₁ htag _hreg hnotfun hnotref heq _hqb hclean
        cases hclean with
        | clean hpoison =>
            exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq
        | guard k' htag' hk'R' _hnotfun' =>
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag'
                  _ = some k := htag
              exact Option.some.inj this
            have hreg : R'.lookup? k = some true := by
              simpa [hk] using hk'R'
            exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref heq)
      (withPred_true_ref := by
        intro k ls l a₀ a₁ qt v₀ v₁ htag _hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁ _hqb hclean
        cases hclean with
        | clean hpoison =>
            exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁
        | guard k' htag' hk'R' _hnotfun' =>
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag'
                  _ = some k := htag
              exact Option.some.inj this
            have hreg : R'.lookup? k = some true := by
              simpa [hk] using hk'R'
            exact agreeValueUnder.withPred_true_ref k htag hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁)
      (nil := by
        intro ρcap₀ ρcap₁ _hsb
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ _hcleanR hlookup1 hlookup2 htyp1 htyp2 hagree htail
          ihagree ihtail hsb
        have hhead : etypClosuresFullBounded qt.etyp B :=
          CapturedEnvFullBounded_member_etypClosures hsb (List.Mem.head _)
        have htail_b : CapturedEnvFullBounded σcap B := CapturedEnvFullBounded_tail hsb
        by_cases hcleanR' : qtypCleanUnder R' qt
        · exact agreeCapturedEnv.cons_clean hcleanR' hlookup1 hlookup2 htyp1 htyp2
            (ihagree hhead hcleanR') (ihtail htail_b)
        · exact agreeCapturedEnv.cons_dirty hcleanR' hlookup1 hlookup2 htyp1 htyp2 (ihtail htail_b))
      (cons_dirty := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihtail hsb
        have hhead : qtypPredTagBounded qt B :=
          CapturedEnvFullBounded_member_predTagBounded hsb (List.Mem.head _)
        have htail_b : CapturedEnvFullBounded σcap B := CapturedEnvFullBounded_tail hsb
        have hdirty' : ¬ qtypCleanUnder R' qt := by
          intro hcleanR'
          exact hdirty (cleanUnder_of_monotoneExt h_mono hnewB hhead hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 (ihtail htail_b))
      hagree
  exact hrec hbound hclean
