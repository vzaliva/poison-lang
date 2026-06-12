/-
  Auto-extracted from FaultRobustnessProofs.lean during StepFR operator refactor.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

lemma stepFR_literal
  
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hvtyp : ∀ θ, valueHasETyp θ v res.qualType.etyp)
  (hpoison : res.qualType.poison = false)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls)
  (hpredNo : res.qualType.pred = Predicate.noPred)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFR ctx e res predSat tm (registry := registry) := by
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
  -- Use world-free inversion lemma for literals
  have ⟨hcf₀, ho₀⟩ := terminatesTo_literal_inv' e v hval
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_literal_inv' e v hval
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard) hinq hqd
  have hbounded_res : TagMeaningBounded tm res.nextTag' := by
    have hnext : res.nextTag' = ctx.nextTag := by
      have hctx := congrArg TypeContext.nextTag hctxAfter
      simpa [ctxAfter] using hctx
    simpa [hnext] using hTmBounded
  have hcanon : IsCanonicalExtension tm ctx e res tm := by
    refine IsCanonicalExtension.refl hbounded_res ?_ hresTm
    simpa [hctxAfter] using hwfTm
  refine ⟨tm, BoundaryTagMeaningPost.of_isCanonical_predSat hcanon hpredlaws, hpredlaws, hresTm, ?_⟩
  -- StepFR existential has structure:
  -- ∃ θ₀' θ₁', wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
  --   valueHasETyp θ₀' o₀ res.qualType.etyp ∧ valueHasETyp θ₁' o₁ res.qualType.etyp ∧
  --   wfTagMeaningCtx ... ∧ wfTypeContext (ctxAfter ctx res) ∧ wfConfig cf₀ ∧ wfConfig cf₁ ∧
  --   runtimeInstantiatesCtx ... ∧ runtimeInstantiatesCtx ... ∧
  --   regimeConsistentWithCtx ... ∧ consistentWithRegime ... ∧ consistentWithRegime ... ∧
  --   agreeOnClean ... ∧ valueConsistentWithRegime ... ∧ valueConsistentWithRegime ... ∧ resultAgreesIfClean ...
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- valueHasETyp θ₀ o₀ res.qualType.etyp
    simp [ho₀]; exact hvtyp θ₀
  · -- valueHasETyp θ₁ o₁ res.qualType.etyp
    simp [ho₁]; exact hvtyp θ₁
  · -- wfTagMeaningCtx tm (ctxAfter ctx res)
    simpa [hctxAfter] using hwfTm
  · -- wfTypeContext (ctxAfter ctx res)
    simpa [hctxAfter] using hwf
  · -- TagBoundedCtx (ctxAfter ctx res)
    simpa [hctxAfter] using htagBounded
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
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpredNo])
      (ho₀ ▸ closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hvtyp θ₀) hnotfun)
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpredNo])
      (ho₁ ▸ closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hvtyp θ₁) hnotfun)
  · -- resultAgreesIfClean
    intro _hclean
    exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref (by simp [ho₀, ho₁])
  · -- ReservedDiscipline for θ₀'
    have hdecl : res.declared' = ctx.declaredExternRefs := by
      have := congrArg TypeContext.declaredExternRefs hctxAfter
      simpa [ctxAfter] using this
    rwa [hdecl]
  · -- ReservedDiscipline for θ₁'
    have hdecl : res.declared' = ctx.declaredExternRefs := by
      have := congrArg TypeContext.declaredExternRefs hctxAfter
      simpa [ctxAfter] using this
    rwa [hdecl]

lemma stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
  (masked : Tag → Prop)
  
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hvtyp : ∀ θ, valueHasETyp θ v res.qualType.etyp)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hpredNo : res.qualType.pred = Predicate.noPred)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctx e res predSat tm (registry := registry) := by
  intro hpredlaws _hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.refl_of_ctxAfter_eq
        hpredlaws hwfTm hTmBounded hctxAfter
        (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType
          hnotfun (by simp [qtypGuardDesc?, hpredNo]))
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hmasked_absent _hmasked_bounded _hbnd hcwr a pm hwfcfg hres hrd ht _hpc
  have ⟨hcf, ho⟩ := terminatesTo_literal_inv' e v hval
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  subst hcf
  have hvalc :
      valueConsistentWithRegimeMasked masked predSat ctx.regime res.qualType μ θ o := by
    exact valueConsistentWithRegimeMasked.noTag
      (by simp [qtypGuardTag, hpredNo])
      (ho ▸ closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType
        (hvtyp θ) hnotfun)
  exact
    singleRunFinalCleanWitness_of_same_state_maskedReg_param
      (masked := masked)
      (CtxCons := fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (ValCons := fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      (_predSat := predSat) (ctx := ctx) (res := res) (tm := tm)
      (μ := μ) (ρ := ρ) (θ := θ)
      (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry })
      (o := o) (a := a) (pm := pm)
      hctxAfter rfl (ho ▸ hvtyp θ) hcwr hvalc hwfTm hwf hric hreg hmasked_none
      hmasked_absent hwfcfg hrd
