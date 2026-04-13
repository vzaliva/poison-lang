/-
  StepFRSeq.lean - Fault-robustness proof for the seq case.

  Contains stepFR_seq and stepFRSingleRunFinalCleanPcTrue_seq.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

private def StepFRSingleRunFinalCleanPcTrueWithCtxValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      wfRealizationMap θ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ ρ θ →
      regimeConsistentWithCtx ctx →
      CtxCons ctx μ ρ θ →
      ∀ (a : Address) (pm : Bool),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } →
        terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o →
        ctx.pc = true →
        ∃ (θ' : RealizationMap),
          wfExtendsMap θ θ' ∧
          valueHasETyp θ' o res.qualType.etyp ∧
          runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
          ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
          PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
          FreshCleanLocsUnrealizedOneRun ctx res θ'

private abbrev StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (predSat : PredSat) (tm : TagMeaning) (fuel : Nat) : Prop :=
  ∀ m < fuel, ∀ (e : Expr) (ctx : TypeContext),
    wfTagMeaningCtx tm ctx →
    ∀ (res : TypeResult),
      typecheck ctx e m = .ok res →
      StepFRSingleRunFinalCleanPcTrueWithCtxValCons
        CtxCons ValCons ctx e res predSat tm

private lemma stepFRSingleRunFinalCleanPcTrue_seq_parametric
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH :
    StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
      CtxCons ValCons predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctx (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueWithCtxValCons
    CtxCons ValCons ctx (Expr.seq e1 e2) res predSat tm := by
  have htc' : typecheckSeq ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_seq_succ] using htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctx e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hctxCons a pm hwfcfg ht hpc
  have hstruct := terminatesTo_seq_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hstruct with ⟨cfg1, v1, ht_e1, ht_e2, _hpm1, _hpm2⟩
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm res1 htc1'
  have hTm1 : wfTagMeaningCtx tm (ctxAfter ctx res1) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm ctx e1 fuel' res1 hwfTm htc1'
  have hwf1 : wfTypeContext (ctxAfter ctx res1) :=
    wfTypeContext_of_wfTypeResult ctx res1
      (typecheckExpr_preserves_wfTypeResult ctx e1 fuel' res1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctx e1 fuel' res1 htc1')
  have hreg1 : regimeConsistentWithCtx (ctxAfter ctx res1) :=
    typecheckExpr_preserves_regimeConsistentWithCtx ctx e1 fuel' res1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := (wfConfig_preserved e1 _ cfg1 v1 ht_e1 hwfcfg).1
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hctxCons a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hv1, hric1, hctxCons1, hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [hctx', ctxAfter] using hTm1
  have hpc1 : ctx'.pc = true := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpc
  have hmono1 : Regime.monotoneStep ctx.regime res1.regime' :=
    regime_monotone ctx e1 fuel' res1 htc1'
  have hric1' : runtimeInstantiatesCtx ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', ctxAfter] using hric1
  have hreg1' : regimeConsistentWithCtx ctx' := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hreg1
  have hctxCons1' : CtxCons ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hctxCons1
  have hwf1' : wfTypeContext ctx' := by
    simpa [hctx', ctxAfter] using hwf1
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res htc2'
  rcases
    hIH2 hpredlaws hwfTm' cfg1.memory cfg1.varEnv θ1 cf o
      hθ1wf hwf1' hric1' hreg1' hctxCons1'
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hv2, hric2, hctxCons2, hvalc2, hpres2, _hfresh2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res cfg1.memory cf.memory θ1 θ2 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpres2
  have hclean_back :
      ∀ l qt_in qt_out,
        ctx.memEnv.lookup l = some qt_in →
        res.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true
        (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res)
        (by simpa [hctx', ctxAfter] using htc2')
        hwf1
        (by simpa [ctxAfter] using hpc)
        l qt_out hlookup_out
        (by simpa [ctxAfter] using typecheckExpr_mem_contains_preserved ctx e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctx.memEnv l _qt_in _hlookup_in))
        hclean_out
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [ctxAfter] using hlookup_mid, by simpa [ctxAfter] using hclean_mid⟩
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctx) (res1 := res1) (res2 := res)
        hclean_back hpres1 hpres2'
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θ2 := by
    intro l qt hnotIn hlookup hclean
    by_cases hcontains_mid : (ctxAfter ctx res1).memEnv.contains l
    · -- l introduced by e1's typing, inherited for e2
      obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res)
          (by simpa [hctx', ctxAfter] using htc2')
          hwf1
          (by simpa [ctxAfter] using hpc)
          l qt hlookup hcontains_mid hclean
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [ctxAfter] using hlookup_mid)
        (by simpa [ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2'
        hlookup_mid hlookup hclean
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
    · -- l not in intermediate context → also fresh for e2
      have hfresh2' : FreshCleanLocsUnrealizedOneRun (ctxAfter ctx res1) res θ2 :=
        by simpa [hctx', updateCtxFromResult, ctxAfter] using _hfresh2
      exact hfresh2' l qt hcontains_mid hlookup hclean
  refine ⟨θ2, hθext, hv2, ?_, ?_, ?_, hpres_final, hfresh_final⟩
  · simpa [hctxAfter] using hric2
  · simpa [hctxAfter] using hctxCons2
  · simpa [hctxAfter] using hvalc2

lemma stepFRSingleRunFinalCleanPcTrue_seq_maskedReg
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctx (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctx (Expr.seq e1 e2) res predSat tm := by
  have htc' : typecheckSeq ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_seq_succ] using htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctx e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hctxCons a pm hwfcfg ht hpc
  have hstruct := terminatesTo_seq_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hstruct with ⟨cfg1, v1, ht_e1, ht_e2, _hpm1, _hpm2⟩
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm res1 htc1'
  have hTm1 : wfTagMeaningCtx tm (ctxAfter ctx res1) :=
    typecheckExpr_preserves_wfTagMeaningCtx tm ctx e1 fuel' res1 hwfTm htc1'
  have hwf1 : wfTypeContext (ctxAfter ctx res1) :=
    wfTypeContext_of_wfTypeResult ctx res1
      (typecheckExpr_preserves_wfTypeResult ctx e1 fuel' res1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctx e1 fuel' res1 htc1')
  have hreg1 : regimeConsistentWithCtxMasked masked (ctxAfter ctx res1) :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctx e1 fuel' res1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := (wfConfig_preserved e1 _ cfg1 v1 ht_e1 hwfcfg).1
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hmasked_none hctxCons a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hv1, hric1, hctxCons1, hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [hctx', ctxAfter] using hTm1
  have hpc1 : ctx'.pc = true := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpc
  have hmono1 : Regime.monotoneStep ctx.regime res1.regime' :=
    regime_monotone ctx e1 fuel' res1 htc1'
  have hmasked_none1 : ∀ k, masked k → (ctxAfter ctx res1).regime.lookup? k = none := by
    intro k hk
    simpa [ctxAfter] using
      masked_lookup_none_of_monotoneStep
        (R := ctx.regime) (R' := res1.regime')
        hmasked_none hmono1 k hk
  have hric1' : runtimeInstantiatesCtx ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', ctxAfter] using hric1
  have hreg1' : regimeConsistentWithCtxMasked masked ctx' := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hreg1
  have hmasked_none1' : ∀ k, masked k → ctx'.regime.lookup? k = none := by
    intro k hk
    simpa [hctx', updateCtxFromResult, ctxAfter] using hmasked_none1 k hk
  have hctxCons1' :
      consistentWithRegimeMasked masked predSat ctx'.regime ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hctxCons1
  have hwf1' : wfTypeContext ctx' := by
    simpa [hctx', ctxAfter] using hwf1
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res htc2'
  rcases
    hIH2 hpredlaws hwfTm' cfg1.memory cfg1.varEnv θ1 cf o
      hθ1wf hwf1' hric1' hreg1' hmasked_none1' hctxCons1'
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hv2, hric2, hctxCons2, hvalc2, hpres2, _hfresh2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res cfg1.memory cf.memory θ1 θ2 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpres2
  have hclean_back :
      ∀ l qt_in qt_out,
        ctx.memEnv.lookup l = some qt_in →
        res.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true
        (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res)
        (by simpa [hctx', ctxAfter] using htc2')
        hwf1
        (by simpa [ctxAfter] using hpc)
        l qt_out hlookup_out
        (by simpa [ctxAfter] using typecheckExpr_mem_contains_preserved ctx e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctx.memEnv l _qt_in _hlookup_in))
        hclean_out
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [ctxAfter] using hlookup_mid, by simpa [ctxAfter] using hclean_mid⟩
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctx) (res1 := res1) (res2 := res)
        hclean_back hpres1 hpres2'
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θ2 := by
    intro l qt hnotIn hlookup hclean
    by_cases hcontains_mid : (ctxAfter ctx res1).memEnv.contains l
    · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res)
          (by simpa [hctx', ctxAfter] using htc2')
          hwf1
          (by simpa [ctxAfter] using hpc)
          l qt hlookup hcontains_mid hclean
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [ctxAfter] using hlookup_mid)
        (by simpa [ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2'
        hlookup_mid hlookup hclean
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
    · have hfresh2' : FreshCleanLocsUnrealizedOneRun (ctxAfter ctx res1) res θ2 :=
        by simpa [hctx', updateCtxFromResult, ctxAfter] using _hfresh2
      exact hfresh2' l qt hcontains_mid hlookup hclean
  refine ⟨θ2, hθext, hv2, ?_, ?_, ?_, hpres_final, hfresh_final⟩
  · simpa [hctxAfter] using hric2
  · simpa [hctxAfter] using hctxCons2
  · simpa [hctxAfter] using hvalc2

lemma stepFRSingleRunFinalCleanPcTrue_seq
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctx (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue ctx (Expr.seq e1 e2) res predSat tm := by
  exact
    stepFRSingleRunFinalCleanPcTrue_seq_parametric
      (CtxCons := fun ctx' μ' ρ' θ' =>
        consistentWithRegime predSat ctx'.regime ctx' μ' ρ' θ')
      (ValCons := valueConsistentWithRegime predSat)
      (ctx := ctx) (predSat := predSat) (tm := tm)
      (e1 := e1) (e2 := e2) (fuel' := fuel') (res := res)
      (IH := fun m hm e ctx' hwfTm' res' htc' =>
        IH m hm e ctx' hwfTm' res' htc')
      htc

lemma stepFR_seq
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.seq e1 e2) res predSat tm := by
  -- Parse typecheck result
  have htc' : typecheckSeq ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_seq_succ] using htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm htagBounded res1 htc1'
  -- Use world-free inversion lemma for seq
  have hstruct₀ := terminatesTo_seq_inv' e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, ht₀_e1, ht₀_e2, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_seq_inv' e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, ht₁_e1, ht₁_e2, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1, hres_agree1⟩
  have hwfTm' : wfTagMeaningCtx tm ctx' := by simpa [hctx', ctxAfter] using _hTm1
  have htagBounded1' : TagBoundedCtx ctx' := by
    simpa [hctx', ctxAfter] using _htagBounded1
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' htagBounded1' res htc2'
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
  have htagR1' : regimeConsistentWithCtx ctx' := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using htagR1
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hcwr₁1
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hagree_clean1
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1; simp only [Config.mk.injEq, true_and]; exact hpm_eq
  have ht₁_e2' : terminatesTo e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by rw [← hcfg₁1_eq]; exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]; exact hwfcf₁1
  -- Apply IH for e2
  -- Note: ctx'.regime = res1.regime' which may differ from ctxᵢ.regime
  -- Use regime monotonicity to relate them
  have h_mono : Regime.monotoneStep ctxᵢ.regime res1.regime' := regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hstep_e2 :=
    hIH2 hpredlaws hwfTm' cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' htagBounded1' hric₀1' hric₁1' htagR1' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, _htagBounded2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  -- IH2 gives agreeOnClean with (ctxAfter ctx' res).regime
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res, their regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  -- IH2 gives regimeConsistentWithCtx with output regime, transfer via hctxAfter
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  refine ⟨hresTm2, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · exact _hvtyp₀2
  · exact _hvtyp₁2
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · simpa [hctxAfter] using _htagBounded2
  · -- valueConsistentWithRegime for cf₀
    -- The result of `seq` is exactly the result of `e2`; reuse IH2.
    simpa [hctxAfter] using _hval_consist₀2
  · -- valueConsistentWithRegime for cf₁
    simpa [hctxAfter] using _hval_consist₁2
  -- Since res is directly the result of e2, hres_agree2 gives us the result directly
  -- IH2 gives resultAgreesIfClean with (ctxAfter ctx' res).regime = (ctxAfter ctxᵢ res).regime
  simpa [hctxAfter] using hres_agree2

-- World-free version of stepFRW_vlet
