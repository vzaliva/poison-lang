/-
  StepFROp.lean - Fault-robustness proofs for the binary and unary operator cases.

  Contains stepFR_op_with_expr_proof, stepFR_unaryop_with_expr_proof,
  stepFRSingleRunFinalCleanPcTrue_op_maskedReg_with_expr_proof, and
  stepFRSingleRunFinalCleanPcTrue_unaryop_maskedReg_with_expr_proof.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

lemma stepFRSingleRunFinalCleanPcTrue_unaryop_maskedReg_with_expr_proof
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (op : UnaryOp) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan : CanUse e)
  (hctxCurrent : CtxReach ctx)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse
      CtxReach
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v) (registry := registry))
  (htc : typecheck ctx (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctx (Expr.unaryop op e) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  have htc' : typecheckUnaryOp ctx op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime,
      h_ret_etyp, _h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctx op e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctx e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hframe hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves predSat tm ctx
        (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hframe htc
  intro μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht hpc P hP hroot
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctx hctxCurrent hcan hwfTm hTmBounded res1 htc1'
  have hstruct := terminatesTo_unaryop_inv' op e
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  rcases hstruct with ⟨cfg', v', ht_e, h_evalop, hmem, hvar, _hnext, _hpure⟩
  rcases
    (hIH hpredlaws (hframe.of_log_eq (typecheckUnaryOp_tagLog htc' htc1)) hwfTm hTmBounded).2 μ ρ θ cfg' v'
      hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht_e hpc hP (hP.closed hroot (SubStep.unary (f := fuel')))
    with ⟨θ', hθext, hvtyp, hric', hcwr', hvalc', hpres', _hfresh', _hrd'⟩
  have h_decl : res.declared' = res1.declared' := by
    simp only [typecheckUnaryOp, bind, Except.bind, pure, Except.pure] at htc'
    change typecheckExpr ctx e fuel' = .ok res1 at htc1'
    rw [htc1'] at htc'
    simp only at htc'
    cases hqt : res1.qualType with
    | mk _etyp _p _pred =>
      simp only [hqt] at htc' h_op
      simp only [h_op] at htc'
      injection htc' with heq
      rw [← heq]
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl]
  have hvaltyp_final : valueHasETyp θ' o res.qualType.etyp := by
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v' o θ' res1.qualType.etyp result_etyp h_op h_evalop
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctx res).regime res.qualType cf.memory θ' o := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using
        (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact
      valueConsistentWithRegimeMasked.noTag
        (by simp [qtypGuardTag, h_ret_pred])
        (closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType
          hvaltyp_final hnotfun_res)
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' := by
    cases hpres' with
    | intro hpres_fn =>
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hlookup_out1 : res1.memEnv'.lookup l = some qt_out := by
          simpa [h_mem] using hlookup_out
        have hclean_out1 : qtypCleanUnder res1.regime' qt_out := by
          simpa [h_regime] using hclean_out
        simpa [hmem] using hpres_fn l qt_in qt_out hlookup_in hlookup_out1 hclean_out1
  refine ⟨θ', hθext, hvaltyp_final, ?_, ?_, hvalc_final, hpres_final, ?_, ?_⟩
  · simpa [hctxAfter, hmem, hvar] using hric'
  · simpa [hctxAfter, hmem, hvar] using hcwr'
  · intro l qt hnotIn hlookup hclean
    exact _hfresh' l qt hnotIn (by rwa [h_mem] at hlookup) (by rwa [h_regime] at hclean)
  · have hreg_cf : cf.registry = registry := by
      simpa using terminatesTo_preserves_registry ht
    have hreg_cfg' : cfg'.registry = registry := by
      simpa using terminatesTo_preserves_registry ht_e
    rw [hreg_cf, h_decl]
    rw [hreg_cfg'] at _hrd'
    exact _hrd'

lemma stepFR_op_with_expr_proof
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan1 : CanUse e1) (hcan2 : CanUse e2)
  (hctxCurrent : CtxReach ctxᵢ)
  (hctxAfter : ∀ {ctx : TypeContext} {res : TypeResult},
    CtxReach ctx → CtxReach (ctxAfter ctx res))
  (hOp : RegistryOperationalSafe registry)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (htc : typecheck ctxᵢ (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.op e1 op e2) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  -- Parse typecheck result
  have htc' : typecheckOp ctxᵢ e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime,
          h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctxᵢ e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext :=
    { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared' }
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using! htc2
  intro hpredlaws hframe hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ P₀ P₁ hprem hroot₀ hroot₁
  have hlogOp := typecheckOp_tagLog htc' htc1 htc2
  have hframe' := hframe.of_log_eq hlogOp
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hctxCurrent hcan1 hwfTm htagBounded res1 htc1'
  -- Use inversion lemma for binary op
  have hstruct₀ := terminatesTo_op_inv' e1 op e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, v₀2, ht₀_e1, ht₀_e2, h_evalop₀, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_op_inv' e1 op e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, v₁2, ht₁_e1, ht₁_e2, h_evalop₁, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hframe'.left hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e1 ht₁_e1 hprem
      (hprem.run₀.closed hroot₀ (SubStep.opLeft (f := fuel')))
      (hprem.run₁.closed hroot₁ (SubStep.opLeft (f := fuel')))
  rcases hstep_e1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1, hres_agree1, _hrd₀1, _hrd₁1⟩
  have hwfTm' : wfTagMeaningCtx tm1 ctx' := by
    simpa [ctx', ctxAfter] using _hTm1
  have htagBounded1' : TagBoundedCtx ctx' := by
    simpa [ctx', ctxAfter] using _htagBounded1
  have hTmBounded' : TagMeaningBounded tm1 ctx'.nextTag := by
    simpa [ctx', ctxAfter] using BoundaryTagMeaningPost.bounded hcanon1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' (by simpa [ctx', ctxAfter] using hctxAfter hctxCurrent)
      hcan2 hwfTm' htagBounded1' res2 htc2'
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
  have htagR1' : regimeConsistentWithCtx ctx' := by
    -- Comes directly from IH1; `ctx'` is exactly `ctxAfter ctxᵢ res1`.
    simpa [ctx', ctxAfter] using htagR1
  -- agreeOnClean from IH1 directly applies since ctx' = ctxAfter ctxᵢ res1
  have hctx'_eq : ctx' = ctxAfter ctxᵢ res1 := by simp [ctx', ctxAfter]
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simp only [hctx'_eq]
    exact hagree_clean1
  -- consistentWithRegime from IH1 uses (ctxAfter ctxᵢ res1).regime = res1.regime' = ctx'.regime
  -- So hcwr₀1 and hcwr₁1 directly give what we need
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hcwr₁1
  -- Apply IH for e2
  -- Note: cfg₀1.pureMode = cfg₁1.pureMode = pm (from inversion lemmas)
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  -- Thread the extern registry: cfg₀1 and cfg₁1 both inherit the default
  -- registry from their initial configs (via `beval_preserves_registry`).
  have hreg_cfg₀1 : cfg₀1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₀_e1
  have hreg_cfg₁1 : cfg₁1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₁_e1
  have hcfg₀1_eq : cfg₀1 = { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } :=
    config_eq_of_registry cfg₀1 registry hreg_cfg₀1
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
    cases cfg₁1 with
    | mk m v n pm r =>
      simp only [Config.mk.injEq, true_and]
      refine ⟨hpm_eq, ?_⟩
      simpa using hreg_cfg₁1
  have ht₀_e2' : terminatesTo e2
      { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }
      cf₀ v₀2 := by rw [← hcfg₀1_eq]; exact ht₀_e2
  have ht₁_e2' : terminatesTo e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }
      cf₁ v₁2 := by rw [← hcfg₁1_eq]; exact ht₁_e2
  have hwfcf₀1' : wfConfig
      { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₀1_eq]; exact hwfcf₀1
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } := by
    rw [← hcfg₁1_eq]; exact hwfcf₁1
  -- Thread RegistryReservedWF through e1 evaluation to get it for e2's starting config
  have hres₀1 : RegistryReservedWF registry cfg₀1.memory cfg₀1.nextAddr := by
    apply RegistryReservedWF_mono hres₀
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 v₀1 hOp ht₀_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry }
        cfg₀1 v₀1 hOp ht₀_e1
  have hres₁1 : RegistryReservedWF registry cfg₁1.memory cfg₁1.nextAddr := by
    apply RegistryReservedWF_mono hres₁
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 v₁1 hOp ht₁_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry }
        cfg₁1 v₁1 hOp ht₁_e1
  -- Thread ReservedDiscipline through e1 evaluation using IH1 output
  have hrd₀1 : ReservedDiscipline registry ctx'.declaredExternRefs θ₀1 := by
    simp only [ctx']
    rw [← hreg_cfg₀1]
    exact _hrd₀1
  have hrd₁1 : ReservedDiscipline registry ctx'.declaredExternRefs θ₁1 := by
    simp only [ctx']
    rw [← hreg_cfg₁1]
    exact _hrd₁1
  have hroot₀2 : P₀ ⟨ctx', e2, fuel',
      { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [hctx'_eq, ← hcfg₀1_eq]
    exact hprem.run₀.closed hroot₀ (SubStep.opRight (f := fuel') htc1' ht₀_e1)
  have hroot₁2 : P₁ ⟨ctx', e2, fuel',
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry }⟩ := by
    rw [hctx'_eq, ← hcfg₁1_eq]
    exact hprem.run₁.closed hroot₁ (SubStep.opRight (f := fuel') htc1' ht₁_e1)
  have hstep_e2 :=
    hIH2 hpredlaws1 (hframe'.next hcanon1.within) hwfTm' hTmBounded' cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ v₀2 v₁2
      hθ₀1wf hθ₁1wf hwf1' htagBounded1' hric₀1' hric₁1' htagR1' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1' hwfcf₁1' hres₀1 hres₁1 hrd₀1 hrd₁1
      ht₀_e2' ht₁_e2' hprem hroot₀2 hroot₁2
  rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, _htagBounded2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2, hres_agree2, _hrd₀2, _hrd₁2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have h_decl_op_early : res.declared' = res2.declared' := by
    unfold typecheckOp at htc'
    simp only [bind, Except.bind, pure, Except.pure] at htc'
    change typecheckExpr ctxᵢ e1 fuel' = .ok res1 at htc1'
    change typecheckExpr ctx' e2 fuel' = .ok res2 at htc2'
    rw [htc1'] at htc'
    cases hqt1 : res1.qualType with
    | mk _etyp1 _p1 _pred1 =>
      simp only [hqt1] at htc'
      rw [htc2'] at htc'
      cases hqt : res2.qualType with
      | mk _etyp _p _pred =>
        simp only [hqt, hqt1] at htc' h_op
        rw [h_op] at htc'
        injection htc' with heq
        rw [← heq]
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl_op_early]
  -- IH2 gives agreeOnClean predSat (ctxAfter ctx' res2).regime ...
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res2, the regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  -- IH2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) (ctxAfter ctx' res2).regime
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res2, this directly gives what we need
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  have hresTm : QTypRespectsTagMeaning tm2 res.qualType := by
    have hnonfun_args :
        res1.qualType.etyp.isFunctionType = false ∧
        res2.qualType.etyp.isFunctionType = false ∧
        result_etyp.isFunctionType = false :=
      opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_args.2.2
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_ret_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm2 res.qualType hnotfun_res hguard) hinq hqd
  have hboundary_op : BoundaryTagMeaningPost ctxᵢ res predSat tm tm2 := by
    exact ⟨TagMeaningExtends.trans
        (BoundaryTagMeaningPost.extends_tm hcanon1)
        (BoundaryTagMeaningPost.extends_tm hcanon2),
      by simpa [h_ntag] using BoundaryTagMeaningPost.bounded hcanon2,
      by simpa [hctxAfter] using BoundaryTagMeaningPost.wfCtx hcanon2,
      hresTm,
      hpredlaws2,
      (hcanon1.within.append hcanon2.within).of_log_eq hlogOp.symm⟩
  refine ⟨tm2, hboundary_op, hpredlaws2, hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_, ?_, ?_⟩
  · -- valueHasETyp θ₀2 o₀ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v₀1 v₀2 o₀ θ₀2 res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₀
  · -- valueHasETyp θ₁2 o₁ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v₁1 v₁2 o₁ θ₁2 res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₁
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · -- TagBoundedCtx
    simpa [hctxAfter] using _htagBounded2
  · -- valueConsistentWithRegime for cf₀
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opEType_implies_nonfun op res1.qualType.etyp
        res2.qualType.etyp result_etyp h_op).2.2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalOp op v₀1 v₀2 o₀ θ₀2
              res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₀)
        hnotfun_res')
  · -- valueConsistentWithRegime for cf₁
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opEType_implies_nonfun op res1.qualType.etyp
        res2.qualType.etyp result_etyp h_op).2.2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalOp op v₁1 v₁2 o₁ θ₁2
              res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₁)
        hnotfun_res')
  · -- resultAgreesIfClean
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
    -- hres_agree1 expects qtypCleanUnder (ctxAfter ctxᵢ res1).regime from IH1
    have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := qtypCleanUnder.clean hjoin_12.1
    -- hres_agree2 expects qtypCleanUnder (ctxAfter ctx' res2).regime from IH2
    have hclean2 : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType := qtypCleanUnder.clean hjoin_12.2
    have hagree_v1 :
        agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 :=
      hres_agree1 hclean1
    have hagree_v2 :
        agreeValueUnder predSat (ctxAfter ctx' res2).regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType v₀2 v₁2 :=
      hres_agree2 hclean2
    have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
      intro ⟨ls, h_etyp⟩
      have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
        simp [h_etyp, opEType?]
      rw [hnone] at h_op; cases h_op
    have hnotref2 : ¬ ∃ ls, res2.qualType.etyp = ETyp.ref ls := by
      intro ⟨ls, h_etyp⟩
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
    have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
      intro ⟨ls, h_etyp⟩
      have h_etyp' : result_etyp = ETyp.ref ls := by simpa [h_ret_etyp] using h_etyp
      have h_op' : opEType? op res1.qualType.etyp res2.qualType.etyp = some (ETyp.ref ls) := by
        simpa [h_etyp'] using h_op
      exact (opEType_ne_ref op res1.qualType.etyp res2.qualType.etyp ls) h_op'
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_args.2.2
    exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq
  · -- ReservedDiscipline for cf₀
    rw [h_decl_op_early]
    exact _hrd₀2
  · -- ReservedDiscipline for cf₁
    rw [h_decl_op_early]
    exact _hrd₁2

lemma stepFR_unaryop_with_expr_proof
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (op : UnaryOp) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan : CanUse e)
  (hctxCurrent : CtxReach ctxᵢ)
  (hOp : RegistryOperationalSafe registry)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (htc : typecheck ctxᵢ (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.unaryop op e) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  have htc' : typecheckUnaryOp ctxᵢ op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctxᵢ op e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hframe hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ P₀ P₁ hprem hroot₀ hroot₁
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hctxCurrent hcan hwfTm htagBounded res1 htc1'
  -- Use inversion lemma for unaryop
  have hstruct₀ := terminatesTo_unaryop_inv' op e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀', v₀', ht₀_e, h_evalop₀, hmem₀, hvar₀, _hnext₀, _hpure₀⟩
  have hstruct₁ := terminatesTo_unaryop_inv' op e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁', v₁', ht₁_e, h_evalop₁, hmem₁, hvar₁, _hnext₁, _hpure₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws (hframe.of_log_eq (typecheckUnaryOp_tagLog htc' htc1)) hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e ht₁_e hprem
      (hprem.run₀.closed hroot₀ (SubStep.unary (f := fuel')))
      (hprem.run₁.closed hroot₁ (SubStep.unary (f := fuel')))
  rcases hstep_e with ⟨tm_e, hcanon_e, hpredlaws_e, hresTm_e, hstep_e⟩
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, _hvtyp₀, _hvtyp₁, _hTm, hwf', _htagBounded', _hwfcf₀', _hwfcf₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e, _hrd₀_e, _hrd₁_e⟩
  have h_decl_unary : res.declared' = res1.declared' := by
    simp only [typecheckUnaryOp, bind, Except.bind, pure, Except.pure] at htc'
    change typecheckExpr ctxᵢ e fuel' = .ok res1 at htc1'
    rw [htc1'] at htc'
    simp only at htc'
    cases hqt : res1.qualType with
    | mk _etyp _p _pred =>
      simp only [hqt] at htc' h_op
      simp only [h_op] at htc'
      injection htc' with heq
      rw [← heq]
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl_unary]
  -- IH gives agreeOnClean with output regime (ctxAfter ctxᵢ res1).regime = res1.regime'
  -- Since ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 (for unaryop), regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  -- IH gives regimeConsistentWithCtx with output regime
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using hreg'
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hcwr₀'
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hcwr₁'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved (Expr.unaryop op e) _ cf₀ o₀ hOp hres₀.toBelow ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved (Expr.unaryop op e) _ cf₁ o₁ hOp hres₁.toBelow ht₁ hwfcfg₁).1
  have hresTm : QTypRespectsTagMeaning tm_e res.qualType := by
    have hnonfun_arg :
        res1.qualType.etyp.isFunctionType = false ∧
        result_etyp.isFunctionType = false :=
      opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_arg.2
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_ret_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm_e res.qualType hnotfun_res hguard) hinq hqd
  have hboundary_unary : BoundaryTagMeaningPost ctxᵢ res predSat tm tm_e := by
    exact ⟨BoundaryTagMeaningPost.extends_tm hcanon_e,
      by simpa [h_ntag] using BoundaryTagMeaningPost.bounded hcanon_e,
      by simpa [hctxAfter] using BoundaryTagMeaningPost.wfCtx hcanon_e,
      hresTm,
      hpredlaws_e,
      hcanon_e.within.of_log_eq (typecheckUnaryOp_tagLog htc' htc1).symm⟩
  refine ⟨tm_e, hboundary_unary, hpredlaws_e, hresTm, ?_⟩
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_, ?_, ?_⟩
  · -- valueHasETyp θ₀' o₀ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v₀' o₀ θ₀' res1.qualType.etyp result_etyp h_op h_evalop₀
  · -- valueHasETyp θ₁' o₁ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v₁' o₁ θ₁' res1.qualType.etyp result_etyp h_op h_evalop₁
  · simpa [hctxAfter] using _hTm
  · simpa [hctxAfter] using hwf'
  · -- TagBoundedCtx
    simpa [hctxAfter] using _htagBounded'
  · -- valueConsistentWithRegime for cf₀
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalUnaryOp op v₀' o₀ θ₀'
              res1.qualType.etyp result_etyp h_op h_evalop₀)
        hnotfun_res')
  · -- valueConsistentWithRegime for cf₁
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalUnaryOp op v₁' o₁ θ₁'
              res1.qualType.etyp result_etyp h_op h_evalop₁)
        hnotfun_res')
  · -- resultAgreesIfClean
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
    -- hres_agree_e expects qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType
    have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := by
      exact qtypCleanUnder.clean hres1_poison
    have hagree_v :
        agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType v₀' v₁' :=
      hres_agree_e hclean1
    have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
      intro hcontra
      rcases hcontra with ⟨ls, h_etyp⟩
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
          some o₀ = LeanPoison.evalUnaryOp op v₀' := by symm; exact h_evalop₀
          _ = some o₁ := hEval₁'
      exact Option.some.inj this
    have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
      intro hcontra
      rcases hcontra with ⟨ls, h_etyp⟩
      have h_etyp' : result_etyp = ETyp.ref ls := by
        simpa [h_ret_etyp] using h_etyp
      have h_op' : opUnaryEType? op res1.qualType.etyp = some (ETyp.ref ls) := by
        simpa [h_etyp'] using h_op
      exact (opUnaryEType_ne_ref op res1.qualType.etyp ls) h_op'
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_arg.2
    exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq
  · -- ReservedDiscipline for cf₀
    have hreg_cf₀ : cf₀.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₀
    have hreg_cfg₀' : cfg₀'.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₀_e
    rw [hreg_cf₀, h_decl_unary]
    rw [hreg_cfg₀'] at _hrd₀_e
    exact _hrd₀_e
  · -- ReservedDiscipline for cf₁
    have hreg_cf₁ : cf₁.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₁
    have hreg_cfg₁' : cfg₁'.registry = registry := by
      simpa using terminatesTo_preserves_registry ht₁_e
    rw [hreg_cf₁, h_decl_unary]
    rw [hreg_cfg₁'] at _hrd₁_e
    exact _hrd₁_e

lemma stepFRSingleRunFinalCleanPcTrue_op_maskedReg_with_expr_proof
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan1 : CanUse e1) (hcan2 : CanUse e2)
  (hctxCurrent : CtxReach ctx)
  (hctxAfter : ∀ {ctx : TypeContext} {res : TypeResult},
    CtxReach ctx → CtxReach (ctxAfter ctx res))
  (hOp : RegistryOperationalSafe registry)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse
      CtxReach
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v) (registry := registry))
  (htc : typecheck ctx (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctx (Expr.op e1 op e2) res predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry) := by
  have htc' : typecheckOp ctx e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag,
      h_regime, h_ret_etyp, _h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctx e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext := {
    ctx with
      memEnv := res1.memEnv'
      tagEnv := res1.tagEnv'
      nextLoc := res1.nextLoc'
      nextTag := res1.nextTag'
      regime := res1.regime'
      declaredExternRefs := res1.declared'
  }
  have htc1' : typecheck ctx e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using! htc2
  intro hpredlaws hframe hwfTm hTmBounded
  have hframe' := hframe.of_log_eq (typecheckOp_tagLog htc' htc1 htc2)
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves predSat tm ctx
        (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hframe htc
  intro μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht hpc P hP hroot
  have hstruct := terminatesTo_op_inv' e1 op e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  rcases hstruct with ⟨cfg1, v1, v2, ht_e1, ht_e2, h_evalop, hpm1, hpm2⟩
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hctxCurrent hcan1 hwfTm hTmBounded res1 htc1'
  have hIH1Inst := hIH1 hpredlaws hframe'.left hwfTm hTmBounded
  rcases hIH1Inst.1 with ⟨tm1, hcanon1, hpredlaws1, _hresTm1, hTm1, hwithin1⟩
  have hwf1 : wfTypeContext (ctxAfter ctx res1) :=
    wfTypeContext_of_wfTypeResult ctx res1
      (typecheckExpr_preserves_wfTypeResult ctx e1 fuel' res1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctx e1 fuel' res1 htc1')
  have hreg1 : regimeConsistentWithCtxMasked masked (ctxAfter ctx res1) :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctx e1 fuel' res1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := by
    exact (wfConfig_preserved e1 _ cfg1 v1 hOp _hres.toBelow ht_e1 hwfcfg).1
  rcases
    hIH1Inst.2 μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht_e1 hpc hP (hP.closed hroot (SubStep.opLeft (f := fuel')))
    with ⟨θ1, hθext1, hv1, hric1, hcwr1, hvalc1, hpres1, _hfresh1, _hrd1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm1 ctx' := by
    simpa [ctx', ctxAfter] using hTm1
  have hTmBounded' : TagMeaningBounded tm1 ctx'.nextTag := by
    simpa [ctx', ctxAfter] using
      IsCanonicalExtension.bounded hcanon1
  have hwf1' : wfTypeContext ctx' := by
    simpa [ctx', ctxAfter] using hwf1
  have hric1' : runtimeInstantiatesCtx ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [ctx', ctxAfter] using hric1
  have hreg1' : regimeConsistentWithCtxMasked masked ctx' := by
    simpa [ctx', ctxAfter] using hreg1
  have hcwr1' :
      consistentWithRegimeMasked masked predSat ctx'.regime ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [ctx', ctxAfter] using hcwr1
  have hpc1 : ctx'.pc = true := by
    simp [ctx']
    exact hpc
  have hmono1 := regime_monotoneExt ctx e1 fuel' res1 htc1'
  have hmasked_none1 : ∀ k, masked k → (ctxAfter ctx res1).regime.lookup? k = none := by
    intro k hk
    exact masked_lookup_none_of_monotoneStepExt
      hmasked_none (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono1 k hk
  have hmasked_none1' : ∀ k, masked k → ctx'.regime.lookup? k = none := by
    intro k hk
    simpa [ctx', ctxAfter] using hmasked_none1 k hk
  have hbnd1 : TagBoundedCtx (ctxAfter ctx res1) :=
    typecheckExpr_preserves_TagBoundedCtx ctx e1 fuel' res1 (by simpa [typecheck] using htc1') hbnd
  have hbnd1' : TagBoundedCtx ctx' := by simpa [ctx', ctxAfter] using hbnd1
  have hmasked_bounded1' : ∀ k, masked k → k < ctx'.nextTag := by
    have hb : ctx.nextTag ≤ res1.nextTag' := typecheck_nextTag_mono ctx e1 fuel' res1 htc1'
    exact fun k hk => by simpa [ctx'] using Nat.lt_of_lt_of_le (hmasked_bounded k hk) hb
  have hmasked_absent1 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx res1) :=
    typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
      masked ctx e1 fuel' res1 hmasked_absent hmasked_none hmasked_bounded htc1'
  have hmasked_absent1' : MaskedTagsAbsentFromTrueTagEnv masked ctx' := by
    simpa [ctx', ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' (by simpa [ctx', ctxAfter] using hctxAfter hctxCurrent)
      hcan2 hwfTm' hTmBounded' res2 htc2'
  -- Thread extern registry: cfg1 inherits default registry from initial config.
  have hreg_cfg1 : cfg1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht_e1
  have hcfg1_eq : cfg1 = { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } :=
    config_eq_of_registry cfg1 registry hreg_cfg1
  have hwfcfg1' : wfConfig { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } := by
    rw [← hcfg1_eq]; exact hwfcfg1
  have ht_e2' : terminatesTo e2 { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry } cf v2 := by
    rw [← hcfg1_eq]; exact ht_e2
  -- Thread RegistryReservedWF and ReservedDiscipline through e1 evaluation for e2's starting config
  have hres1_single : RegistryReservedWF registry cfg1.memory cfg1.nextAddr := by
    apply RegistryReservedWF_mono _hres
    · exact terminatesTo_memory_contains_mono e1
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
        cfg1 v1 hOp ht_e1
    · exact terminatesTo_nextAddr_mono e1
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }
        cfg1 v1 hOp ht_e1
  have hrd1_single : ReservedDiscipline registry ctx'.declaredExternRefs θ1 := by
    simp only [ctx']
    rw [← hreg_cfg1]
    exact _hrd1
  have hroot2 : P ⟨ctx', e2, fuel',
      { memory := cfg1.memory, varEnv := cfg1.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }⟩ := by
    have hctx'_eq : ctx' = ctxAfter ctx res1 := by simp [ctx', ctxAfter]
    rw [hctx'_eq, ← hcfg1_eq]
    exact hP.closed hroot (SubStep.opRight (f := fuel') htc1' ht_e1)
  rcases
    (hIH2 hpredlaws1 (hframe'.next hwithin1) hwfTm' hTmBounded').2 cfg1.memory cfg1.varEnv θ1 cf v2
      hθ1wf hwf1' hric1' hreg1' hmasked_none1' hmasked_absent1' hmasked_bounded1' hbnd1' hcwr1'
      cfg1.nextAddr cfg1.pureMode hwfcfg1' hres1_single hrd1_single ht_e2' hpc1 hP hroot2
    with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2, _hfresh2, _hrd2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have h_decl_op2 : res.declared' = res2.declared' := by
    unfold typecheckOp at htc'
    simp only [bind, Except.bind, pure, Except.pure] at htc'
    change typecheckExpr ctx e1 fuel' = .ok res1 at htc1'
    change typecheckExpr ctx' e2 fuel' = .ok res2 at htc2'
    rw [htc1'] at htc'
    cases hqt1 : res1.qualType with
    | mk _etyp1 _p1 _pred1 =>
      simp only [hqt1] at htc'
      rw [htc2'] at htc'
      cases hqt : res2.qualType with
      | mk _etyp _p _pred =>
        simp only [hqt, hqt1] at htc' h_op
        rw [h_op] at htc'
        injection htc' with heq
        rw [← heq]
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl_op2]
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res2 cfg1.memory cf.memory θ1 θ2 := by
    simpa [ctx', ctxAfter] using hpres2
  have hclean_back :
      ∀ l qt_in qt_out,
        ctx.memEnv.lookup l = some qt_in →
        res2.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res2.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true
        (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res2)
        (by simpa [ctx', ctxAfter] using! htc2')
        hwf1 hbnd1
        (by simpa [ctxAfter] using hpc)
        l qt_out
        (by simpa using hlookup_out)
        (by simpa [ctxAfter] using typecheckExpr_mem_contains_preserved ctx e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctx.memEnv l _qt_in _hlookup_in))
        (by simpa using hclean_out)
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [ctxAfter] using hlookup_mid, by simpa [ctxAfter] using hclean_mid⟩
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    have hpres_to_res2 :
        PreservesInheritedFinalCleanLocsOneRun ctx res2 μ cf.memory θ θ2 := by
      exact
        PreservesInheritedFinalCleanLocsOneRun.compose
          (ctx := ctx) (res1 := res1) (res2 := res2)
          hclean_back hpres1 hpres2'
    rcases hpres_to_res2 with ⟨hpres_fn⟩
    refine ⟨?_⟩
    intro l qt_in qt_out hlookup_in hlookup_out hclean_out
    have hlookup_out2 : res2.memEnv'.lookup l = some qt_out := by
      simpa [h_mem] using hlookup_out
    have hclean_out2 : qtypCleanUnder res2.regime' qt_out := by
      simpa [h_regime] using hclean_out
    exact hpres_fn l qt_in qt_out hlookup_in hlookup_out2 hclean_out2
  have hvaltyp_final : valueHasETyp θ2 o res.qualType.etyp := by
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v1 v2 o θ2 res1.qualType.etyp res2.qualType.etyp result_etyp
      (OpEType.complete h_op) h_evalop
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctx res).regime res.qualType cf.memory θ2 o := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using
        (opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op).2.2
    exact
      valueConsistentWithRegimeMasked.noTag
        (by simp [qtypGuardTag, h_ret_pred])
        (closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType
          hvaltyp_final hnotfun_res)
  have hcfg_eq : cfg1.pureMode = pm := by
    simpa using hpm1
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θ2 := by
    intro l qt hnotIn hlookup hclean
    have hlookup2 : res2.memEnv'.lookup l = some qt := by rwa [h_mem] at hlookup
    have hclean2 : qtypCleanUnder res2.regime' qt := by rwa [h_regime] at hclean
    by_cases hcontains_mid : (ctxAfter ctx res1).memEnv.contains l
    · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res2)
          (by simpa [ctx', ctxAfter] using! htc2')
          hwf1 hbnd1
          (by simpa [ctxAfter] using hpc)
          l qt hlookup2 hcontains_mid hclean2
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [ctxAfter] using hlookup_mid)
        (by simpa [ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2'
        hlookup_mid hlookup2 hclean2
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
    · have hfresh2' : FreshCleanLocsUnrealizedOneRun (ctxAfter ctx res1) res2 θ2 :=
        by simpa [ctx', ctxAfter] using _hfresh2
      exact hfresh2' l qt hcontains_mid hlookup2 hclean2
  refine ⟨θ2, hθext, hvaltyp_final, ?_, ?_, hvalc_final, hpres_final, hfresh_final, ?_⟩
  · simpa [hctxAfter, hcfg_eq] using hric2
  · simpa [hctxAfter, hcfg_eq] using hcwr2
  · rw [h_decl_op2]
    exact _hrd2

