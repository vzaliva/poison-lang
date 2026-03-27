/-
  FaultRobustnessProofs.lean - Orchestration of fault-robustness proofs.

  Imports all per-operator StepFR* files and assembles the step-level IOFree
  theorem and final fault-robustness bridges.

  Each stepFR_* case proof lives in its own StepFR*.lean file.
  Shared infrastructure is in StepFR.lean.
-/
import LeanProofs.StepFR
import LeanProofs.StepFRApp
import LeanProofs.StepFRAssign
import LeanProofs.StepFRLiteral
import LeanProofs.StepFRVar
import LeanProofs.StepFROp
import LeanProofs.StepFRFnPfn
import LeanProofs.StepFRIte
import LeanProofs.StepFRDeref
import LeanProofs.StepFRNewRef
import LeanProofs.StepFRSeq
import LeanProofs.StepFRVlet

open List
open List.Mem
open Std
open scoped MemoryTypeEnv



private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree
  (masked : Tag → Prop)
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  ∀ fuel res,
    typecheck .ioFree ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      .ioFree ctxᵢ e res predSat tm := by
  intro fuel res htc
  revert masked e ctxᵢ res htc
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
      intro masked e ctxᵢ res htc
      have IH' :
          ∀ m < n, ∀ (masked' : Tag → Prop) (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
            typecheck .ioFree ctx' e' m = .ok res' →
            StepFRSingleRunFinalCleanPcTrueMaskedRegParam
              masked'
              (fun ctx μ ρ θ =>
                consistentWithRegimeMasked masked' predSat ctx.regime ctx μ ρ θ)
              (fun R qt μ θ v =>
                valueConsistentWithRegimeMasked masked' predSat R qt μ θ v)
              .ioFree ctx' e' res' predSat tm := by
        intro m hm masked' e' ctx' res' htc'
        exact IH m hm masked' e' ctx' res' htc'
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm Expr.unit res Value.unit hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.unit)
                  hnotfun hpredNo hctxAfter
          | num k =>
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
              have hval : Expr.toValue? (Expr.num k) = some (Value.num k) := by
                simp [Expr.toValue?]
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.num k) res (Value.num k) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.num k)
                  hnotfun hpredNo hctxAfter
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.bool b) res (Value.bool b) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.bool b)
                  hnotfun hpredNo hctxAfter
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.str s) res (Value.str s) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.str s)
                  hnotfun hpredNo hctxAfter
          | var name =>
              exact
                stepFRSingleRunFinalCleanPcTrue_var_maskedReg
                  masked .ioFree
                  ctxᵢ predSat tm name res fuel
                  htc
          | op e1 op e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_op_maskedReg
                      masked ctxᵢ predSat tm e1 e2 op fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | unaryop uop e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_unaryop_maskedReg
                      masked ctxᵢ predSat tm e uop fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | ite e1 e2 e3 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_ite_succ, typecheckIf] at htc
              | succ fuel' =>
                  unfold StepFRSingleRunFinalCleanPcTrueMaskedRegParam
                  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
                    simpa [typecheck, typecheckExpr_ite_succ] using htc
                  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                  rcases hstruct with h1 | hrest
                  · rcases h1 with
                      ⟨k, deps, hmatch, hregime_true, res1, htc1, hbool, res2, htc2,
                        hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', _hpoison, hetyp⟩
                    intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
                    let ctxPure : TypeContext := { ctxᵢ with pureCtx := true }
                    let ctxTrue : TypeContext := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
                    have htc1' : typecheck .ioFree ctxPure e1 fuel' = .ok res1 := by
                      simpa [ctxPure, typecheck, Nat.succ_sub_one] using htc1
                    have hwfTm_pure : wfTagMeaningCtx tm ctxPure := by
                      simpa [ctxPure, wfTagMeaningCtx] using hwfTm
                    have hwf_pure : wfTypeContext ctxPure := by
                      simpa [ctxPure, wfTypeContext] using hwf
                    have htagR_pure : regimeConsistentWithCtxMasked masked ctxPure := by
                      simpa [ctxPure, regimeConsistentWithCtxMasked] using htagR
                    have hmasked_none_pure :
                        ∀ t, masked t → ctxPure.regime.lookup? t = none := by
                      simpa [ctxPure] using hmasked_none
                    have hcwr_pure :
                        consistentWithRegimeMasked masked predSat ctxPure.regime ctxPure μ ρ θ := by
                      simpa [ctxPure, consistentWithRegimeMasked] using hcwr
                    have hpc_pure : ctxPure.pc = true := by
                      simpa [ctxPure] using hpc
                    have hIH_e1 := IH' fuel' (by omega) masked e1 ctxPure res1 htc1'
                    have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
                    rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                    rcases
                        hIH_e1 hpredlaws hwfTm_pure μ ρ θ cfg1 (Value.bool b)
                          hθwf hwf_pure hric htagR_pure hmasked_none_pure hcwr_pure
                          a pm hwfcfg ht_e1 hpc_pure
                      with ⟨θ1, hθext1, _hv1, hric1, hcwr1, _hvalc1, hpres1⟩
                    have hcwr_unmasked :
                        consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ :=
                      consistentWithRegimeMasked_unmask
                        (masked := masked) (predSat := predSat)
                        (R := ctxᵢ.regime) (ctx := ctxᵢ)
                        (μ := μ) (ρ := ρ) (θ := θ)
                        hmasked_none hcwr
                    have hb_true : b = true := by
                      exact
                        matchGuard_runtime_branch_alignment
                          predSat tm .ioFree
                          ctxᵢ μ ρ θ a pm
                          hwfTm hpredlaws hric hcwr_unmasked
                          e1 k deps true b cfg1
                          hmatch hregime_true ht_e1
                    have ht_e2 : terminatesTo .ioFree e2 cfg1 cf o := by
                      cases hbranch with
                      | inl h => exact h.2
                      | inr h =>
                          have : false = true := by rw [← h.1, hb_true]
                          contradiction
                    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                    have hwfcfg1 : wfConfig cfg1 :=
                      (wfConfig_preserved .ioFree e1 _ cfg1 (Value.bool b) ht_e1 hwfcfg).1
                    have htc2' : typecheck .ioFree ctxTrue e2 fuel' = .ok res2 := by
                      simpa [ctxTrue, typecheck, Nat.succ_sub_one] using htc2
                    have hwfTm_true : wfTagMeaningCtx tm ctxTrue := by
                      simpa [ctxTrue, wfTagMeaningCtx] using hwfTm
                    have hwf_true : wfTypeContext ctxTrue := by
                      simpa [ctxTrue, wfTypeContext] using hwf
                    have htagR_true : regimeConsistentWithCtxMasked masked ctxTrue := by
                      exact
                        tagEnvConsistentWithRegimeMasked_insert_true
                          masked ctxᵢ.tagEnv ctxᵢ.regime k deps htagR hregime_true
                    have hmasked_none_true :
                        ∀ t, masked t → ctxTrue.regime.lookup? t = none := by
                      simpa [ctxTrue] using hmasked_none
                    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
                    have hric1' : runtimeInstantiatesCtx ctxTrue cfg1.memory cfg1.varEnv θ1 := by
                      have hsub : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
                        exact
                          typecheckExpr_pure_mem_subset_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1
                      exact
                        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
                          (ctx := ctxᵢ) (res := res1) (μ := cfg1.memory) (ρ := cfg1.varEnv) (θ := θ1)
                          (k := k) (deps := deps)
                          hsub hric1
                    have hcwr1' :
                        consistentWithRegimeMasked masked predSat ctxTrue.regime ctxTrue
                          cfg1.memory cfg1.varEnv θ1 := by
                      refine
                        consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
                          masked predSat ctxᵢ res1
                          cfg1.memory cfg1.varEnv θ1
                          k deps
                          ?_ ?_ hcwr1
                      · intro k' b' hk
                        exact
                          typecheckExpr_pure_regime_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 k' b' hk
                      · intro l qt k' hlookup hguard hRdef
                        exact
                          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 l qt k' hlookup hguard hRdef
                    have hpc_true : ctxTrue.pc = true := by
                      simpa [ctxTrue] using hpc
                    have hpredNo : res.qualType.pred = Predicate.noPred := by
                      exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                    have hIH_e2 := IH' fuel' (by omega) masked e2 ctxTrue res2 htc2'
                    rcases
                        hIH_e2 hpredlaws hwfTm_true
                          cfg1.memory cfg1.varEnv θ1 cf o
                          hθ1wf hwf_true hric1' htagR_true hmasked_none_true hcwr1'
                          cfg1.nextAddr cfg1.pureMode hwfcfg1
                          ht_e2 hpc_true
                      with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2⟩
                    have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                    have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxTrue res2 := by
                      simp [ctxAfter, ctxTrue, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
                    have hpres_final :
                        PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ2 := by
                      refine ⟨?_⟩
                      intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                      rcases
                          typecheckExpr_clean_lookup_origin_of_pc_true
                            ctxTrue e2 fuel' res2 htc2 hpc_true
                            l qt_out (by simpa [hmemEnv] using hlookup_out)
                            (by simpa [hregime'] using hclean_out)
                        with ⟨qt_mid, hlookup_mid_true, hclean_mid_true⟩
                      have hlookup_mid_res1 : res1.memEnv'.lookup l = some qt_mid := by
                        exact
                          typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
                            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                            hpe1 htc1 l qt_mid (by simpa [ctxTrue] using hlookup_mid_true)
                      have hclean_mid_res1 : qtypCleanUnder res1.regime' qt_mid := by
                        exact
                          qtypCleanUnder_transport_pure_regime_of_toPExpr
                            ctxᵢ e1 pe1 fuel' res1 hpe1 htc1 qt_mid
                            (by simpa [ctxTrue] using hclean_mid_true)
                      have hpres_mid :
                          PreservesInheritedCleanLocOneRun μ cfg1.memory θ θ1 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxPure) (res := res1)
                          (μ_in := μ) (μ_out := cfg1.memory) (θ_in := θ) (θ_out := θ1)
                          hpres1
                          (by simpa [ctxPure] using hlookup_in)
                          hlookup_mid_res1
                          hclean_mid_res1
                      have hpres_last :
                          PreservesInheritedCleanLocOneRun cfg1.memory cf.memory θ1 θ2 l :=
                        PreservesInheritedFinalCleanLocsOneRun.apply
                          (ctx := ctxTrue) (res := res2)
                          (μ_in := cfg1.memory) (μ_out := cf.memory) (θ_in := θ1) (θ_out := θ2)
                          hpres2
                          hlookup_mid_true
                          (by simpa [hmemEnv] using hlookup_out)
                          (by simpa [hregime'] using hclean_out)
                      exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_last
                    refine ⟨θ2, hθext, ?_, ?_, ?_, ?_, hpres_final⟩
                    · simpa [hetyp] using hv2
                    · simpa [hctxAfter] using hric2
                    · simpa [hctxAfter] using hcwr2
                    · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                      · simp [qtypGuardTag, hpredNo]
                      ·
                        have hcap2 :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxTrue res2).regime
                              res2.qualType cf.memory θ2 o :=
                          valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                        have hcap2' :
                            closureCapturedVarsRegimeMasked masked predSat
                              (ctxAfter ctxᵢ res).regime
                              res2.qualType cf.memory θ2 o := by
                          simpa [hctxAfter] using hcap2
                        exact
                          closureCapturedVarsRegimeMasked_transport_etyp
                            (qt := res2.qualType) (qt' := res.qualType)
                            hetyp.symm hcap2'
                  · rcases hrest with h2 | hrest
                    · rcases h2 with
                        ⟨k, deps, hmatch, hregime_false, res1, htc1, hbool, res3, htc3,
                          hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', _hpoison, hetyp⟩
                      intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
                      let ctxPure : TypeContext := { ctxᵢ with pureCtx := true }
                      let ctxFalse : TypeContext := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩ }
                      have htc1' : typecheck .ioFree ctxPure e1 fuel' = .ok res1 := by
                        simpa [ctxPure, typecheck, Nat.succ_sub_one] using htc1
                      have hwfTm_pure : wfTagMeaningCtx tm ctxPure := by
                        simpa [ctxPure, wfTagMeaningCtx] using hwfTm
                      have hwf_pure : wfTypeContext ctxPure := by
                        simpa [ctxPure, wfTypeContext] using hwf
                      have htagR_pure : regimeConsistentWithCtxMasked masked ctxPure := by
                        simpa [ctxPure, regimeConsistentWithCtxMasked] using htagR
                      have hmasked_none_pure :
                          ∀ t, masked t → ctxPure.regime.lookup? t = none := by
                        simpa [ctxPure] using hmasked_none
                      have hcwr_pure :
                          consistentWithRegimeMasked masked predSat ctxPure.regime ctxPure μ ρ θ := by
                        simpa [ctxPure, consistentWithRegimeMasked] using hcwr
                      have hpc_pure : ctxPure.pc = true := by
                        simpa [ctxPure] using hpc
                      have hIH_e1 := IH' fuel' (by omega) masked e1 ctxPure res1 htc1'
                      have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
                      rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                      rcases
                          hIH_e1 hpredlaws hwfTm_pure μ ρ θ cfg1 (Value.bool b)
                            hθwf hwf_pure hric htagR_pure hmasked_none_pure hcwr_pure
                            a pm hwfcfg ht_e1 hpc_pure
                        with ⟨θ1, hθext1, _hv1, hric1, hcwr1, _hvalc1, hpres1⟩
                      have hcwr_unmasked :
                          consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ :=
                        consistentWithRegimeMasked_unmask
                          (masked := masked) (predSat := predSat)
                          (R := ctxᵢ.regime) (ctx := ctxᵢ)
                          (μ := μ) (ρ := ρ) (θ := θ)
                          hmasked_none hcwr
                      have hb_false : b = false := by
                        exact
                          matchGuard_runtime_branch_alignment
                            predSat tm .ioFree
                            ctxᵢ μ ρ θ a pm
                            hwfTm hpredlaws hric hcwr_unmasked
                            e1 k deps false b cfg1
                            hmatch hregime_false ht_e1
                      have ht_e3 : terminatesTo .ioFree e3 cfg1 cf o := by
                        cases hbranch with
                        | inl h =>
                            have : true = false := by rw [← h.1, hb_false]
                            contradiction
                        | inr h => exact h.2
                      have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                      have hwfcfg1 : wfConfig cfg1 :=
                        (wfConfig_preserved .ioFree e1 _ cfg1 (Value.bool b) ht_e1 hwfcfg).1
                      have htc3' : typecheck .ioFree ctxFalse e3 fuel' = .ok res3 := by
                        simpa [ctxFalse, typecheck, Nat.succ_sub_one] using htc3
                      have hwfTm_false : wfTagMeaningCtx tm ctxFalse := by
                        simpa [ctxFalse, wfTagMeaningCtx] using hwfTm
                      have hwf_false : wfTypeContext ctxFalse := by
                        simpa [ctxFalse, wfTypeContext] using hwf
                      have htagR_false : regimeConsistentWithCtxMasked masked ctxFalse := by
                        exact
                          tagEnvConsistentWithRegimeMasked_insert_false
                            masked ctxᵢ.tagEnv ctxᵢ.regime k deps htagR
                      have hmasked_none_false :
                          ∀ t, masked t → ctxFalse.regime.lookup? t = none := by
                        simpa [ctxFalse] using hmasked_none
                      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
                      have hric1' : runtimeInstantiatesCtx ctxFalse cfg1.memory cfg1.varEnv θ1 := by
                        have hsub : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
                          exact
                            typecheckExpr_pure_mem_subset_of_toPExpr
                              (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                              hpe1 htc1
                        have hric_true :
                            runtimeInstantiatesCtx
                              { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
                              cfg1.memory cfg1.varEnv θ1 := by
                          exact
                            runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
                              (ctx := ctxᵢ) (res := res1) (μ := cfg1.memory) (ρ := cfg1.varEnv) (θ := θ1)
                              (k := k) (deps := deps)
                              hsub hric1
                        simpa [ctxFalse, runtimeInstantiatesCtx] using hric_true
                      have hcwr1' :
                          consistentWithRegimeMasked masked predSat ctxFalse.regime ctxFalse
                            cfg1.memory cfg1.varEnv θ1 := by
                        have hcwr_true :
                            consistentWithRegimeMasked masked predSat
                              ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
                              ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
                              cfg1.memory cfg1.varEnv θ1 := by
                          refine
                            consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
                              masked predSat ctxᵢ res1
                              cfg1.memory cfg1.varEnv θ1
                              k deps
                              ?_ ?_ hcwr1
                          · intro k' b' hk
                            exact
                              typecheckExpr_pure_regime_bridge_of_toPExpr
                                (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                                hpe1 htc1 k' b' hk
                          · intro l qt k' hlookup hguard hRdef
                            exact
                              typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
                                (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                                hpe1 htc1 l qt k' hlookup hguard hRdef
                        simpa [ctxFalse, consistentWithRegimeMasked] using hcwr_true
                      have hpc_false : ctxFalse.pc = true := by
                        simpa [ctxFalse] using hpc
                      have hpredNo : res.qualType.pred = Predicate.noPred := by
                        exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                      have hIH_e3 := IH' fuel' (by omega) masked e3 ctxFalse res3 htc3'
                      rcases
                          hIH_e3 hpredlaws hwfTm_false
                            cfg1.memory cfg1.varEnv θ1 cf o
                            hθ1wf hwf_false hric1' htagR_false hmasked_none_false hcwr1'
                            cfg1.nextAddr cfg1.pureMode hwfcfg1
                            ht_e3 hpc_false
                        with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2⟩
                      have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                      have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxFalse res3 := by
                        simp [ctxAfter, ctxFalse, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
                      have hpres_final :
                          PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ2 := by
                        refine ⟨?_⟩
                        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                        rcases
                            typecheckExpr_clean_lookup_origin_of_pc_true
                              ctxFalse e3 fuel' res3 htc3 hpc_false
                              l qt_out (by simpa [hmemEnv] using hlookup_out)
                              (by simpa [hregime'] using hclean_out)
                          with ⟨qt_mid, hlookup_mid_false, hclean_mid_false⟩
                        have hlookup_mid_res1 : res1.memEnv'.lookup l = some qt_mid := by
                          exact
                            typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
                              (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
                              hpe1 htc1 l qt_mid (by simpa [ctxFalse] using hlookup_mid_false)
                        have hclean_mid_res1 : qtypCleanUnder res1.regime' qt_mid := by
                          exact
                            qtypCleanUnder_transport_pure_regime_of_toPExpr
                              ctxᵢ e1 pe1 fuel' res1 hpe1 htc1 qt_mid
                              (by simpa [ctxFalse] using hclean_mid_false)
                        have hpres_mid :
                            PreservesInheritedCleanLocOneRun μ cfg1.memory θ θ1 l :=
                          PreservesInheritedFinalCleanLocsOneRun.apply
                            (ctx := ctxPure) (res := res1)
                            (μ_in := μ) (μ_out := cfg1.memory) (θ_in := θ) (θ_out := θ1)
                            hpres1
                            (by simpa [ctxPure] using hlookup_in)
                            hlookup_mid_res1
                            hclean_mid_res1
                        have hpres_last :
                            PreservesInheritedCleanLocOneRun cfg1.memory cf.memory θ1 θ2 l :=
                          PreservesInheritedFinalCleanLocsOneRun.apply
                            (ctx := ctxFalse) (res := res3)
                            (μ_in := cfg1.memory) (μ_out := cf.memory) (θ_in := θ1) (θ_out := θ2)
                            hpres2
                            hlookup_mid_false
                            (by simpa [hmemEnv] using hlookup_out)
                            (by simpa [hregime'] using hclean_out)
                        exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_last
                      refine ⟨θ2, hθext, ?_, ?_, ?_, ?_, hpres_final⟩
                      · simpa [hetyp] using hv2
                      · simpa [hctxAfter] using hric2
                      · simpa [hctxAfter] using hcwr2
                      · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                        · simp [qtypGuardTag, hpredNo]
                        ·
                          have hcap2 :
                              closureCapturedVarsRegimeMasked masked predSat
                                (ctxAfter ctxFalse res3).regime
                                res3.qualType cf.memory θ2 o :=
                            valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                          have hcap2' :
                              closureCapturedVarsRegimeMasked masked predSat
                                (ctxAfter ctxᵢ res).regime
                                res3.qualType cf.memory θ2 o := by
                            simpa [hctxAfter] using hcap2
                          exact
                            closureCapturedVarsRegimeMasked_transport_etyp
                              (qt := res3.qualType) (qt' := res.qualType)
                              hetyp.symm hcap2'
                    · rcases hrest with h3 | h4
                      · obtain ⟨k, deps, hmatch, hregime_none, res1, htc1, hbool, res2, htc2, res3, htc3,
                          hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp, hpred⟩ := h3
                        exact
                          stepFRSingleRun_ite_mode3_maskedReg
                            masked ctxᵢ predSat tm e1 e2 e3 fuel' res IH'
                            k deps (by simpa [Nat.succ_sub_one] using hmatch) hregime_none
                            res1 (by simpa [Nat.succ_sub_one] using htc1) hbool
                            res2 (by simpa [Nat.succ_sub_one] using htc2)
                            res3 (by simpa [Nat.succ_sub_one] using htc3)
                            hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison hetyp hpred
                      · rcases h4 with
                          ⟨⟨err, hmatch_fail⟩, res1, htc1, hbool, res2, htc2, res3, htc3,
                            hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp, _hpred⟩
                        intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
                        let ctx' : TypeContext := ctxAfter ctxᵢ res1
                        let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
                        let ctx'' : TypeContext := { ctx' with pc := pc' }
                        let ctxForE3 : TypeContext := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                        have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
                          simpa [typecheck, Nat.succ_sub_one] using htc1
                        have hIH_e1 := IH' fuel' (by omega) masked e1 ctxᵢ res1 htc1'
                        have hstruct_rt := terminatesTo_ite_inv' e1 e2 e3
                          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
                        rcases hstruct_rt with ⟨cfg1, b, ht_e1, hbranch, _hpm1, _hpmf⟩
                        rcases
                            hIH_e1 hpredlaws hwfTm μ ρ θ cfg1 (Value.bool b)
                              hθwf hwf hric htagR hmasked_none hcwr
                              a pm hwfcfg ht_e1 hpc
                          with ⟨θ1, hθext1, hv1, hric1, hcwr1, hvalc1, hpres1⟩
                        have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
                        have hwfcfg1 : wfConfig cfg1 :=
                          (wfConfig_preserved .ioFree e1 _ cfg1 (Value.bool b) ht_e1 hwfcfg).1
                        have hmono1 :
                            Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime :=
                          regime_monotone ctxᵢ e1 fuel' res1 htc1'
                        have htagR1 :
                            regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ res1) :=
                          typecheckExpr_preserves_regimeConsistentWithCtxMasked
                            masked ctxᵢ e1 fuel' res1 htagR htc1'
                        have hmasked_none1 :
                            ∀ t, masked t → (ctxAfter ctxᵢ res1).regime.lookup? t = none :=
                          masked_lookup_none_of_monotoneStep hmasked_none hmono1
                        have hwfTm1 : wfTagMeaningCtx tm (ctxAfter ctxᵢ res1) := by
                          exact
                            typecheckExpr_preserves_wfTagMeaningCtx
                              tm ctxᵢ e1 fuel' res1 hwfTm htc1'
                        have hwf1 : wfTypeResult res1 :=
                          typecheckExpr_preserves_wfTypeResult ctxᵢ e1 fuel' res1 hwf htc1'
                        have hwf_ctx' : wfTypeContext ctx' := by
                          simpa [ctx'] using wfTypeContext_of_wfTypeResult ctxᵢ res1 hwf1
                        have hwfTm_ctx'' : wfTagMeaningCtx tm ctx'' := by
                          simpa [ctx'', ctx', pc'] using hwfTm1
                        have hwf_ctx'' : wfTypeContext ctx'' := by
                          simpa [ctx'', ctx', pc', wfTypeContext] using hwf_ctx'
                        have hric1_ctx'' :
                            runtimeInstantiatesCtx ctx'' cfg1.memory cfg1.varEnv θ1 := by
                          simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric1
                        have hcwr1_ctx'' :
                            consistentWithRegimeMasked masked predSat ctx''.regime ctx''
                              cfg1.memory cfg1.varEnv θ1 := by
                          simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr1
                        have htagR_ctx'' : regimeConsistentWithCtxMasked masked ctx'' := by
                          simpa [ctx'', ctx', pc', regimeConsistentWithCtxMasked] using htagR1
                        have hmasked_none_ctx'' :
                            ∀ t, masked t → ctx''.regime.lookup? t = none := by
                          simpa [ctx'', ctx', pc', ctxAfter] using hmasked_none1
                        have hpc'' : ctx''.pc = true := by
                          simp [ctx'', pc', hpc, joinPoison]
                        have hnextLoc_mono :
                            res1.nextLoc' ≤ res2.nextLoc' := by
                          have : ctx''.nextLoc ≤ res2.nextLoc' :=
                            typecheck_nextLoc_mono ctx'' e2 fuel' res2
                              (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                          simpa [ctx'', ctx'] using this
                        have hnextTag_mono :
                            res1.nextTag' ≤ res2.nextTag' := by
                          have : ctx''.nextTag ≤ res2.nextTag' :=
                            typecheck_nextTag_mono .ioFree ctx'' e2 fuel' res2
                              (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                          simpa [ctx'', ctx'] using this
                        have hwfTm_ctxForE3 : wfTagMeaningCtx tm ctxForE3 := by
                          simpa [ctxForE3, ctx'', ctx', pc'] using hwfTm1
                        have hwf_ctxForE3 : wfTypeContext ctxForE3 := by
                          intro l hl
                          simp only [ctxForE3, ctx'', ctx', ctxAfter] at hl ⊢
                          exact Nat.lt_of_lt_of_le (hwf_ctx' l hl) hnextLoc_mono
                        have hric1_ctxForE3 :
                            runtimeInstantiatesCtx ctxForE3 cfg1.memory cfg1.varEnv θ1 := by
                          simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric1
                        have hcwr1_ctxForE3 :
                            consistentWithRegimeMasked masked predSat ctxForE3.regime ctxForE3
                              cfg1.memory cfg1.varEnv θ1 := by
                          simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr1
                        have htagR_ctxForE3 : regimeConsistentWithCtxMasked masked ctxForE3 := by
                          show tagEnvConsistentWithRegimeMasked masked ctxForE3.tagEnv ctxForE3.regime
                          simpa [ctxForE3, ctx'', ctx', pc', regimeConsistentWithCtxMasked] using htagR1
                        have hmasked_none_ctxForE3 :
                            ∀ t, masked t → ctxForE3.regime.lookup? t = none := by
                          simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hmasked_none1
                        have hpcForE3 : ctxForE3.pc = true := by
                          simp [ctxForE3, ctx'', pc', hpc, joinPoison]
                        have htc2' : typecheck .ioFree ctx'' e2 fuel' = .ok res2 := by
                          simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2
                        have htc3' : typecheck .ioFree ctxForE3 e3 fuel' = .ok res3 := by
                          simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3
                        have hpredNo : res.qualType.pred = Predicate.noPred := by
                          exact typecheckIf_pred_noPred ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
                        have hcompat23 : beqETypSignature res2.qualType.etyp res3.qualType.etyp = true := by
                          by_contra hcompat
                          have hcompat' : beqETypSignature res2.qualType.etyp res3.qualType.etyp = false := by
                            cases h : beqETypSignature res2.qualType.etyp res3.qualType.etyp <;> simp_all
                          have hmatch_fail' :
                              matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .error err := by
                            simpa [Nat.succ_sub_one] using hmatch_fail
                          have htc1_expr :
                              typecheckExpr .ioFree ctxᵢ e1 fuel' = .ok res1 := by
                            simpa [Nat.succ_sub_one] using htc1
                          have htc2_expr :
                              typecheckExpr .ioFree ctx'' e2 fuel' = .ok res2 := by
                            simpa [ctx'', ctx', pc', Nat.succ_sub_one] using htc2
                          have htc3_expr :
                              typecheckExpr .ioFree ctxForE3 e3 fuel' = .ok res3 := by
                            simpa [ctxForE3, ctx'', ctx', pc', Nat.succ_sub_one] using htc3
                          have htcIf_err :
                              typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') =
                                .error s!"Branches of if must have same type" := by
                            cases hq1 : res1.qualType with
                            | mk etyp1 p1 pred1 =>
                                have hbool1 : etyp1 = ETyp.bool := by
                                  simpa [hq1] using hbool
                                subst etyp1
                                have htc2_raw :
                                    typecheckExpr .ioFree
                                      { pc := joinPoison ctxᵢ.pc p1
                                      , regime := res1.regime'
                                      , memEnv := res1.memEnv'
                                      , varEnv := ctxᵢ.varEnv
                                      , tagEnv := res1.tagEnv'
                                      , nextLoc := res1.nextLoc'
                                      , nextTag := res1.nextTag'
                                      , pureCtx := ctxᵢ.pureCtx } e2 fuel' = .ok res2 := by
                                  simpa [ctx'', ctx', pc', hq1] using htc2_expr
                                have htc3_raw :
                                    typecheckExpr .ioFree
                                      { pc := joinPoison ctxᵢ.pc p1
                                      , regime := res1.regime'
                                      , memEnv := res1.memEnv'
                                      , varEnv := ctxᵢ.varEnv
                                      , tagEnv := res1.tagEnv'
                                      , nextLoc := res2.nextLoc'
                                      , nextTag := res2.nextTag'
                                      , pureCtx := ctxᵢ.pureCtx } e3 fuel' = .ok res3 := by
                                  simpa [ctxForE3, ctx'', ctx', pc', hq1] using htc3_expr
                                unfold typecheckIf
                                rw [hmatch_fail', htc1_expr]
                                simp only [bind, Except.bind]
                                simp [hq1]
                                rw [htc2_raw]
                                simp
                                rw [htc3_raw]
                                cases hq2 : res2.qualType with
                                | mk etyp2 p2 pred2 =>
                                    cases hq3 : res3.qualType with
                                    | mk etyp3 p3 pred3 =>
                                        have hcompat'' : beqETypSignature etyp2 etyp3 = false := by
                                          simpa [hq2, hq3] using hcompat'
                                        simp [Except.pure, hq3, hcompat'', pure]
                          rw [htcIf_err] at htcIf
                          cases htcIf
                        have hclean_back_mid :
                            ∀ l qt_in qt_out,
                              ctxᵢ.memEnv.lookup l = some qt_in →
                              res.memEnv'.lookup l = some qt_out →
                              qtypCleanUnder res.regime' qt_out →
                              ∃ qt_mid,
                                res1.memEnv'.lookup l = some qt_mid ∧
                                qtypCleanUnder res1.regime' qt_mid := by
                          intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
                          have hlookup_join :
                              (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                            simpa [hmemEnv] using hlookup_out
                          cases hclean_out with
                          | clean hpoison_out =>
                              have hcontains_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                                memEnv_contains_of_lookup_some
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
                              rcases
                                  joinMemEnvsStrong_contains_implies_or
                                    res2.memEnv' res3.memEnv' l hcontains_join
                                with hcontains2 | hcontains3
                              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                  ⟨qt2, hlookup2⟩
                                have henv2 : res2.memEnv'.lookup l ≠ none := by
                                  intro hnone
                                  rw [hlookup2] at hnone
                                  contradiction
                                rcases
                                    joinMemEnvsStrong_lookup_clean_left
                                      res2.memEnv' res3.memEnv' l qt_out
                                      hlookup_join hpoison_out henv2
                                  with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctx'' e2 fuel' res2 htc2' hpc''
                                    l qt2' hlookup2' (qtypCleanUnder.clean hpoison2)
                              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                  ⟨qt3, hlookup3⟩
                                have henv3 : res3.memEnv'.lookup l ≠ none := by
                                  intro hnone
                                  rw [hlookup3] at hnone
                                  contradiction
                                rcases
                                    joinMemEnvsStrong_lookup_clean_right
                                      res2.memEnv' res3.memEnv' l qt_out
                                      hlookup_join hpoison_out henv3
                                  with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctxForE3 e3 fuel' res3 htc3' hpcForE3
                                    l qt3' hlookup3' (qtypCleanUnder.clean hpoison3)
                          | guard k htag hk hnotfun =>
                              have hk_join :
                                  (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                simpa [hregime'] using hk
                              have hcontains_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                                memEnv_contains_of_lookup_some
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
                              rcases
                                  joinMemEnvsStrong_contains_implies_or
                                    res2.memEnv' res3.memEnv' l hcontains_join
                                with hcontains2 | hcontains3
                              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                  ⟨qt2, hlookup2⟩
                                have htag2 : qtypGuardTag qt2 = some k :=
                                  joinMemEnvsStrong_lookup_guardTag_left
                                    res2.memEnv' res3.memEnv' l qt_out qt2 k
                                    hlookup_join hlookup2 htag
                                have hk2 : res2.regime'.lookup? k = some true :=
                                  joinRegimes_lookup_some_left
                                    res2.regime' res3.regime' k true hk_join
                                have hnotfun2 : qt2.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                                  native_decide
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctx'' e2 fuel' res2 htc2' hpc''
                                    l qt2 hlookup2
                                    (qtypCleanUnder.guard k htag2 hk2 hnotfun2)
                              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                  ⟨qt3, hlookup3⟩
                                have htag3 : qtypGuardTag qt3 = some k :=
                                  joinMemEnvsStrong_lookup_guardTag_right
                                    res2.memEnv' res3.memEnv' l qt_out qt3 k
                                    hlookup_join hlookup3 htag
                                have hk3 : res3.regime'.lookup? k = some true :=
                                  joinRegimes_lookup_some_right
                                    res2.regime' res3.regime' k true hk_join
                                have hnotfun3 : qt3.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                                  native_decide
                                exact
                                  typecheckExpr_clean_lookup_origin_of_pc_true
                                    ctxForE3 e3 fuel' res3 htc3' hpcForE3
                                    l qt3 hlookup3
                                    (qtypCleanUnder.guard k htag3 hk3 hnotfun3)
                        cases hbranch with
                        | inl hbranch_true =>
                            have ht_e2 : terminatesTo .ioFree e2 cfg1 cf o := hbranch_true.2
                            have hIH_e2 := IH' fuel' (by omega) masked e2 ctx'' res2 htc2'
                            rcases
                                hIH_e2 hpredlaws hwfTm_ctx'' cfg1.memory cfg1.varEnv θ1 cf o
                                  hθ1wf hwf_ctx'' hric1_ctx'' htagR_ctx'' hmasked_none_ctx'' hcwr1_ctx''
                                  cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc''
                              with ⟨θ2, hθext2, hv2, hric2, hcwr2, hvalc2, hpres2⟩
                            have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
                            have hcwr2_left :
                                consistentWithRegimeMasked masked predSat
                                  (ctxAfter ctxᵢ res2).regime
                                  (ctxAfter ctxᵢ res2)
                                  cf.memory cf.varEnv θ2 := by
                              simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr2
                            have hcwr_final :
                                consistentWithRegimeMasked masked predSat
                                  (ctxAfter ctxᵢ res).regime
                                  (ctxAfter ctxᵢ res)
                                  cf.memory cf.varEnv θ2 := by
                              exact
                                consistentWithRegimeMasked_join_from_left
                                  masked predSat ctxᵢ
                                  res2 res3 res
                                  cf.memory cf.varEnv θ2
                                  hmemEnv hregime' hcwr2_left
                            have hric_final :
                                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ2 := by
                              unfold runtimeInstantiatesCtx at hric2 ⊢
                              constructor
                              · intro l a hθlookup
                                rcases hric2.1 l a hθlookup with ⟨hcontains2, hmem⟩
                                rcases
                                    memEnv_lookup_some_of_contains
                                      (ctxAfter ctx'' res2).memEnv l hcontains2
                                  with ⟨qt2, hlookup2ctx⟩
                                have hlookup2 : res2.memEnv'.lookup l = some qt2 := by
                                  simpa [ctxAfter] using hlookup2ctx
                                rcases
                                    joinMemEnvsStrong_lookup_some_of_left_lookup
                                      res2.memEnv' res3.memEnv' l qt2 hlookup2
                                  with ⟨qt, hlookup_join⟩
                                have hcontains_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
                                  exact
                                    memEnv_contains_of_lookup_some
                                      (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                                exact ⟨by simpa [ctxAfter, hmemEnv] using hcontains_join, hmem⟩
                              · intro x qt hlookup
                                have hlookup' :
                                    (ctxAfter ctx'' res2).varEnv.lookup x = some qt := by
                                  simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                                exact hric2.2 hlookup'
                            have hpres_branch_final :
                                PreservesInheritedFinalCleanLocsOneRun
                                  (ctxAfter ctxᵢ res1) res
                                  cfg1.memory cf.memory θ1 θ2 := by
                              refine ⟨?_⟩
                              intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                              have hlookup_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                                simpa [hmemEnv] using hlookup_out
                              have hcontains_in :
                                  (ctxAfter ctxᵢ res1).memEnv.contains l := by
                                exact
                                  memEnv_contains_of_lookup_some
                                    (ctxAfter ctxᵢ res1).memEnv l qt_in
                                    (by simpa [ctxAfter] using hlookup_in)
                              have hcontains2 : res2.memEnv'.contains l :=
                                typecheckExpr_mem_contains_preserved
                                  ctx'' e2 fuel' res2
                                  (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                                  l
                                  (by simpa [ctx'', ctx', pc', ctxAfter] using hcontains_in)
                              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                                ⟨qt2, hlookup2⟩
                              have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                                cases hclean_out with
                                | clean hpoison_out =>
                                    have henv2 : res2.memEnv'.lookup l ≠ none := by
                                      intro hnone
                                      rw [hlookup2] at hnone
                                      contradiction
                                    rcases
                                        joinMemEnvsStrong_lookup_clean_left
                                          res2.memEnv' res3.memEnv' l qt_out
                                          hlookup_join hpoison_out henv2
                                      with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                                    have hqt2 : qt2 = qt2' := by
                                      rw [hlookup2] at hlookup2'
                                      injection hlookup2'
                                    cases hqt2
                                    exact qtypCleanUnder.clean hpoison2
                                | guard k htag hk hnotfun =>
                                    have hk_join :
                                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                      simpa [hregime'] using hk
                                    have htag2 : qtypGuardTag qt2 = some k :=
                                      joinMemEnvsStrong_lookup_guardTag_left
                                        res2.memEnv' res3.memEnv' l qt_out qt2 k
                                        hlookup_join hlookup2 htag
                                    have hk2 : res2.regime'.lookup? k = some true :=
                                      joinRegimes_lookup_some_left
                                        res2.regime' res3.regime' k true hk_join
                                    have hnotfun2 : qt2.etyp.isFunctionType = false := by
                                      rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                                      native_decide
                                    exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
                              exact
                                PreservesInheritedFinalCleanLocsOneRun.apply
                                  (ctx := ctx'') (res := res2)
                                  (μ_in := cfg1.memory) (μ_out := cf.memory)
                                  (θ_in := θ1) (θ_out := θ2)
                                  hpres2
                                  (by simpa [ctx'', ctx', pc', ctxAfter] using hlookup_in)
                                  hlookup2
                                  hclean2
                            have hpres_final :
                                PreservesInheritedFinalCleanLocsOneRun
                                  ctxᵢ res μ cf.memory θ θ2 := by
                              exact
                                PreservesInheritedFinalCleanLocsOneRun.compose
                                  (ctx := ctxᵢ) (res1 := res1) (res2 := res)
                                  hclean_back_mid hpres1
                                  (by simpa [ctx'] using hpres_branch_final)
                            refine ⟨θ2, hθext, ?_, hric_final, hcwr_final, ?_, hpres_final⟩
                            · simpa [hetyp] using valueHasETyp_joinETyps_left hv2
                            · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                              · simp [qtypGuardTag, hpredNo]
                              ·
                                have hcap2 :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctx'' res2).regime
                                      res2.qualType cf.memory θ2 o :=
                                  valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc2
                                have hlookup_back :
                                    ∀ k b,
                                      (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                                        (ctxAfter ctx'' res2).regime.lookup? k = some b := by
                                  intro k b hk
                                  have hk' :
                                      (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
                                    simpa [ctxAfter, hregime'] using hk
                                  simpa [ctxAfter] using
                                    joinRegimes_lookup_some_left
                                      res2.regime' res3.regime' k b hk'
                                have hcap2' :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctxᵢ res).regime
                                      res2.qualType cf.memory θ2 o := by
                                  exact
                                    closureCapturedVarsRegimeMasked_transport_lookup_back
                                      (masked := masked) (predSat := predSat)
                                      (R := (ctxAfter ctx'' res2).regime)
                                      (R' := (ctxAfter ctxᵢ res).regime)
                                      (qt := res2.qualType) (μ := cf.memory) (θ := θ2) (v := o)
                                      hlookup_back hcap2
                                have hcap2_join :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctxᵢ res).regime
                                      ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison,
                                        joinPoison res2.qualType.poison res3.qualType.poison,
                                        joinPredicates res2.qualType.pred res3.qualType.pred⟩
                                      cf.memory θ2 o :=
                                  by
                                    have hcap2'' :
                                        closureCapturedVarsRegimeMasked masked predSat
                                          (ctxAfter ctxᵢ res).regime
                                          ⟨res2.qualType.etyp, res2.qualType.poison, res2.qualType.pred⟩
                                          cf.memory θ2 o := by
                                      cases hq2 : res2.qualType with
                                      | mk etyp2 poison2 pred2 =>
                                          simpa [hq2] using hcap2'
                                    simpa using
                                      (closureCapturedVarsRegimeMasked_joinETyps_step
                                        masked predSat (ctxAfter ctxᵢ res).regime
                                        cf.memory θ2 o
                                        res2.qualType.etyp res3.qualType.etyp
                                        res2.qualType.poison res3.qualType.poison
                                        res2.qualType.pred res3.qualType.pred
                                        hcompat23
                                        hcap2'')
                                exact
                                  closureCapturedVarsRegimeMasked_transport_etyp
                                    (qt := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                        res2.qualType.poison res3.qualType.poison,
                                      joinPoison res2.qualType.poison res3.qualType.poison,
                                      joinPredicates res2.qualType.pred res3.qualType.pred⟩)
                                    (qt' := res.qualType)
                                    (by simp [hetyp]) hcap2_join
                        | inr hbranch_false =>
                            have ht_e3 : terminatesTo .ioFree e3 cfg1 cf o := hbranch_false.2
                            have hIH_e3 := IH' fuel' (by omega) masked e3 ctxForE3 res3 htc3'
                            rcases
                                hIH_e3 hpredlaws hwfTm_ctxForE3
                                  cfg1.memory cfg1.varEnv θ1 cf o
                                  hθ1wf hwf_ctxForE3 hric1_ctxForE3
                                  htagR_ctxForE3 hmasked_none_ctxForE3 hcwr1_ctxForE3
                                  cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e3 hpcForE3
                              with ⟨θ3, hθext3, hv3, hric3, hcwr3, hvalc3, hpres3⟩
                            have hθext : wfExtendsMap θ θ3 := wfExtendsMap_trans hθext1 hθext3
                            have hcwr3_right :
                                consistentWithRegimeMasked masked predSat
                                  (ctxAfter ctxᵢ res3).regime
                                  (ctxAfter ctxᵢ res3)
                                  cf.memory cf.varEnv θ3 := by
                              simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegimeMasked] using hcwr3
                            have hcwr_final :
                                consistentWithRegimeMasked masked predSat
                                  (ctxAfter ctxᵢ res).regime
                                  (ctxAfter ctxᵢ res)
                                  cf.memory cf.varEnv θ3 := by
                              exact
                                consistentWithRegimeMasked_join_from_right
                                  masked predSat ctxᵢ
                                  res2 res3 res
                                  cf.memory cf.varEnv θ3
                                  hmemEnv hregime' hcwr3_right
                            have hric_final :
                                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ3 := by
                              unfold runtimeInstantiatesCtx at hric3 ⊢
                              constructor
                              · intro l a hθlookup
                                rcases hric3.1 l a hθlookup with ⟨hcontains3, hmem⟩
                                rcases
                                    memEnv_lookup_some_of_contains
                                      (ctxAfter ctxForE3 res3).memEnv l hcontains3
                                  with ⟨qt3, hlookup3ctx⟩
                                have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                                  simpa [ctxAfter] using hlookup3ctx
                                rcases
                                    joinMemEnvsStrong_lookup_some_of_right_lookup
                                      res2.memEnv' res3.memEnv' l qt3 hlookup3
                                  with ⟨qt, hlookup_join⟩
                                have hcontains_join :
                                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
                                  exact
                                    memEnv_contains_of_lookup_some
                                      (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                                exact ⟨by simpa [ctxAfter, hmemEnv] using hcontains_join, hmem⟩
                              · intro x qt hlookup
                                have hlookup' :
                                    (ctxAfter ctxForE3 res3).varEnv.lookup x = some qt := by
                                  simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hlookup
                                exact hric3.2 hlookup'
                            have hpres_branch_final :
                                PreservesInheritedFinalCleanLocsOneRun
                                  (ctxAfter ctxᵢ res1) res
                                  cfg1.memory cf.memory θ1 θ3 := by
                              refine ⟨?_⟩
                              intro l qt_in qt_out hlookup_in hlookup_out hclean_out
                              have hlookup_join :
                                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
                                simpa [hmemEnv] using hlookup_out
                              have hcontains_in :
                                  (ctxAfter ctxᵢ res1).memEnv.contains l := by
                                exact
                                  memEnv_contains_of_lookup_some
                                    (ctxAfter ctxᵢ res1).memEnv l qt_in
                                    (by simpa [ctxAfter] using hlookup_in)
                              have hcontains3 : res3.memEnv'.contains l :=
                                typecheckExpr_mem_contains_preserved
                                  ctxForE3 e3 fuel' res3
                                  (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                                  l
                                  (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hcontains_in)
                              rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                                ⟨qt3, hlookup3⟩
                              have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                                cases hclean_out with
                                | clean hpoison_out =>
                                    have henv3 : res3.memEnv'.lookup l ≠ none := by
                                      intro hnone
                                      rw [hlookup3] at hnone
                                      contradiction
                                    rcases
                                        joinMemEnvsStrong_lookup_clean_right
                                          res2.memEnv' res3.memEnv' l qt_out
                                          hlookup_join hpoison_out henv3
                                      with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                                    have hqt3 : qt3 = qt3' := by
                                      rw [hlookup3] at hlookup3'
                                      injection hlookup3'
                                    cases hqt3
                                    exact qtypCleanUnder.clean hpoison3
                                | guard k htag hk hnotfun =>
                                    have hk_join :
                                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                                      simpa [hregime'] using hk
                                    have htag3 : qtypGuardTag qt3 = some k :=
                                      joinMemEnvsStrong_lookup_guardTag_right
                                        res2.memEnv' res3.memEnv' l qt_out qt3 k
                                        hlookup_join hlookup3 htag
                                    have hk3 : res3.regime'.lookup? k = some true :=
                                      joinRegimes_lookup_some_right
                                        res2.regime' res3.regime' k true hk_join
                                    have hnotfun3 : qt3.etyp.isFunctionType = false := by
                                      rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                                      native_decide
                                    exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
                              exact
                                PreservesInheritedFinalCleanLocsOneRun.apply
                                  (ctx := ctxForE3) (res := res3)
                                  (μ_in := cfg1.memory) (μ_out := cf.memory)
                                  (θ_in := θ1) (θ_out := θ3)
                                  hpres3
                                  (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hlookup_in)
                                  hlookup3
                                  hclean3
                            have hpres_final :
                                PreservesInheritedFinalCleanLocsOneRun
                                  ctxᵢ res μ cf.memory θ θ3 := by
                              exact
                                PreservesInheritedFinalCleanLocsOneRun.compose
                                  (ctx := ctxᵢ) (res1 := res1) (res2 := res)
                                  hclean_back_mid hpres1
                                  (by simpa [ctx'] using hpres_branch_final)
                            refine ⟨θ3, hθext, ?_, hric_final, hcwr_final, ?_, hpres_final⟩
                            · simpa [hetyp] using
                                valueHasETyp_joinETyps_right hcompat23 hv3
                            · refine valueConsistentWithRegimeMasked.noTag ?_ ?_
                              · simp [qtypGuardTag, hpredNo]
                              ·
                                have hcap3 :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctxForE3 res3).regime
                                      res3.qualType cf.memory θ3 o :=
                                  valueConsistentWithRegimeMasked_closureCapturedVarsRegime hvalc3
                                have hlookup_back :
                                    ∀ k b,
                                      (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                                        (ctxAfter ctxForE3 res3).regime.lookup? k = some b := by
                                  intro k b hk
                                  have hk' :
                                      (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
                                    simpa [ctxAfter, hregime'] using hk
                                  simpa [ctxAfter] using
                                    joinRegimes_lookup_some_right
                                      res2.regime' res3.regime' k b hk'
                                have hcap3' :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctxᵢ res).regime
                                      res3.qualType cf.memory θ3 o := by
                                  exact
                                    closureCapturedVarsRegimeMasked_transport_lookup_back
                                      (masked := masked) (predSat := predSat)
                                      (R := (ctxAfter ctxForE3 res3).regime)
                                      (R' := (ctxAfter ctxᵢ res).regime)
                                      (qt := res3.qualType) (μ := cf.memory) (θ := θ3) (v := o)
                                      hlookup_back hcap3
                                have hcap3_join :
                                    closureCapturedVarsRegimeMasked masked predSat
                                      (ctxAfter ctxᵢ res).regime
                                      ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                          res2.qualType.poison res3.qualType.poison,
                                        joinPoison res2.qualType.poison res3.qualType.poison,
                                        joinPredicates res2.qualType.pred res3.qualType.pred⟩
                                      cf.memory θ3 o :=
                                  by
                                    have hcap3'' :
                                        closureCapturedVarsRegimeMasked masked predSat
                                          (ctxAfter ctxᵢ res).regime
                                          ⟨res3.qualType.etyp, res3.qualType.poison, res3.qualType.pred⟩
                                          cf.memory θ3 o := by
                                      cases hq3 : res3.qualType with
                                      | mk etyp3 poison3 pred3 =>
                                          simpa [hq3] using hcap3'
                                    simpa using
                                      (closureCapturedVarsRegimeMasked_joinETyps_step_right
                                        masked predSat (ctxAfter ctxᵢ res).regime
                                        cf.memory θ3 o
                                        res2.qualType.etyp res3.qualType.etyp
                                        res2.qualType.poison res3.qualType.poison
                                        res2.qualType.pred res3.qualType.pred
                                        hcompat23
                                        hcap3'')
                                exact
                                  closureCapturedVarsRegimeMasked_transport_etyp
                                    (qt := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
                                        res2.qualType.poison res3.qualType.poison,
                                      joinPoison res2.qualType.poison res3.qualType.poison,
                                      joinPredicates res2.qualType.pred res3.qualType.pred⟩)
                                    (qt' := res.qualType)
                                    (by simp [hetyp]) hcap3_join
          | newRef e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckNewRef] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_newRef_maskedReg
                      masked ctxᵢ predSat tm e fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | assign e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckAssign] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_assign_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | deref e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckDeref] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_deref_maskedReg
                      masked ctxᵢ predSat tm e fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | seq e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_seq_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | vlet z e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_vlet_maskedReg
                      masked ctxᵢ predSat tm z e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | fn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_fn_maskedReg
                  masked .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | pfn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_pfn_maskedReg
                  masked .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | app e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckApp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_app_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
              unfold StepFRSingleRunFinalCleanPcTrueMaskedRegParam
              intro _hpredlaws _hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
              have : False := by
                obtain ⟨fuelT, verboseT, heq⟩ := ht
                have h_world := congrArg (fun f => f LeanProofs.defaultWorld) heq
                cases fuelT with
                | zero =>
                    simp [LeanPoison.beval, pure] at h_world
                    cases h_world
                | succ fuelT' =>
                    simp [LeanPoison.beval, pure] at h_world
                    cases h_world
              exact False.elim this

private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  ∀ fuel res,
    typecheck .ioFree ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrue .ioFree ctxᵢ e res predSat tm := by
  intro fuel res htc
  have hmasked :=
    TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree
      (masked := fun _ => False) e ctxᵢ predSat tm fuel res htc
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg hcwr a pm hwfcfg ht hpc
  have hreg_masked :
      regimeConsistentWithCtxMasked (fun _ => False) ctxᵢ := by
    intro k deps hlookup
    exact Or.inr (hreg k deps hlookup)
  have hcwr_masked :
      consistentWithRegimeMasked (fun _ => False) predSat ctxᵢ.regime ctxᵢ μ ρ θ := by
    rcases hcwr with ⟨hlocs, hvars, hclos⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l qt k hlookup hguard hRdef
      exact Or.inr (hlocs l qt k hlookup hguard hRdef)
    · intro x qt k hlookup hguard hRdef
      exact Or.inr (hvars x qt k hlookup hguard hRdef)
    · intro x qt v hlookup hlookup_v
      cases hclos x qt v hlookup hlookup_v with
      | intro hdeep =>
          exact
            deepValueQTypProperty_mono
              (fun σcap ρcap ⟨hP, hT⟩ =>
                ⟨(fun x qt_x k_x hlook hguard hkR =>
                    Or.inr (hP x qt_x k_x hlook hguard hkR)),
                  hT⟩)
              hdeep
  have hmasked_none_init :
      ∀ k, (fun _ => False) k → ctxᵢ.regime.lookup? k = none := by
    intro k hk
    cases hk
  rcases
      hmasked hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg_masked hmasked_none_init hcwr_masked a pm hwfcfg ht hpc
    with ⟨θ', hθext, hvaltyp, hric', hcwr_masked', hvalc_masked', hpres⟩
  have hmasked_none :
      ∀ k, (fun _ => False) k → (ctxAfter ctxᵢ res).regime.lookup? k = none := by
    intro k hk
    cases hk
  have hcwr' :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf.memory cf.varEnv θ' :=
    consistentWithRegimeMasked_unmask
      (masked := fun _ => False) (predSat := predSat)
      (R := (ctxAfter ctxᵢ res).regime) (ctx := ctxAfter ctxᵢ res)
      (μ := cf.memory) (ρ := cf.varEnv) (θ := θ')
      hmasked_none hcwr_masked'
  have hvalc' :
      valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
        res.qualType cf.memory θ' o :=
    valueConsistentWithRegimeMasked_unmask
      (masked := fun _ => False) (predSat := predSat)
      (R := (ctxAfter ctxᵢ res).regime) (qt := res.qualType)
      (μ := cf.memory) (θ := θ') (v := o)
      hmasked_none hvalc_masked'
  exact ⟨θ', hθext, hvaltyp, hric', hcwr', hvalc', hpres⟩


-- I/O-free step theorem: proves StepFR directly (no world-threading)
-- Restructured to avoid variable capture: induction is generalized over all expressions
theorem TypeSystemEnforcesFaultRobustness_step_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat tm := by
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
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm Expr.unit res Value.unit hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.unit) hpoison hnotfun hnotref hpredNo hctxAfter
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
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.num n) res (Value.num n) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.num n) hpoison hnotfun hnotref hpredNo hctxAfter
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
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.bool b) res (Value.bool b) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.bool b) hpoison hnotfun hnotref hpredNo hctxAfter
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
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.str s) res (Value.str s) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.str s) hpoison hnotfun hnotref hpredNo hctxAfter
        | var name =>
            exact stepFR_var .ioFree ctxᵢ predSat tm name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                exact stepFR_op ctxᵢ predSat e1 e2 op fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | unaryop uop e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                exact stepFR_unaryop ctxᵢ predSat e uop fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | ite e1 e2 e3 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckIf] at htc
            | succ fuel' =>
                have hsingleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')) := by
                  intro m _hm e ctx' hwfTm' res' htc'
                  exact TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree e ctx' predSat tm m res' htc'
                exact
                  stepFR_ite ctxᵢ predSat tm e1 e2 e3 fuel' res
                    (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH)
                    hsingleIH htc
        | newRef e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                exact stepFR_newRef ctxᵢ predSat e fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | assign e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckAssign] at htc
            | succ fuel' =>
                exact stepFR_assign ctxᵢ predSat tm e1 e2 fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | deref e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckDeref] at htc
            | succ fuel' =>
                exact stepFR_deref ctxᵢ predSat tm e fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                exact stepFR_seq ctxᵢ predSat e1 e2 fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                exact stepFR_vlet ctxᵢ predSat vname e1 e2 fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | fn name ty e1 ty2 =>
            exact stepFR_fn .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | pfn name ty e1 ty2 =>
            exact stepFR_pfn .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | app e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckApp] at htc
            | succ fuel' =>
                have hsingleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')) := by
                  intro m _hm e ctx' hwfTm' res' htc'
                  exact TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree e ctx' predSat tm m res' htc'
                exact
                  stepFR_app ctxᵢ predSat tm e1 e2 fuel' res
                    (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH)
                    hsingleIH htc
        | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            -- In `.ioFree` mode, I/O constructs cannot terminate, so StepFR is vacuous.
            intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
            have : False := by
              obtain ⟨fuelT, verboseT, heq⟩ := ht₀
              -- In `.ioFree` mode, evaluation yields `ioForbidden`, never `.success`.
              have h_world := congrArg (fun f => f LeanProofs.defaultWorld) heq
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

-- Bridges from step theorem to full specification
-- FaultRobustnessSpec specialized to ioFree mode (implied by FaultRobustnessSpec)
def FaultRobustnessSpec_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) (_tm : TagMeaning) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool),
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime ctx.regime s →
    wfRealizationMap θ₁ →  wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } →
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₁ ρ₁ θ₁ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₂ ρ₂ θ₂ →
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
lemma FaultRobustnessSpec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
    FaultRobustnessSpec e s obs ctx predSat tm → FaultRobustnessSpec_ioFree e s obs ctx predSat tm := by
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
      ∀ (predSat : PredSat) (tm : TagMeaning),
        wfTagMeaningCtx tm ctx →
        PredSatLaws predSat tm →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck .ioFree ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          FaultRobustnessSpec_ioFree e s obs ctx predSat tm)

-- TypeSystemEnforcesFaultRobustness_spec implies TypeSystemEnforcesFaultRobustness_spec_ioFree
lemma TypeSystemEnforcesFaultRobustness_spec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
    TypeSystemEnforcesFaultRobustness_spec e s obs → TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs := by
  intro h his hos ctx hctx hwf hpc hte predSat tm hwfTm hps htc
  exact FaultRobustnessSpec_implies_ioFree e s obs ctx predSat tm
    (h his hos ctx hctx hwf hpc hte predSat tm hwfTm hps htc)

theorem TypeSystemEnforcesFaultRobustness_impl_IOFree :
  (∀ e ctxᵢ predSat tm, TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat tm) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx hwf _hpc hte predSat tm hwfTm hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstep e ctx predSat tm
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hWfRegime hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ htrustedInit₁ htrustedInit₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
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
  have hreg : regimeConsistentWithCtx ctx := htagR
  -- Need consistentWithRegime for both runs (derived from bridge lemma)
  have hcwr₁ : consistentWithRegime predSat R ctx μ₁ ρ₁ θ₁ := by
    have hcrs₁' : consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ := by
      simpa [hRdef] using hcrs₁
    have hWfRegime' : wfRegime R s := by
      simpa [hRdef] using hWfRegime
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₁ ρ₁ θ₁ hcrs₁' hric₁ (by simpa [hRdef] using htrustedInit₁) his hctx hWfRegime'
  have hcwr₂ : consistentWithRegime predSat R ctx μ₂ ρ₂ θ₂ := by
    have hcrs₂' : consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ := by
      simpa [hRdef] using hcrs₂
    have hWfRegime' : wfRegime R s := by
      simpa [hRdef] using hWfRegime
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₂ ρ₂ θ₂ hcrs₂' hric₂ (by simpa [hRdef] using htrustedInit₂) his hctx hWfRegime'
  have hstep_fr :=
    hstep' hps hwfTm μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ hwf hric₁ hric₂ hreg hcwr₁ hcwr₂ hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  -- StepFR result structure: ∃ θ₁' θ₂', wfExtendsMap ∧ wfExtendsMap ∧ valueHasETyp ∧ valueHasETyp ∧
  --   wfTagMeaningCtx ∧ wfTypeContext ∧ wfConfig ∧ wfConfig ∧ ... ∧ agreeOnClean ∧ resultAgreesIfClean
  rcases hstep_fr with ⟨_hresTm, hstep_fr⟩
  rcases hstep_fr with ⟨θ₁', θ₂', hwfext₁, hwfext₂, _hvtyp₁, _hvtyp₂, _hTm', _hwfctx', _hwfcfg₁', _hwfcfg₂', _hric₁', _hric₂', _hreg', _hcwr₁', _hcwr₂', hagree_clean', _hval_consist₁, _hval_consist₂, hret_agree⟩
  refine ⟨θ₁', θ₂', hwfext₁, hwfext₂, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · -- Observable memory locations agree
    intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hctx_lookup : (ctxAfter ctx res).memEnv.lookup l = some qt := by
      simpa [ctxAfter] using hlookup_mem
    -- Use output regime since hagree_clean' now uses (ctxAfter ctx res).regime
    have hclean : qtypCleanUnder (ctxAfter ctx res).regime qt := by
      exact qtypCleanUnder.clean hpoison
    have hlocEntry : agreeLocUnder predSat (ctxAfter ctx res).regime cf₁.memory cf₂.memory θ₁' θ₂' (l, qt) :=
      (hagree_clean'.1 l qt hctx_lookup hclean)
    cases hlocEntry with
    | agree_values _l _qt a₁' a₂' n₁ n₂ hreal₁ hreal₂ hlookup₁ hlookup₂ hagree =>
        -- Reduce to equality of stored ints via agreement on the stored values.
        have hvalEq : n₁ = n₂ := by
          cases hagree with
          | clean_eq_nonref_nonarrow _ _ _ hval =>
              cases hval
              rfl
          | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isArrow = true implies function type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisArrow) (by decide)
          | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv1 _ =>
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
        -- Use output regime since hret_agree now uses (ctxAfter ctx res).regime
        have hret_clean : qtypCleanUnder (ctxAfter ctx res).regime res.qualType :=
          qtypCleanUnder.clean hret_poison
        have hret_agree' :
            agreeValueUnder predSat (ctxAfter ctx res).regime cf₁.memory cf₂.memory θ₁' θ₂' res.qualType o₁ o₂ :=
          hret_agree hret_clean
        cases et with
        | ref ls =>
            cases hret_agree' with
            | @clean_ref ls' l a₁' a₂' _qt _v₁ _v₂ hpoison' hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by
                  have h_eq : ETyp.ref ls' = ETyp.ref ls := by rw [← hetyp, hret_et]
                  injection h_eq
                subst hls_eq
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k ls' l a₁' a₂' _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by
                  have h_eq : ETyp.ref ls' = ETyp.ref ls := by rw [← hetyp, hret_et]
                  injection h_eq
                subst hls_eq
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
                exact (hnotref ⟨ls, hret_et⟩).elim
            | withPred_true_eq _ _ _ _ hnotref _ =>
                exact (hnotref ⟨ls, hret_et⟩).elim
            | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_arrow _ hisArrow =>
                -- qt.etyp is an arrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : False := by
                  have hisArrow_ref : (ETyp.ref ls).isArrow = true := by
                    simpa [hret_et] using hisArrow
                  simp [ETyp.isArrow] at hisArrow_ref
                exact False.elim this
            | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_parrow _ hisParrow =>
                -- qt.etyp is a parrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : False := by
                  have hisParrow_ref : (ETyp.ref ls).isParrow = true := by
                    simpa [hret_et] using hisParrow
                  simp [ETyp.isParrow] at hisParrow_ref
                exact False.elim this
        | int =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | bool =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | unit =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | string =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
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
  · intro e' ctxᵢ predSat tm
    simpa using TypeSystemEnforcesFaultRobustness_step_IOFree e' ctxᵢ predSat tm
