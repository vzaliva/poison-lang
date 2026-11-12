/-
  StepFRVar.lean - Fault-robustness proof for the variable case.

  Contains stepFR_var and stepFRSingleRunFinalCleanPcTrue_var_maskedReg.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

private def VarCtxToValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx : TypeContext) (name : Name) (res : TypeResult)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value),
    typecheckVar ctx name = .ok res →
    ρ.lookup name = some v →
    CtxCons ctx μ ρ θ →
    ValCons (ctxAfter ctx res).regime res.qualType μ θ v

private def StepFRVarCtxToValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  VarCtxToValCons CtxCons ValCons

private lemma var_valueConsistentWithRegime_of_typecheck
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (name : Name) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
  (htc : typecheckVar ctxᵢ name = .ok res)
  (hρ : ρ.lookup name = some v)
  (hcwr : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ) :
  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime res.qualType μ θ v := by
  have hregime' : res.regime' = ctxᵢ.regime :=
    typecheckVar_preserves_regime ctxᵢ name res htc
  have hreg_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by
    simp [ctxAfter, hregime']
  simp [hreg_after]
  cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
  | none =>
      simp [typecheckVar, hlookup_ctx] at htc
  | some qt =>
      cases hpred : qt.pred with
      | noPred =>
          have hres :
              res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
            have htc'' := htc
            cases hqt : qt with
            | mk etyp poison pred =>
                have hpred' : pred = Predicate.noPred := by
                  simpa [hqt] using hpred
                simp [typecheckVar, hlookup_ctx, hpred', hqt, pure, Except.pure] at htc''
                cases htc''
                rfl
          exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
            (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardOnly k =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardOnly k := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              exact valueConsistentWithRegime.guardOnly_ok k (by simp [hres, hpred])
                (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardClosure k arg_name pred_body var_env =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              have hnclos : closureCapturedVarsRegime predSat ctxᵢ.regime res.qualType μ θ v :=
                closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ)
              cases hk : ctxᵢ.regime.lookup? k with
              | none =>
                  exact valueConsistentWithRegime.notInRegime k (by simp [qtypGuardTag, hres, hpred]) hk
                    hnclos
              | some b =>
                  have htag_qt : qtypGuardTag qt = some k := by
                    simp [qtypGuardTag, hpred]
                  have hvr : varsRegime predSat ctxᵢ.regime μ ρ (name, qt) :=
                    hcwr.2.1 name qt k hlookup_ctx htag_qt (by simp [hk])
                  cases hvr with
                  | noPred_ok hnp =>
                      exfalso
                      simp [hnp] at htag_qt
                  | guardOnly_ok _k hgo =>
                      exfalso
                      simp [hpred] at hgo
                  | withPred_ok k' arg_name' pred_body' var_env' v' b' hclos hregime hvar hconsist =>
                      have hk' : k' = k := by
                        have hclos' : qt.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                          simpa using hclos
                        have : some k' = some k := by
                          simpa [qtypGuardTag, hclos'] using htag_qt
                        exact Option.some.inj this
                      cases hk'
                      have hb' : b' = b := by
                        have : some b' = some b := by simpa [hregime] using hk
                        exact Option.some.inj this
                      cases hb'
                      have hv' : v' = v := by
                        have : some v' = some v := by simpa [hvar] using hρ
                        exact Option.some.inj this
                      cases hv'
                      cases b with
                      | false =>
                          have hnot_qt : ¬ qtypPredHolds predSat qt μ v := (hconsist.2 rfl)
                          have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                            qtypPredHolds_transport_pred_not (predSat := predSat) (qt := qt) (qt' := res.qualType)
                              (by simp [hres]) hnot_qt
                          exact valueConsistentWithRegime.inRegimeFalse k
                            (by simp [qtypGuardTag, hres, hpred]) hk hnot_res
                            hnclos
                      | true =>
                          have hholds_qt : qtypPredHolds predSat qt μ v := (hconsist.1 rfl)
                          have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := qt) (qt' := res.qualType)
                              (by simp [hres]) hholds_qt
                          exact valueConsistentWithRegime.inRegimeTrue k
                            (by simp [qtypGuardTag, hres, hpred]) hk hholds_res
                            hnclos
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))

private lemma var_valueConsistentWithRegimeMasked_of_typecheck
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (name : Name) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
  (htc : typecheckVar ctxᵢ name = .ok res)
  (hρ : ρ.lookup name = some v)
  (hcwr : consistentWithRegimeMasked masked predSat ctxᵢ.regime ctxᵢ μ ρ θ) :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime res.qualType μ θ v := by
  have hregime' : res.regime' = ctxᵢ.regime :=
    typecheckVar_preserves_regime ctxᵢ name res htc
  have hreg_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by
    simp [ctxAfter, hregime']
  simp [hreg_after]
  cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
  | none =>
      simp [typecheckVar, hlookup_ctx] at htc
  | some qt =>
      cases hpred : qt.pred with
      | noPred =>
          have hres :
              res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
            have htc'' := htc
            cases hqt : qt with
            | mk etyp poison pred =>
                have hpred' : pred = Predicate.noPred := by
                  simpa [hqt] using hpred
                simp [typecheckVar, hlookup_ctx, hpred', hqt, pure, Except.pure] at htc''
                cases htc''
                rfl
          exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hres])
            (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardOnly k =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardOnly k := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              exact valueConsistentWithRegimeMasked.guardOnly_ok k (by simp [hres, hpred])
                (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardClosure k arg_name pred_body var_env =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              have hnclos :
                  closureCapturedVarsRegimeMasked masked predSat ctxᵢ.regime res.qualType μ θ v :=
                closureCapturedVarsRegimeMasked_transport_etyp
                  (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ)
              cases hk : ctxᵢ.regime.lookup? k with
              | none =>
                  exact valueConsistentWithRegimeMasked.notInRegime k
                    (by simp [qtypGuardTag, hres, hpred]) hk hnclos
              | some b =>
                  have htag_qt : qtypGuardTag qt = some k := by
                    simp [qtypGuardTag, hpred]
                  have hvr_masked : masked k ∨ varsRegime predSat ctxᵢ.regime μ ρ (name, qt) :=
                    hcwr.2.1 name qt k hlookup_ctx htag_qt (by simp [hk])
                  cases hvr_masked with
                  | inl hmasked =>
                      exact valueConsistentWithRegimeMasked.maskedTag k
                        (by simp [qtypGuardTag, hres, hpred]) hmasked hnclos
                  | inr hvr =>
                      cases hvr with
                      | noPred_ok hnp =>
                          exfalso
                          simp [hnp] at htag_qt
                      | guardOnly_ok _k hgo =>
                          exfalso
                          simp [hpred] at hgo
                      | withPred_ok k' arg_name' pred_body' var_env' v' b' hclos hregime hvar hconsist =>
                          have hk' : k' = k := by
                            have hclos' : qt.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                              simpa using hclos
                            have : some k' = some k := by
                              simpa [qtypGuardTag, hclos'] using htag_qt
                            exact Option.some.inj this
                          cases hk'
                          have hb' : b' = b := by
                            have : some b' = some b := by simpa [hregime] using hk
                            exact Option.some.inj this
                          cases hb'
                          have hv' : v' = v := by
                            have : some v' = some v := by simpa [hvar] using hρ
                            exact Option.some.inj this
                          cases hv'
                          cases b with
                          | false =>
                              have hnot_qt : ¬ qtypPredHolds predSat qt μ v := hconsist.2 rfl
                              have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                                qtypPredHolds_transport_pred_not
                                  (predSat := predSat) (qt := qt) (qt' := res.qualType)
                                  (by simp [hres]) hnot_qt
                              exact valueConsistentWithRegimeMasked.inRegimeFalse k
                                (by simp [qtypGuardTag, hres, hpred]) hk hnot_res hnclos
                          | true =>
                              have hholds_qt : qtypPredHolds predSat qt μ v := hconsist.1 rfl
                              have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                                qtypPredHolds_transport_pred
                                  (predSat := predSat) (qt := qt) (qt' := res.qualType)
                                  (by simp [hres]) hholds_qt
                              exact valueConsistentWithRegimeMasked.inRegimeTrue k
                                (by simp [qtypGuardTag, hres, hpred]) hk hholds_res hnclos
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))

private theorem stepFRVar_ctxToValCons_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRVarCtxToValCons
    (fun ctx μ ρ θ =>
      _root_.consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v =>
      _root_.valueConsistentWithRegimeMasked masked predSat R qt μ θ v) := by
  intro ctx name' res' μ ρ θ v htc' hρ hctxCons
  simpa [StepFRVarCtxToValCons, _root_.consistentWithRegimeMasked,
    _root_.valueConsistentWithRegimeMasked, consistentWithRegimeMasked,
    valueConsistentWithRegimeMasked] using
    var_valueConsistentWithRegimeMasked_of_typecheck
      (masked := masked)
      (ctxᵢ := ctx) (predSat := predSat) (name := name') (res := res')
      (μ := μ) (ρ := ρ) (θ := θ) (v := v)
      htc' hρ hctxCons

lemma stepFRSingleRunFinalCleanPcTrue_var_maskedReg
  (masked : Tag → Prop)
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ =>
      consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v =>
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.var name) res predSat tm (Nat.succ fuel) (registry := registry) := by
  have htc' : typecheckVar ctxᵢ name = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  have hdeclared : res.declared' = ctxᵢ.declaredExternRefs := by
    have htc'' := htc'
    simp [typecheckVar] at htc''
    split at htc'' <;>
      (repeat (first | split at htc'' | simp [pure, Except.pure, throw] at htc'' | cases htc'' | rfl))
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter,
      typecheckVar_preserves_memEnv ctxᵢ name res htc',
      typecheckVar_preserves_tagEnv ctxᵢ name res htc',
      typecheckVar_preserves_nextLoc ctxᵢ name res htc',
      typecheckVar_preserves_nextTag ctxᵢ name res htc',
      typecheckVar_preserves_regime ctxᵢ name res htc',
      hdeclared]
  intro hpredlaws hframe hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves predSat tm ctxᵢ
        (Expr.var name) (Nat.succ fuel) res hwfTm hTmBounded hframe htc
  intro μ ρ θ cf o hθwf _hwf hric _hreg _hmasked_none _hmasked_absent _hmasked_bounded _hbnd hctxCons a pm hwfcfg _hres _hrd ht _hpc _P _hP _hroot
  rcases
    terminatesTo_var_inv' name
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
    with ⟨v, hlookup, hcf, ho⟩
  subst hcf
  have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
    rw [ho]
    exact var_valueHasETyp_of_typecheck ctxᵢ μ ρ θ name res v htc' hθwf hric hlookup
  have hvalc :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime res.qualType μ θ o := by
    rw [ho]
    exact
      stepFRVar_ctxToValCons_masked masked predSat
        ctxᵢ name res μ ρ θ v htc' hlookup hctxCons
  refine ⟨θ, ?_, hvaltyp, ?_, ?_, hvalc, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ hlookup => hlookup, fun hθwf' => hθwf'⟩
  · simpa [hctxAfter] using hric
  · simpa [hctxAfter] using hctxCons
  · simpa [hctxAfter] using
      (PreservesInheritedFinalCleanLocsOneRun.refl (ctx := ctxᵢ) (res := res) (ρ := ρ) hric)
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter
  · -- ReservedDiscipline for θ'
    have hdecl : res.declared' = ctxᵢ.declaredExternRefs := by
      have := congrArg TypeContext.declaredExternRefs hctxAfter
      simpa [ctxAfter] using this
    rwa [hdecl]

lemma stepFR_var
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFR ctxᵢ (Expr.var name) res predSat tm (Nat.succ fuel) (registry := registry) := by
  intro hpredlaws _hframe hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁ _P₀ _P₁ _hprem _hroot₀ _hroot₁
  have htagR : tagEnvConsistentWithRegime ctxᵢ.tagEnv ctxᵢ.regime := hreg
  -- Use inversion lemma to extract config and value
  have hinv₀ := terminatesTo_var_inv' name
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  have hinv₁ := terminatesTo_var_inv' name
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
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
  --            regimeConsistentWithCtx ... ∧ agreeOnClean ... ∧ valueConsistentWithRegime ... ∧ valueConsistentWithRegime ... ∧ resultAgreesIfClean ...
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
  have hreg_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by
    simp [ctxAfter, hregime']
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
    | none =>
        simp [typecheckVar, hlookup_ctx] at htc'
    | some qt =>
        have hqtTm : QTypRespectsTagMeaning tm qt :=
          wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ name qt hwfTm hlookup_ctx
        cases hpred : qt.pred with
        | noPred =>
            have hres :
                res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
              have htc'' := htc'
              cases hqt : qt with
              | mk etyp poison pred =>
                  have hpred' : pred = Predicate.noPred := by
                    simpa [hqt] using hpred
                  simp [typecheckVar, hlookup_ctx, hpred', hqt, pure, Except.pure] at htc''
                  cases htc''
                  rfl
            have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
            have hpredEq : res.qualType.pred = qt.pred := by simp [hres, hpred]
            exact fun {qt'} {k} {d} hinq hqd =>
              (QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
        | guardOnly k =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardOnly k := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                have hpredEq : res.qualType.pred = qt.pred := by simp [hres]
                exact fun {qt'} {k} {d} hinq hqd =>
                  (QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
            | some tv =>
                cases tv with
                | mk b deps =>
                    have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases b with
                    | true =>
                        have hres :
                            res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
                    | false =>
                        have hres :
                            res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
        | guardClosure k arg_name pred_body var_env =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                have hpredEq : res.qualType.pred = qt.pred := by simp [hres]
                exact fun {qt'} {k} {d} hinq hqd =>
                  (QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
            | some tv =>
                cases tv with
                | mk b deps =>
                    have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases b with
                    | true =>
                        have hres :
                            res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
                    | false =>
                        have hres :
                            res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
  have hvcons
      (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
      (hρ : ρ.lookup name = some v)
    (hcwr : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ)
    (hric : runtimeInstantiatesCtx ctxᵢ μ ρ θ) :
    valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime res.qualType μ θ v := by
    exact
      var_valueConsistentWithRegime_of_typecheck
        (ctxᵢ := ctxᵢ) (predSat := predSat) (name := name) (res := res)
        (μ := μ) (ρ := ρ) (θ := θ) (v := v)
        htc' hρ hcwr
  have hcanon : IsCanonicalExtension tm ctxᵢ (Expr.var name) res tm := by
    refine IsCanonicalExtension.refl ?_ ?_ hresTm
    · simpa [hnextTag] using hTmBounded
    · simpa [ctxAfter, hmem] using! hwfTm
  refine ⟨tm, BoundaryTagMeaningPost.of_isCanonical_predSat hcanon hpredlaws
    (WithinLog.refl tm _), hpredlaws, hresTm, ?_⟩
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- valueHasETyp θ₀ o₀ res.qualType.etyp
    exact var_valueHasETyp_of_typecheck ctxᵢ μ₀ ρ₀ θ₀ name res o₀ htc' hθ₀ hric₀ hlookup₀
  · -- valueHasETyp θ₁ o₁ res.qualType.etyp
    exact var_valueHasETyp_of_typecheck ctxᵢ μ₁ ρ₁ θ₁ name res o₁ htc' hθ₁ hric₁ hlookup₁
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res): typecheckVar does not change varEnv/memEnv
    simpa [ctxAfter, hmem] using! hwfTm
  · -- wfTypeContext (ctxAfter ctxᵢ res): typecheckVar does not change the context
    simpa [ctxAfter, wfTypeContext, hmem, hnextLoc] using hwf
  · -- TagBoundedCtx (ctxAfter ctxᵢ res)
    simpa [ctxAfter, TagBoundedCtx, tagEnvBoundedInCtx, predTagsBoundedInCtx, closureEnvBoundedInCtx,
           hmem, htag, hnextTag, hnextLoc, hregime'] using htagBounded
  · -- wfConfig cf₀ (unchanged since var doesn't modify config)
    exact hwfcfg₀
  · -- wfConfig cf₁ (unchanged since var doesn't modify config)
    exact hwfcfg₁
  · -- runtimeInstantiatesCtx for θ₀' (var doesn't change context or config)
    simpa [ctxAfter, hmem] using! hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [ctxAfter, hmem] using! hric₁
  · -- regimeConsistentWithCtx (var doesn't change tagEnv or nextTag or regime)
    -- (ctxAfter ctxᵢ res).regime = res.regime' = ctxᵢ.regime
    simpa [ctxAfter, regimeConsistentWithCtx, htag, hnextTag, hregime'] using hreg
  · -- consistentWithRegime for run 0 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using! hcwr₀
  · -- consistentWithRegime for run 1 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using! hcwr₁
  · -- agreeOnClean for ctxAfter: typecheckVar doesn't change the context (including regime)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using! hagree
  · -- valueConsistentWithRegime for cf₀
    exact hvcons μ₀ ρ₀ θ₀ o₀ hlookup₀ hcwr₀ hric₀
  · -- valueConsistentWithRegime for cf₁
    exact hvcons μ₁ ρ₁ θ₁ o₁ hlookup₁ hcwr₁ hric₁
  · -- Result agreement for clean outputs (requires predicate/tagEnv analysis).
    -- Key: (ctxAfter ctxᵢ res).regime = res.regime' = ctxᵢ.regime
    have hregime_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [ctxAfter, hregime']
    -- Rewrite the goal to use ctxᵢ.regime so the rest of the proof works
    simp only [hregime_after]
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
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
                    have hnotfun_qt : qt.etyp.isFunctionType = false := by
                      simpa [hres] using hnotfun_res
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            exact hnotref ⟨ls, by simpa [hres] using h⟩
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
                        | clean_internal_arrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
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
                        | clean_internal_parrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
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
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            exact hnotref ⟨ls, by simpa [hres] using h⟩
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
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
                        have hnotfun_qt : qt.etyp.isFunctionType = false := by
                          -- If qt.etyp were a function type, typecheckVar would have thrown an error
                          by_contra h
                          simp at h
                          -- From htc', typecheckVar succeeded
                          have htc'' := htc'
                          cases qt with
                          | mk etyp poison pred =>
                              have : pred = Predicate.guardOnly k := by simpa using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by simpa using htag
                              simp [this, h, typecheckVar, hlookup_ctx, htag', throw] at htc''
                              cases htc''
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                exact hnotref ⟨ls, by simpa [hres] using h⟩
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow (by simp [hres, hpc]) hnotfun' hnotref' hEq
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Arrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_arrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                              -- Dirty arrow: qt.etyp is arrow but hnotfun_qt says it's not a function type
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisArrow, Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Parrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                              -- Dirty parrow: qt.etyp is parrow but hnotfun_qt says it's not a function type
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisParrow, Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                exact hnotref ⟨ls, by simpa [hres] using h⟩
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
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
                    have hnotfun_qt : qt.etyp.isFunctionType = false := by
                      simpa [hres] using hnotfun_res
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                        | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Arrow types are function types, contradicts hnotfun_qt
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.true_or] at hnotfun_qt
                            cases hnotfun_qt
                        | clean_internal_arrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.true_or] at hnotfun_qt
                            cases hnotfun_qt
                        | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                            exfalso
                            simp only [ETyp.isFunctionType] at hnotfun_qt
                            rw [hisArrow, Bool.true_or] at hnotfun_qt
                            cases hnotfun_qt
                        | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Parrow types are function types, contradicts hnotfun_qt
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.or_true] at hnotfun_qt
                            cases hnotfun_qt
                        | clean_internal_parrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.or_true] at hnotfun_qt
                            cases hnotfun_qt
                        | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                            exfalso
                            simp only [ETyp.isFunctionType] at hnotfun_qt
                            rw [hisParrow, Bool.or_true] at hnotfun_qt
                            cases hnotfun_qt
                      | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
                      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
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
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
                        have hnotfun_qt : qt.etyp.isFunctionType = false := by
                          -- If qt.etyp were a function type, typecheckVar would have thrown an error
                          by_contra h
                          simp at h
                          -- From htc', typecheckVar succeeded
                          have htc'' := htc'
                          cases qt with
                          | mk etyp poison pred =>
                              have : pred = Predicate.guardClosure k arg_name pred_body var_env := by simpa using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by simpa using htag
                              simp [this, h, typecheckVar, hlookup_ctx, htag', throw] at htc''
                              cases htc''
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Arrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_arrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisArrow, Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Parrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow_extern hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisParrow, Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
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
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
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
  · -- ReservedDiscipline for θ₀'
    have hdecl : res.declared' = ctxᵢ.declaredExternRefs := by
      have htcx := htc'
      simp [typecheckVar] at htcx
      split at htcx <;>
        (repeat (first | split at htcx | simp [pure, Except.pure, throw] at htcx | cases htcx | rfl))
    rwa [hdecl]
  · -- ReservedDiscipline for θ₁'
    have hdecl : res.declared' = ctxᵢ.declaredExternRefs := by
      have htcx := htc'
      simp [typecheckVar] at htcx
      split at htcx <;>
        (repeat (first | split at htcx | simp [pure, Except.pure, throw] at htcx | cases htcx | rfl))
    rwa [hdecl]
