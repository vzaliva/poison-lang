/-
  StepFRDeref.lean - Fault-robustness proof for the deref case.

  Contains stepFR_deref_with_expr_proof and
  stepFRSingleRunFinalCleanPcTrue_deref_maskedReg_with_expr_proof.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

private def DerefCtxToValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx : TypeContext) (e : Expr) (res res1 : TypeResult) (fuel' : Nat)
    (cf : Config) (θ : RealizationMap) (a' : Address) (n : Int),
    typecheckDeref ctx e (Nat.succ fuel') = .ok res →
    typecheck ctx e fuel' = .ok res1 →
    res.memEnv' = res1.memEnv' →
    valueHasETyp θ (Value.loc a') res1.qualType.etyp →
    cf.memory.lookup a' = some n →
    CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ →
    ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ (Value.num n)

private lemma deref_valueConsistentWithRegimeMasked_of_typecheck
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (res res1 : TypeResult) (fuel' : Nat)
  (cf : Config) (θ' : RealizationMap) (a' : Address) (n : Int)
  (htc : typecheckDeref ctxᵢ e (Nat.succ fuel') = .ok res)
  (htc1 : typecheck ctxᵢ e fuel' = .ok res1)
  (hmemEq : res.memEnv' = res1.memEnv')
  (hvloc : valueHasETyp θ' (Value.loc a') res1.qualType.etyp)
  (hlookup_cf : cf.memory.lookup a' = some n)
  (hcwr_final :
    consistentWithRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
      cf.memory cf.varEnv θ') :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime
    res.qualType cf.memory θ' (Value.num n) := by
  have htc1_expr : typecheckExpr ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck] using htc1
  have hderef_etyp_int : res.qualType.etyp = ETyp.int :=
    typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc
  have hnonclos :
      closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime
        res.qualType cf.memory θ' (Value.num n) :=
    closureCapturedVarsRegimeMasked_nonClosure_of_nonFunctionType (θ := θ')
      (by rw [hderef_etyp_int]; exact valueHasETyp.num n)
      (by simp [hderef_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  cases hpred_res : res.qualType.pred with
  | noPred =>
      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag, hpred_res]) hnonclos
  | guardOnly k =>
      exact valueConsistentWithRegimeMasked.guardOnly_ok k (by simp [hpred_res]) hnonclos
  | guardClosure k arg_name pred_body var_env =>
      have htag_res : qtypGuardTag res.qualType = some k := by
        simp [qtypGuardTag, hpred_res]
      cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
      | none =>
          exact valueConsistentWithRegimeMasked.notInRegime k htag_res hk hnonclos
      | some b =>
          have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
            have htc'' := htc
            simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
            cases hq : res1.qualType with
            | mk etyp poison pred =>
                cases etyp with
                | ref ls =>
                    simp [hq] at htc''
                    exact ⟨ls, rfl⟩
                | _ =>
                    simp [hq] at htc''
          rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
          have hres1_poison_false : res1.qualType.poison = false := by
            cases hq : res1.qualType with
            | mk etyp poison pred =>
                cases hpoison : poison with
                | false =>
                    simp
                | true =>
                    have : False := by
                      have h_etyp : etyp = ETyp.ref ls0 := by
                        simpa [hq] using hres1_etyp0
                      have htc_bad := htc
                      simp [typecheckDeref, htc1_expr, hq, h_etyp, hpoison, bind, Except.bind] at htc_bad
                      by_cases hls : ls0 = ∅
                      · simp [hls] at htc_bad
                      · simp [hls] at htc_bad
                        cases hfold :
                            ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                              match res1.memEnv'.lookup l with
                              | some qt =>
                                  pure
                                    (joinPoison x.1 qt.poison,
                                      match x.2 with
                                      | none => some qt.pred
                                      | some p => some (joinPredicates p qt.pred))
                              | none =>
                                  throw
                                    (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                        | error err =>
                            erw [hfold] at htc_bad
                            cases htc_bad
                        | ok v =>
                            erw [hfold] at htc_bad
                            simp [pure, Except.pure] at htc_bad
                            cases htc_bad
                            cases hpred_res
                    exact False.elim this
          rcases valueHasETyp_loc_inv hvloc with ⟨ls1, l, hRef1, hθl, hlin1⟩
          have hls : ls1 = ls0 := by
            rw [hres1_etyp0] at hRef1
            cases hRef1
            rfl
          subst ls1
          have htc'' := htc
          cases hq : res1.qualType with
          | mk etyp poison pred =>
              have h_etyp : etyp = ETyp.ref ls0 := by
                simpa [hq] using hres1_etyp0
              have h_poison : poison = false := by
                simpa [hq] using hres1_poison_false
              simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
              by_cases hls0 : ls0 = ∅
              · simp [hls0] at htc''
              · simp [hls0] at htc''
                cases hfold :
                    ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                      match res1.memEnv'.lookup l with
                      | some qt =>
                          pure (joinPoison x.1 qt.poison,
                            match x.2 with
                            | none => some qt.pred
                            | some p => some (joinPredicates p qt.pred))
                      | none =>
                          throw
                            (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                | error err =>
                    erw [hfold] at htc''
                    cases htc''
                | ok v =>
                    erw [hfold] at htc''
                    have hfold' :
                        LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                          Except.ok v := by
                      simpa [LocSet.foldM, derefFoldF] using! hfold
                    cases hmerged : v.2.getD Predicate.noPred with
                    | noPred =>
                        simp [hmerged, pure, Except.pure] at htc''
                        cases htc''
                        cases hpred_res
                    | guardOnly k' =>
                        cases htagEnv' : res1.tagEnv'[k']? with
                        | some tv =>
                            cases tv with
                            | mk val deps =>
                                cases val with
                                | true =>
                                    simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                    cases htc''
                                    cases hpred_res
                                | false =>
                                    simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                    cases htc''
                                    cases hpred_res
                        | none =>
                            simp [hmerged, htagEnv', pure, Except.pure] at htc''
                            cases htc''
                            cases hpred_res
                    | guardClosure k' arg_name' pred_body' var_env' =>
                        cases htagEnv : res1.tagEnv'[k']? with
                        | some tv =>
                            cases tv with
                            | mk val deps =>
                                cases val with
                                | true =>
                                    simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                    cases htc''
                                    cases hpred_res
                                | false =>
                                    simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                    cases htc''
                                    cases hpred_res
                        | none =>
                            simp [hmerged, htagEnv, pure, Except.pure] at htc''
                            have hEq :
                                { qualType :=
                                    { etyp := ETyp.int, poison := joinPoison ctxᵢ.pc v.1,
                                      pred := Predicate.guardClosure k' arg_name' pred_body' var_env' },
                                  memEnv' := res1.memEnv', tagEnv' := res1.tagEnv', nextLoc' := res1.nextLoc',
                                  nextTag' := res1.nextTag', regime' := res1.regime',
                                  declared' := res1.declared' } = res := by
                              simpa using htc''
                            have hpred_tc : res.qualType.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                              have h := congrArg (fun r => r.qualType.pred) hEq.symm
                              simp at h
                              exact h
                            have hpred_fold :
                                v.2.getD Predicate.noPred =
                                  Predicate.guardClosure k arg_name pred_body var_env := by
                              calc
                                v.2.getD Predicate.noPred =
                                    Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                                  simp [hmerged]
                                _ = res.qualType.pred := by
                                  exact hpred_tc.symm
                                _ = Predicate.guardClosure k arg_name pred_body var_env := by
                                  exact hpred_res
                            obtain ⟨qt_mem, hlookup_mem, hqt_pred⟩ :=
                              deref_foldM_pred_eq_guardClosure res1.memEnv' ls0 v.1 v.2 hfold' hpred_fold l hlin1
                            have hlookup_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_mem := by
                              simpa [ctxAfter, hmemEq] using hlookup_mem
                            have htag_mem : qtypGuardTag qt_mem = some k := by
                              simp [qtypGuardTag, hqt_pred]
                            have hk_ne : (ctxAfter ctxᵢ res).regime.lookup? k ≠ none := by
                              simp [hk]
                            have hmasked_or_hlocs :=
                              hcwr_final.1 l qt_mem k hlookup_ctx htag_mem hk_ne
                            cases hmasked_or_hlocs with
                            | inl hmasked =>
                                exact valueConsistentWithRegimeMasked.maskedTag k
                                  htag_res hmasked hnonclos
                            | inr hlocs =>
                                cases hlocs with
                                | noPred_ok hnone =>
                                    simp [hnone] at htag_mem
                                | guardOnly_ok k'' hgo =>
                                    simp [hqt_pred] at hgo
                                | withPred_ok k0 arg_name0 pred_body0 var_env0 a0 n0 b0 hclos hregime hreal hmem_cell hconsist =>
                                    have ha : a0 = a' := by
                                      have : some a0 = some a' := by
                                        calc
                                          some a0 = θ'.lookup l := by symm; exact hreal
                                          _ = some a' := hθl
                                      exact Option.some.inj this
                                    have hn : n0 = n := by
                                      have : some n0 = some n := by
                                        calc
                                          some n0 = cf.memory.lookup a0 := by symm; exact hmem_cell
                                          _ = cf.memory.lookup a' := by simp [ha]
                                          _ = some n := hlookup_cf
                                      exact Option.some.inj this
                                    have hk0 : k0 = k := by
                                      have htag0 : qtypGuardTag qt_mem = some k0 := by
                                        have hclos' :
                                            qt_mem.pred =
                                              Predicate.guardClosure k0 arg_name0 pred_body0 var_env0 := by
                                          simpa using hclos
                                        simp [qtypGuardTag, hclos']
                                      have : some k0 = some k := by
                                        calc
                                          some k0 = qtypGuardTag qt_mem := by symm; exact htag0
                                          _ = some k := htag_mem
                                      exact Option.some.inj this
                                    have hregime_k : (ctxAfter ctxᵢ res).regime.lookup? k = some b0 := by
                                      simpa [hk0] using hregime
                                    cases hb : b0 with
                                    | true =>
                                        have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                                          simpa [hb] using hregime_k
                                        have hholds_cell : qtypPredHolds predSat qt_mem cf.memory (Value.num n) := by
                                          simpa [hn] using hconsist.1 hb
                                        have hpredEq : qt_mem.pred = res.qualType.pred := by
                                          simp [hqt_pred, hpred_res]
                                        have hholds_res :
                                            qtypPredHolds predSat res.qualType cf.memory (Value.num n) :=
                                          qtypPredHolds_transport_pred (predSat := predSat)
                                            (qt := qt_mem) (qt' := res.qualType) (μ := cf.memory) (v := Value.num n)
                                            hpredEq hholds_cell
                                        exact valueConsistentWithRegimeMasked.inRegimeTrue k
                                          htag_res hktrue hholds_res hnonclos
                                    | false =>
                                        have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                                          simpa [hb] using hregime_k
                                        have hnot_cell : ¬ qtypPredHolds predSat qt_mem cf.memory (Value.num n) := by
                                          simpa [hn] using hconsist.2 hb
                                        have hpredEq : qt_mem.pred = res.qualType.pred := by
                                          simp [hqt_pred, hpred_res]
                                        have hnot_res :
                                            ¬ qtypPredHolds predSat res.qualType cf.memory (Value.num n) :=
                                          qtypPredHolds_transport_pred_not (predSat := predSat)
                                            (qt := qt_mem) (qt' := res.qualType) (μ := cf.memory) (v := Value.num n)
                                            hpredEq hnot_cell
                                        exact valueConsistentWithRegimeMasked.inRegimeFalse k
                                          htag_res hkfalse hnot_res hnonclos

private def StepFRDerefCtxToValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  DerefCtxToValCons CtxCons ValCons

private theorem stepFRDeref_ctxToValCons_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRDerefCtxToValCons
    (fun ctx μ ρ θ =>
      consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v =>
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v) := by
  intro ctx e' res' res1 fuel'' cf θ a' n htc' htc1' hmemEq hvloc hlookup_cf hctxCons
  simpa [StepFRDerefCtxToValCons] using
    deref_valueConsistentWithRegimeMasked_of_typecheck
      (masked := masked) (ctxᵢ := ctx) (predSat := predSat)
      (e := e') (res := res') (res1 := res1) (fuel' := fuel'')
      (cf := cf) (θ' := θ) (a' := a') (n := n)
      htc' htc1' hmemEq hvloc hlookup_cf hctxCons

lemma stepFRSingleRunFinalCleanPcTrue_deref_maskedReg_with_expr_proof
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan : CanUse e)
  (hctxCurrent : CtxReach ctxᵢ)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse
      CtxReach
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v) (registry := registry))
  (htc : typecheck ctxᵢ (Expr.deref e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ =>
      consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v =>
      valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.deref e) res predSat tm (registry := registry) := by
  classical
  have htc' : typecheckDeref ctxᵢ e (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckDeref_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctxᵢ e fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have h_decl : res.declared' = res1.declared' := by
    simp only [typecheckDeref, bind, Except.bind] at htc'
    rw [htc1_expr] at htc'
    simp only at htc'
    cases hqt : res1.qualType with
    | mk etyp p pred =>
      rw [hqt] at htc'
      cases hetyp : etyp with
      | ref ls =>
        rw [hetyp] at htc'
        simp only at htc'
        split at htc' <;> try simp at htc'
        simp only [pure, Except.pure] at htc'
        split at htc' <;> try simp at htc'
        split at htc' <;> (try (cases htc'; rfl))
        split at htc'
        · cases htc'; rfl
        · split at htc' <;> (cases htc'; rfl)
        · split at htc' <;> (cases htc'; rfl)
      | int | bool | unit | string | arrow _ _ | parrow _ _ => simp [hetyp] at htc'
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves hExtTyping predSat tm ctxᵢ
        (Expr.deref e) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht hpc
  have hIH := IH fuel' (by simp)
    e ctxᵢ hctxCurrent hcan hwfTm hTmBounded res1 htc1'
  have hstruct := terminatesTo_deref_inv' e
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  rcases hstruct with ⟨cfg', a', n, ht_e, hlookup, ho, hmem, hvar, _hnext, _hpm⟩
  rcases
    (hIH hpredlaws hExtTyping hwfTm hTmBounded).2 μ ρ θ cfg' (Value.loc a')
      hθwf hwf hric hregCtx hmasked_none hmasked_absent hmasked_bounded hbnd hcwr a pm hwfcfg _hres _hrd ht_e hpc
    with ⟨θ', hθext, hvloc, hric', hctxCons', _hvalc', hpres', _hfresh', _hrd'⟩
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl]
  have hvaltyp_final : valueHasETyp θ' o res.qualType.etyp := by
    subst ho
    rw [typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc']
    exact valueHasETyp.num n
  have hric_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    simpa [hctxAfter, hmem, hvar] using hric'
  have hctxCons_final :
      consistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    simpa [hctxAfter, hmem, hvar] using hctxCons'
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime res.qualType cf.memory θ' o := by
    subst ho
    have hlookup_cf : cf.memory.lookup a' = some n := by
      simpa [hmem] using hlookup
    exact
      stepFRDeref_ctxToValCons_masked masked predSat
        ctxᵢ e res res1 fuel' cf θ' a' n htc' htc1' h_mem hvloc hlookup_cf hctxCons_final
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ' := by
    cases hpres' with
    | intro hpres_fn =>
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hlookup_out1 : res1.memEnv'.lookup l = some qt_out := by
          simpa [h_mem] using hlookup_out
        have hclean_out1 : qtypCleanUnder res1.regime' qt_out := by
          simpa [h_regime] using hclean_out
        simpa [hmem] using hpres_fn l qt_in qt_out hlookup_in hlookup_out1 hclean_out1
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ' := by
    intro l qt hnotIn hlookup hclean
    exact _hfresh' l qt hnotIn (by rwa [h_mem] at hlookup) (by rwa [h_regime] at hclean)
  have hrd_final : ReservedDiscipline cf.registry res.declared' θ' := by
    have hreg_cf : cf.registry = registry := by simpa using terminatesTo_preserves_registry ht
    have hreg_cfg' : cfg'.registry = registry := by simpa using terminatesTo_preserves_registry ht_e
    rw [hreg_cf, h_decl, ← hreg_cfg']; exact _hrd'
  exact ⟨θ', hθext, hvaltyp_final, hric_final, hctxCons_final, hvalc_final, hpres_final, hfresh_final, hrd_final⟩

/-- Run-agnostic value-consistency for the deref result.  Both parallel runs share
this proof: the unmasked statement is recovered from the (more general) masked
case analysis in `deref_valueConsistentWithRegimeMasked_of_typecheck` via
`valueConsistentWithRegimeMasked_unmask` at `masked := fun _ => False` (vacuous
masking). -/
private lemma deref_valueConsistentWithRegime_one_run
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (res res1 : TypeResult) (fuel' : Nat)
  (cf : Config) (θ' : RealizationMap) (a' : Address) (n : Int)
  (htc : typecheckDeref ctxᵢ e (Nat.succ fuel') = .ok res)
  (htc1 : typecheck ctxᵢ e fuel' = .ok res1)
  (hmemEq : res.memEnv' = res1.memEnv')
  (hvloc : valueHasETyp θ' (Value.loc a') res1.qualType.etyp)
  (hlookup_cf : cf.memory.lookup a' = some n)
  (hcwr_final :
    consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
      cf.memory cf.varEnv θ') :
  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
    res.qualType cf.memory θ' (Value.num n) :=
  valueConsistentWithRegimeMasked_unmask (fun _ h => h.elim)
    (deref_valueConsistentWithRegimeMasked_of_typecheck (masked := fun _ => False)
      ctxᵢ predSat e res res1 fuel' cf θ' a' n
      htc htc1 hmemEq hvloc hlookup_cf
      (consistentWithRegime_to_masked (masked := fun _ => False) hcwr_final))

lemma stepFR_deref_with_expr_proof
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan : CanUse e)
  (hctxCurrent : CtxReach ctxᵢ)
  (IH :
    StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
      CanUse CtxReach (registry := registry))
  (hOp : RegistryOperationalSafe registry)
  (htc : typecheck ctxᵢ (Expr.deref e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.deref e) res predSat tm (registry := registry) := by
  classical
  -- Parse typecheck result
  have htc' : typecheckDeref ctxᵢ e (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckDeref_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr ctxᵢ e fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have h_decl : res.declared' = res1.declared' := by
    simp only [typecheckDeref, bind, Except.bind] at htc'
    rw [htc1_expr] at htc'
    simp only at htc'
    cases hqt : res1.qualType with
    | mk etyp p pred =>
      rw [hqt] at htc'
      cases hetyp : etyp with
      | ref ls =>
        rw [hetyp] at htc'
        simp only at htc'
        split at htc' <;> try simp at htc'
        simp only [pure, Except.pure] at htc'
        split at htc' <;> try simp at htc'
        split at htc' <;> (try (cases htc'; rfl))
        split at htc'
        · cases htc'; rfl
        · split at htc' <;> (cases htc'; rfl)
        · split at htc' <;> (cases htc'; rfl)
      | int | bool | unit | string | arrow _ _ | parrow _ _ => simp [hetyp] at htc'
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
  have hIH := IH fuel' (by simp)
    e ctxᵢ hctxCurrent hcan hwfTm htagBounded res1 htc1'
  -- Invert deref evaluation
  have hstruct₀ := terminatesTo_deref_inv' e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀', a₀', n₀, ht₀_e, hlookup₀, hv₀, hmem₀, hvar₀, hnext₀, hpm₀⟩
  have hstruct₁ := terminatesTo_deref_inv' e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁', a₁', n₁, ht₁_e, hlookup₁, hv₁, hmem₁, hvar₁, hnext₁, hpm₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.loc a₀') (Value.loc a₁')
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨tm_e, hcanon_e, hpredlaws_e, hresTm_e, hstep_e⟩
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, _hvtyp₀, _hvtyp₁, _hTm', hwf', _htagBounded', hwfcfg₀', hwfcfg₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e, _hrd₀_e, _hrd₁_e⟩
  -- Post-context is unchanged by deref (only result type changes)
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    cases ctxᵢ
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime, h_decl]
  -- IH gives agreeOnClean with (ctxAfter ctxᵢ res1).regime; transfer via hctxAfter
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  -- IH gives regimeConsistentWithCtx with output regime; transfer via hctxAfter
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using hreg'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved (Expr.deref e) _ cf₀ o₀ hOp hres₀.toBelow ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved (Expr.deref e) _ cf₁ o₁ hOp hres₁.toBelow ht₁ hwfcfg₁).1
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hcwr₀'
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hcwr₁'
  have hresTm : QTypRespectsTagMeaning tm_e res.qualType :=
    typecheckDeref_qtypRespects tm_e ctxᵢ e fuel' res res1 _hTm' htc1_expr htc'
  have hboundary_deref : BoundaryTagMeaningPost ctxᵢ res predSat tm tm_e := by
    exact ⟨BoundaryTagMeaningPost.extends_tm hcanon_e,
      by simpa [h_ntag] using BoundaryTagMeaningPost.bounded hcanon_e,
      by simpa [hctxAfter] using BoundaryTagMeaningPost.wfCtx hcanon_e,
      hresTm,
      hpredlaws_e⟩
  refine ⟨tm_e, hboundary_deref, hpredlaws_e, hresTm, ?_⟩
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_, ?_, ?_⟩
  · subst hv₀
    have hres_etyp_int : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    rw [hres_etyp_int]
    exact valueHasETyp.num n₀
  · subst hv₁
    have hres_etyp_int : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    rw [hres_etyp_int]
    exact valueHasETyp.num n₁
  · simpa [hctxAfter] using _hTm'
  · simpa [hctxAfter] using hwf'
  · -- TagBoundedCtx
    simpa [hctxAfter] using _htagBounded'
  · subst hv₀
    exact deref_valueConsistentWithRegime_one_run ctxᵢ predSat e res res1 fuel'
      cf₀ θ₀' a₀' n₀ htc' htc1' h_mem _hvtyp₀
      (by simpa [hmem₀] using hlookup₀) hcwr₀_final
  · subst hv₁
    exact deref_valueConsistentWithRegime_one_run ctxᵢ predSat e res res1 fuel'
      cf₁ θ₁' a₁' n₁ htc' htc1' h_mem _hvtyp₁
      (by simpa [hmem₁] using hlookup₁) hcwr₁_final
  -- Result agreement when clean: deref reads from a clean location
  intro hclean
  -- We need to show o₀ = o₁ (both are ints from the same logical location)
  -- First, show the argument type is ref int
  have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
    have htc'' := htc'
    simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        cases etyp <;> simp [hq] at htc''
        rename_i ls
        exact ⟨ls, rfl⟩
  -- The reference itself must be unpoisoned if the deref result is clean
  have hres1_poison_false : res1.qualType.poison = false := by
    by_contra hbad
    rcases hres1_etyp with ⟨ls, hres1_etyp⟩
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        -- simplify typecheckDeref under poisonRef = true
        have h_etyp : etyp = ETyp.ref ls := by
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
  -- Use output regime for IH result
  have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
    qtypCleanUnder.clean hres1_poison_false
  have hagree_ref :
      agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType (Value.loc a₀') (Value.loc a₁') :=
    hres_agree_e hres1_clean
  -- Extract the logical location l from reference agreement
  rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
  have ⟨l, hθ₀l, hθ₁l, hlin⟩ :
      ∃ l, θ₀'.lookup l = some a₀' ∧ θ₁'.lookup l = some a₁' ∧ l ∈ ls0 := by
    cases hagree_ref with
    | @clean_ref ls l a1 a2 qt v1 v2 _hetyp_poison hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have hls_eq : ETyp.ref ls = ETyp.ref ls0 := by
          calc
            ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ls0 := hres1_etyp0
        injection hls_eq with hls; subst hls
        -- Align addresses using hv1/hv2
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | @withPred_true_ref k ls l a1 a2 qt v1 v2 _htag _hreg hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have hls_eq : ETyp.ref ls = ETyp.ref ls0 := by
          calc
            ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ls0 := hres1_etyp0
        injection hls_eq with hls; subst hls
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | clean_eq_nonref_nonarrow _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ls0, hres1_etyp0⟩
    | withPred_true_eq _ _ _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ls0, hres1_etyp0⟩
    | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | clean_internal_arrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
    | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | clean_internal_parrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
    | some e =>
        -- get? returns MemEntry; lookup returns QTyp (etyp = int)
        have hlookup_l' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some ⟨ETyp.int, e.poison, e.pred⟩ := by
          simp only [ctxAfter] at hlookup_l
          simp only [ctxAfter, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_l, Option.map] 
        exact ⟨⟨ETyp.int, e.poison, e.pred⟩, hlookup_l'⟩
  obtain ⟨qt, hlookup_ctx⟩ := hlookup_ctx
  -- Get agreement on the location from agreeOnClean (need cleanliness under the *post-e* regime).
  have hclean_loc : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
    -- Analyze typecheckDeref to obtain the fold result, then use hclean.
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        have h_etyp : etyp = ETyp.ref ls0 := by
          simpa [hq] using hres1_etyp0
        have h_poison : poison = false := by
          simpa [hq] using hres1_poison_false
        have htc'' := htc'
        simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
        by_cases hls : ls0 = ∅
        · simp [hls] at htc''
        · simp [hls] at htc''
          cases hfold :
              ls0.foldM (m := Except String) (false, none) (fun x l =>
                match res1.memEnv'.lookup l with
                | some qt =>
                    pure
                      (joinPoison x.1 qt.poison,
                        match x.2 with
                        | none => some qt.pred
                        | some p => some (joinPredicates p qt.pred))
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
                    match res1.memEnv'.lookup l with
                    | some qt =>
                        pure
                          (joinPoison x.1 qt.poison,
                            match x.2 with
                            | none => some qt.pred
                            | some p => some (joinPredicates p qt.pred))
                    | none =>
                        throw
                          (toString "Location " ++ toString l ++ toString " not found in memory environment")) =
                    Except.ok v_3 := by
                simpa using hfold
              erw [hfold_plain] at htc''
              have hfold' :
                  LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                    Except.ok v_3 := by
                simpa [LocSet.foldM, derefFoldF] using! hfold
              have hlookup_ctx' : res1.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_ctx
              cases hclean with
            | clean hpoison =>
                cases hpred : v_3.2.getD Predicate.noPred with
                | noPred =>
                    simp [pure, Except.pure, hpred] at htc''
                    cases htc''
                    have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                      simpa [hpoison]
                    have hjoined_false : v_3.1 = false :=
                      (joinPoison_eq_false hjoin').2
                    obtain ⟨qt', hlookup', hpoison'⟩ :=
                      deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                    have hqt' : qt' = qt := by
                      have : some qt' = some qt := by
                        calc
                          some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
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
                        obtain ⟨qt', hlookup', hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
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
                                -- regime consistency yields regime lookup = some true
                                have htagEnv' :
                                    (ctxAfter ctxᵢ res1).tagEnv.get? k = some ⟨true, deps⟩ := by
                                  simpa [ctxAfter] using htagEnv
                                -- hreg' uses output regime (ctxAfter ctxᵢ res1).regime
                                have hreg_k' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true :=
                                  (hreg' k deps htagEnv')
                                have hreg_k : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := hreg_k'
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred]
                                  simp [predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using! htagqt
                                obtain ⟨qt'', hlookup''⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
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
                        obtain ⟨qt', hlookup', hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
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
                                -- hreg' uses output regime (ctxAfter ctxᵢ res1).regime
                                have hreg_k' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true :=
                                  (hreg' k deps htagEnv')
                                have hreg_k : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := hreg_k'
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred, predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using! htagqt
                                obtain ⟨qt'', hlookup''⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
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
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
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
                        obtain ⟨qt'', hlookup''⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                        have hreg' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := by
                          simpa [ctxAfter, h_regime] using hreg
                        exact qtypCleanUnder.guard k htagqt' hreg' hnotfun'
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
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have htagqt' : qtypGuardTag qt = some k := by
                          have hk : k' = k := by
                            simpa [qtypGuardTag, hpred] using htag
                          simpa [hk, hqt'] using! htagqt
                        obtain ⟨qt'', hlookup''⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                        have hreg'' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := by
                          simpa [ctxAfter, h_regime] using hreg
                        exact qtypCleanUnder.guard k htagqt' hreg'' hnotfun'
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
          | @withPred_true_ref k ls l0 a1 a2 qt' v1 v2 _htag _hreg _hetyp _hlookup1 _hin hv1 _hlookup2 _hv2 =>
              cases hv1
          | clean_internal_arrow _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
            cases hv1
          | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
            cases hv1
          | dirty_internal_arrow _ hisArrow htyp1 _ =>
              -- Value.num can only have type int, so isArrow must be false.
              have hqte_int : qt.etyp = ETyp.int :=
                valueHasETyp_num_etyp htyp1
              have : qt.etyp.isArrow = false := by
                simp [hqte_int, ETyp.isArrow]
              rw [hisArrow] at this
              cases this
          | clean_internal_parrow _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
            cases hv1
          | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
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
  have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
    intro hcontra
    rcases hcontra with ⟨ls, h_etyp⟩
    -- deref always returns int
    have : res.qualType.etyp = ETyp.ref ls := h_etyp
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
  · -- ReservedDiscipline for θ₀'
    have hreg_cf₀ : cf₀.registry = registry := by simpa using terminatesTo_preserves_registry ht₀
    have hreg_cfg₀' : cfg₀'.registry = registry := by simpa using terminatesTo_preserves_registry ht₀_e
    rw [hreg_cf₀, h_decl, ← hreg_cfg₀']; exact _hrd₀_e
  · -- ReservedDiscipline for θ₁'
    have hreg_cf₁ : cf₁.registry = registry := by simpa using terminatesTo_preserves_registry ht₁
    have hreg_cfg₁' : cfg₁'.registry = registry := by simpa using terminatesTo_preserves_registry ht₁_e
    rw [hreg_cf₁, h_decl, ← hreg_cfg₁']; exact _hrd₁_e

