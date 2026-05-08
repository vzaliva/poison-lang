/-
  StepFRNewRef.lean - Fault-robustness proof for the newRef case.

  Contains stepFR_newRef, stepFRSingleRunFinalCleanPcTrue_newRef,
  and exclusive join-lookup helpers.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

variable {registry : ExternRegistry}

private def StepFRSingleRunFinalCleanPcTrueWithCtxValCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
    PredSatLaws predSat tm →
    ExternTypingAssumptions →
    wfTagMeaningCtx tm ctx →
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      wfRealizationMap θ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ ρ θ →
      regimeConsistentWithCtx ctx →
      CtxCons ctx μ ρ θ →
      ∀ (a : Address) (pm : Bool),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } →
        terminatesTo e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o →
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
        CtxCons ValCons ctx e res predSat tm (registry := registry)

private def NewRefCtxConsFinish
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext) (res res1 : TypeResult) (l : Loc) (storedQt : QTyp)
    (cfg1 cf : Config) (θ1 θ' : RealizationMap) (n : Int),
    PredSatLaws predSat tm →
    wfConfig cfg1 →
    (ctxAfter ctx res).regime = (ctxAfter ctx res1).regime →
    res.memEnv' = updateMemEnv res1.memEnv' l storedQt →
    cf.memory = cfg1.memory.update cfg1.nextAddr n →
    cf.varEnv = cfg1.varEnv →
    ctx.pc = true →
    wfExtendsMap θ1 θ' →
    storedQt =
      ⟨ETyp.int, joinPoison ctx.pc res1.qualType.poison,
        if ctx.pc = true then Predicate.noPred else res1.qualType.pred⟩ →
    CtxCons (ctxAfter ctx res1) cfg1.memory cfg1.varEnv θ1 →
    CtxCons (ctxAfter ctx res) cf.memory cf.varEnv θ'

private def NewRefResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx : TypeContext) (res : TypeResult) (cf : Config)
    (θ : RealizationMap) (a : Address),
    res.qualType.pred = Predicate.noPred →
    ValCons (ctxAfter ctx res).regime res.qualType cf.memory θ (Value.loc a)

private lemma newRef_valueConsistentWithRegimeMasked_result
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (res : TypeResult) (cf : Config)
  (θ : RealizationMap) (a : Address)
  (hpred : res.qualType.pred = Predicate.noPred) :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx res).regime
    res.qualType cf.memory θ (Value.loc a) := by
  refine valueConsistentWithRegimeMasked.noTag ?_ ?_
  · simp [qtypGuardTag, hpred]
  · exact
      .nonClosure
        (by intro xp body ρcap h; simp at h)
        (by intro xp body ρcap h; simp at h)

private lemma consistentWithRegimeMasked_newRef_finish
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (res res1 : TypeResult) (l : Loc) (storedQt : QTyp)
  (cfg' cf : Config) (θ1 θ' : RealizationMap) (n : Int)
  (hpredlaws : PredSatLaws predSat tm)
  (hwfcfg1 : wfConfig cfg')
  (hregime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime)
  (h_mem : res.memEnv' = updateMemEnv res1.memEnv' l storedQt)
  (hmem : cf.memory = cfg'.memory.update cfg'.nextAddr n)
  (hvar : cf.varEnv = cfg'.varEnv)
  (hpc : ctxᵢ.pc = true)
  (hθext' : wfExtendsMap θ1 θ')
  (hstoredQt :
    storedQt =
      ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison,
        if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩)
  (hcwr1 :
    consistentWithRegimeMasked masked predSat (ctxAfter ctxᵢ res1).regime (ctxAfter ctxᵢ res1)
      cfg'.memory cfg'.varEnv θ1) :
  consistentWithRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
    cf.memory cf.varEnv θ' := by
  have hqtypPredHolds_mem :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg'.memory v ↔ qtypPredHolds predSat qt cf.memory v := by
    intro qt v
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ1 cfg'.memory cf.memory qt v
  constructor
  · intro l0 qt k hlookup hguard hkR
    by_cases h_eq : l0 = l
    · subst l0
      have hlookup' : res.memEnv'.lookup l = some qt := by
        simpa [ctxAfter] using hlookup
      rw [h_mem] at hlookup'
      have hqt : qt = storedQt := by
        have hself :
            (updateMemEnv res1.memEnv' l storedQt).lookup l =
              some ⟨ETyp.int, storedQt.poison, storedQt.pred⟩ := by
          simp [updateMemEnv, MemoryTypeEnv.lookup]
        have hqt' : qt = ⟨ETyp.int, storedQt.poison, storedQt.pred⟩ := by
          apply Option.some.inj
          calc
            some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by
              symm
              exact hlookup'
            _ = some ⟨ETyp.int, storedQt.poison, storedQt.pred⟩ := hself
        simpa [hstoredQt] using hqt'
      subst qt
      have : False := by
        simp [hstoredQt, hpc, qtypGuardTag] at hguard
      exact False.elim this
    · have hlookup_res1 : res1.memEnv'.lookup l0 = some qt := by
        have hlookup' : res.memEnv'.lookup l0 = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        rw [MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq] at hlookup'
        exact hlookup'
      have hkR1 : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hmasked_or_hloc :=
        hcwr1.1 l0 qt k (by simpa [ctxAfter] using hlookup_res1) hguard hkR1
      cases hmasked_or_hloc with
      | inl hmasked =>
          exact Or.inl hmasked
      | inr hloc =>
          cases hloc with
          | noPred_ok hpred =>
              exact Or.inr (locsRegime.noPred_ok (l0, qt) hpred)
          | guardOnly_ok k' hgo =>
              exact Or.inr (locsRegime.guardOnly_ok (l0, qt) k' hgo)
          | withPred_ok k' arg_name pred_body var_env a_old n_old b hclos hreg hreal hmem_old hcons =>
              have hreal' : θ'.lookup l0 = some a_old := by
                exact hθext'.1 l0 a_old hreal
              have hcontains_addr : cfg'.memory.contains a_old = true := Memory_contains_of_lookup hmem_old
              have hneq_addr : a_old ≠ cfg'.nextAddr := by
                intro haeq
                subst haeq
                exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr hcontains_addr)
              have hmem_same : cf.memory.lookup a_old = cfg'.memory.lookup a_old := by
                rw [hmem]
                simpa [Memory.update] using
                  (Memory_lookup_update_ne (μ := cfg'.memory) (a := a_old) (a' := cfg'.nextAddr) (v := n) hneq_addr)
              have hmem_final : cf.memory.lookup a_old = some n_old := by
                rw [hmem_same]
                exact hmem_old
              have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
                simpa [hregime_eq] using hreg
              have hcons' :
                  (b = true → qtypPredHolds predSat qt cf.memory (Value.num n_old)) ∧
                  (b = false → ¬ qtypPredHolds predSat qt cf.memory (Value.num n_old)) := by
                constructor
                · intro hb
                  exact (hqtypPredHolds_mem qt (Value.num n_old)).1 (hcons.1 hb)
                · intro hb hholds
                  exact (hcons.2 hb) ((hqtypPredHolds_mem qt (Value.num n_old)).2 hholds)
              exact Or.inr <|
                locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a_old n_old b
                  hclos hreg' hreal' hmem_final hcons'
  constructor
  · intro x qt k hlookup hguard hkR
    have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    have hkR1 : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
      simpa [hregime_eq] using hkR
    have hmasked_or_hvars := hcwr1.2.1 x qt k hlookup_old hguard hkR1
    cases hmasked_or_hvars with
    | inl hmasked =>
        exact Or.inl hmasked
    | inr hvars =>
        cases hvars with
        | noPred_ok hpred =>
            exact Or.inr (varsRegime.noPred_ok (x, qt) hpred)
        | guardOnly_ok k' hgo =>
            exact Or.inr (varsRegime.guardOnly_ok (x, qt) k' hgo)
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar_old hcons =>
            have hvar' : cf.varEnv.lookup x = some v := by
              simpa [hvar] using hvar_old
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq] using hreg
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf.memory v) := by
              constructor
              · intro hb
                exact (hqtypPredHolds_mem qt v).1 (hcons.1 hb)
              · intro hb hholds
                exact (hcons.2 hb) ((hqtypPredHolds_mem qt v).2 hholds)
            exact Or.inr <|
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hvar' hcons'
  · intro x qt v hlookup hlookup_v
    have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    have hlookup_v_old : cfg'.varEnv.lookup x = some v := by
      simpa [hvar] using hlookup_v
    have hcap :
        closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctxᵢ res).regime qt cfg'.memory θ1 v := by
      rw [hregime_eq]
      exact hcwr1.2.2 x qt v hlookup_old hlookup_v_old
    exact closureCapturedVarsRegimeMasked_transport_μ_θ hqtypPredHolds_mem hθext'.1 hcap

private def StepFRNewRefCtxConsFinish
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  NewRefCtxConsFinish CtxCons predSat tm

private def StepFRNewRefResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  NewRefResultValCons ValCons

private theorem stepFRNewRef_ctxConsFinish_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRNewRefCtxConsFinish
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    predSat tm := by
  intro ctx res' res1 l storedQt cfg1 cf θ1 θ' n
    hpredlaws hwfcfg1 hregime_eq hmemEq hmem hvar hpc hθext hstoredQt hctxCons
  simpa [StepFRNewRefCtxConsFinish] using
    consistentWithRegimeMasked_newRef_finish
      (masked := masked)
      (ctxᵢ := ctx) (predSat := predSat) (tm := tm)
      (res := res') (res1 := res1) (l := l) (storedQt := storedQt)
      (cfg' := cfg1) (cf := cf) (θ1 := θ1) (θ' := θ') (n := n)
      hpredlaws hwfcfg1 hregime_eq hmemEq hmem hvar hpc hθext hstoredQt hctxCons

private theorem stepFRNewRef_resultValCons_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRNewRefResultValCons
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v) := by
  intro ctx res cf θ a hpred
  simpa [StepFRNewRefResultValCons] using
    newRef_valueConsistentWithRegimeMasked_result
      (masked := masked)
      (ctx := ctx) (predSat := predSat) (res := res) (cf := cf) (θ := θ) (a := a)
      hpred

lemma stepFRSingleRunFinalCleanPcTrue_newRef_maskedReg
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel'))
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v) (registry := registry))
  (htc : typecheck ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.newRef e) res predSat tm (registry := registry) := by
  classical
  have htc' : typecheckNewRef ctxᵢ e (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨res1, l, htc1, hl, _h_etyp1, h_etyp, _h_poison, h_pred, h_mem, _h_tag, _h_loc, _h_ntag, h_regime⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves hExtTyping predSat tm ctxᵢ
        (Expr.newRef e) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hmasked_absent hcwr a pm hwfcfg ht hpc
  have hIH := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm hTmBounded res1 htc1'
  have hstruct := terminatesTo_newRef_inv' e
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  rcases hstruct with ⟨cfg', n, ht_e, ho, hmem, _hnext, hvar, _hpm⟩
  rcases
    (hIH hpredlaws hExtTyping hwfTm hTmBounded).2 μ ρ θ cfg' (Value.num n)
      hθwf hwf hric hregCtx hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e hpc
    with ⟨θ1, hθext1, hvnum1, hric1, hctxCons1, _hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwf1 : wfTypeContext (ctxAfter ctxᵢ res1) :=
    wfTypeContext_of_wfTypeResult ctxᵢ res1
      (typecheckExpr_preserves_wfTypeResult ctxᵢ e fuel' res1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctxᵢ e fuel' res1 htc1')
  have hwfcfg1 : wfConfig cfg' := (wfConfig_preserved e _ cfg' (Value.num n) ht_e hwfcfg).1
  have hregime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime := by
    simp [ctxAfter, h_regime]
  let θ' := θ1.update l cfg'.nextAddr
  let storedQt : QTyp :=
    ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison,
      if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  have h_fresh : θ1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by
      simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg'.memory cfg'.varEnv θ1 l hwf1 hric1 hge
  have hθext' : wfExtendsMap θ1 θ' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst h_eq
        rw [h_fresh] at hlookup
        cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp
          have : l = l' := LawfulEqCmp.eq_of_compare hcmp
          exact h_eq this.symm
        have h_theta_def : θ' = θ1.insert l cfg'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]
        simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]
        exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a0 hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ1.get? l' ≠ some cfg'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ1.lookup l' = some cfg'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]
          exact h_eq
        have h_contains : cfg'.memory.contains cfg'.nextAddr := (hric1.1 l' cfg'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a0, θ1.get? k₁ = some a0 → θ1.get? k₂ = some a0 → k₁ = k₂ := by
        intro k₁ k₂ a0 h1 h2
        exact hWF k₁ k₂ a0 h1 h2
      have hlookup1' : (θ1.insert l cfg'.nextAddr).get? l₁ = some a0 := hlookup1
      have hlookup2' : (θ1.insert l cfg'.nextAddr).get? l₂ = some a0 := hlookup2
      exact
        ExtTreeMap_insert_preserves_injectivity
          θ1 l cfg'.nextAddr h_fresh_value' h_inj' l₁ l₂ a0 hlookup1' hlookup2'
  have hθext : wfExtendsMap θ θ' := wfExtendsMap_trans hθext1 hθext'
  have hric_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    unfold runtimeInstantiatesCtx
    rcases hric1 with ⟨hmem1, hvars1⟩
    constructor
    · intro l' a' hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a' = cfg'.nextAddr := by
          have hself : θ'.lookup l = some cfg'.nextAddr := by
            simp [θ', RealizationMap.update, RealizationMap.lookup]
          have : (some a' : Option Address) = some cfg'.nextAddr := by
            calc
              some a' = θ'.lookup l := by symm; exact hlookup
              _ = some cfg'.nextAddr := hself
          exact Option.some.inj this
        subst a'
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by
            rw [h_mem]
            simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf.memory.contains cfg'.nextAddr := by
          rw [hmem]
          simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hlookup_old : θ1.lookup l' = some a' := by
          simpa [θ', RealizationMap_lookup_update_ne h_eq] using hlookup
        have hmem_old := hmem1 l' a' hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by
          simpa [ctxAfter] using hmem_old.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]
            simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf.memory.contains a' := by
          have hμ1 : cfg'.memory.contains a' := hmem_old.2
          rw [hmem, ExtTreeMap.contains_insert]
          simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      have hlookup1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars1 hlookup1
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar] using hvlookup
      · exact valueHasETyp_extends hθext'.1 hvtyp
  have hctxCons_final :
      consistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    exact
      stepFRNewRef_ctxConsFinish_masked masked predSat tm
        ctxᵢ res res1 l storedQt cfg' cf θ1 θ' n
        hpredlaws hwfcfg1 hregime_eq h_mem hmem hvar hpc hθext' rfl hctxCons1
  have hclean_back :
      ∀ l0 qt_in qt_out,
        ctxᵢ.memEnv.lookup l0 = some qt_in →
        res.memEnv'.lookup l0 = some qt_out →
        qtypCleanUnder res.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l0 = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l0 qt_in qt_out hlookup_in hlookup_out hclean_out
    by_cases h_eq : l0 = l
    · subst l0
      have hcontains_in : ctxᵢ.memEnv.contains l = true :=
        memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
      have hlt_ctx : l < ctxᵢ.nextLoc := hwf.1 l hcontains_in
      have hmono_next : ctxᵢ.nextLoc ≤ res1.nextLoc' :=
        typecheck_nextLoc_mono ctxᵢ e fuel' res1 htc1'
      have hlt_res1 : l < res1.nextLoc' := Nat.lt_of_lt_of_le hlt_ctx hmono_next
      have : False := by simp [hl] at hlt_res1
      exact this.elim
    · have hlookup_mid : res1.memEnv'.lookup l0 = some qt_out := by
        rw [h_mem] at hlookup_out
        rw [MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq] at hlookup_out
        exact hlookup_out
      have hclean_mid : qtypCleanUnder res1.regime' qt_out := by
        simpa [h_regime] using hclean_out
      exact ⟨qt_out, hlookup_mid, hclean_mid⟩
  have hwrite_pres :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctxᵢ res1) res cfg'.memory cf.memory θ1 θ' := by
    refine ⟨?_⟩
    intro l0 qt_in qt_out hlookup_in _hlookup_out _hclean_out
    by_cases h_eq : l0 = l
    · subst l0
      have hcontains_mid : res1.memEnv'.contains l = true :=
        memEnv_contains_of_lookup_some res1.memEnv' l qt_in hlookup_in
      have hlt_mid : l < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l = true := by
          simpa [ctxAfter] using hcontains_mid
        exact hwf1.1 l this
      have : False := by simp [hl] at hlt_mid
      exact this.elim
    · cases hθ1lookup : θ1.lookup l0 with
      | none =>
          have hθout : θ'.lookup l0 = none := by
            simpa [θ', RealizationMap_lookup_update_ne h_eq] using hθ1lookup
          exact .both_unrealized hθ1lookup hθout
      | some a_old =>
          have hcontains_addr : cfg'.memory.contains a_old = true := by
            exact (hric1.1 l0 a_old hθ1lookup).2
          rcases Memory_lookup_some_of_contains hcontains_addr with ⟨n_old, hlookup_mem_in⟩
          have hneq_addr : a_old ≠ cfg'.nextAddr := by
            intro haeq
            subst haeq
            exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr hcontains_addr)
          have hθout : θ'.lookup l0 = some a_old := by
            simpa [θ', RealizationMap_lookup_update_ne h_eq] using hθ1lookup
          have hmem_same : cf.memory.lookup a_old = cfg'.memory.lookup a_old := by
            rw [hmem]
            simpa [Memory.update] using
              (Memory_lookup_update_ne (μ := cfg'.memory) (a := a_old) (a' := cfg'.nextAddr) (v := n) hneq_addr)
          have hlookup_mem_out : cf.memory.lookup a_old = some n_old := by
            rw [hmem_same]
            exact hlookup_mem_in
          exact .preserve_value a_old n_old hθ1lookup hlookup_mem_in hθout hlookup_mem_out
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ' := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctxᵢ) (res1 := res1) (res2 := res)
        hclean_back hpres1 hwrite_pres
  have hvaltyp_final : valueHasETyp θ' o res.qualType.etyp := by
    subst ho
    rw [h_etyp]
    have hlookup : θ'.lookup l = some cfg'.nextAddr := by
      simp [θ', RealizationMap.update, RealizationMap.lookup]
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime res.qualType cf.memory θ' o := by
    subst ho
    exact stepFRNewRef_resultValCons_masked masked predSat ctxᵢ res cf θ' cfg'.nextAddr h_pred
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ' := by
    intro l0 qt hnotIn hlookup hclean
    by_cases h_eq : l0 = l
    · subst l0
      have hpoison_true : qt.poison = true := by
        rw [h_mem] at hlookup
        simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
          Std.ExtTreeMap.getElem?_insert_self, Option.map] at hlookup
        have hqt_eq := Option.some.inj hlookup
        rw [← hqt_eq]
        simp [joinPoison, hpc]
      have hpred_noPred : qt.pred = Predicate.noPred := by
        rw [h_mem] at hlookup
        simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
          Std.ExtTreeMap.getElem?_insert_self, Option.map] at hlookup
        have hqt_eq := Option.some.inj hlookup
        rw [← hqt_eq]
        simp [hpc]
      cases hclean with
      | clean hp => simp [hpoison_true] at hp
      | guard k htag _ _ =>
          simp [qtypGuardTag, hpred_noPred] at htag
    · have hlookup1 : res1.memEnv'.lookup l0 = some qt := by
        rw [h_mem] at hlookup
        rwa [MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq] at hlookup
      have hclean1 : qtypCleanUnder res1.regime' qt := by
        rwa [h_regime] at hclean
      have hθ1_none := _hfresh1 l0 qt hnotIn hlookup1 hclean1
      simpa [θ', RealizationMap_lookup_update_ne h_eq] using hθ1_none
  exact
    ⟨θ', hθext, hvaltyp_final, hric_final, hctxCons_final, hvalc_final, hpres_final, hfresh_final⟩


lemma stepFR_newRef
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry))
  (htc : typecheck ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.newRef e) res predSat tm (registry := registry) := by
  -- Parse typecheck result
  have htc' : typecheckNewRef ctxᵢ e (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  obtain ⟨res1, l, htc1, hl, h_etyp1, h_etyp, h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm htagBounded res1 htc1'
  -- Use world-free inversion lemma for newRef
  have hstruct₀ := terminatesTo_newRef_inv' e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀', n₀, ht₀_e, ho₀, hmem₀, hnext₀, hvar₀, hpm₀⟩
  have hstruct₁ := terminatesTo_newRef_inv' e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁', n₁, ht₁_e, ho₁, hmem₁, hnext₁, hvar₁, hpm₁⟩
  -- Apply IH for e
  have hstep_e :=
    hIH hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.num n₀) (Value.num n₁)
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hstep_e⟩
  rcases hstep_e with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e⟩
  -- Derive regime equality: newRef preserves regime (res.regime' = res1.regime')
  -- From typecheckNewRef_structure, we already have h_regime
  -- This gives us (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime
  have hregime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime := by
    simp [ctxAfter, h_regime]
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
    simp only [wfTypeContext, ctxAfter]
    have hmono_res : ctxᵢ.nextLoc ≤ res.nextLoc' := by
      rw [h_loc]; exact Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e fuel' res1 htc1') (Nat.le_succ _)
    refine ⟨?_, varEnvRefLocsBounded_mono hwf.2.1 hmono_res,
             varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono_res⟩
    intro l' hcontains
    rw [h_mem] at hcontains
    rw [h_loc]
    by_cases h_eq : l' = l
    · subst h_eq; rw [hl]; exact Nat.lt_succ_self res1.nextLoc'
    · have hmem : l' ∈ updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩ :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have h_isSome : ((updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩)[l']?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      have h_cmp_ne : compare l l' ≠ Ordering.eq := by
        intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
      have h_isSome' : (res1.memEnv'[l']?).isSome = true := by
        simpa [updateMemEnv, ExtTreeMap.getElem?_insert, h_cmp_ne] using h_isSome
      have hmem' : l' ∈ res1.memEnv' := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 h_isSome'
      have hcontains' : res1.memEnv'.contains l' = true := (Std.ExtTreeMap.contains_iff_mem).2 hmem'
      have hlt : l' < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l' := by simpa [ctxAfter] using hcontains'
        exact hwf1.1 l' this
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
  -- Prove regimeConsistentWithCtx (IH gives with output regime)
  have hreg' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    -- htagR1 gives regimeConsistentWithCtx (ctxAfter ctxᵢ res1); use hregime_eq to transfer
    unfold regimeConsistentWithCtx
    rw [hregime_eq]
    simpa [ctxAfter, h_tag, h_ntag] using htagR1
  -- Prove agreeOnClean (using output regime from IH)
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    rw [hregime_eq]
    have hqtypPredHolds_mem₀ :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v :=
      qtypPredHolds_mem_compat_of_predSatLaws
        (hpredlaws := hpredlaws) (θ := θ₀1) (μ := cfg₀'.memory) (μ' := cf₀.memory)
    have hqtypPredHolds_mem₁ :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v :=
      qtypPredHolds_mem_compat_of_predSatLaws
        (hpredlaws := hpredlaws) (θ := θ₁1) (μ := cfg₁'.memory) (μ' := cf₁.memory)
    exact agreeOnClean_newRef_extend
      predSat (ctxAfter ctxᵢ res1).regime ctxᵢ res1 res l ETyp.int
      cfg₀' cfg₁' cf₀ cf₁ n₀ n₁ cfg₀'.nextAddr cfg₁'.nextAddr θ₀1 θ₁1 θ₀' θ₁'
      h_mem h_etyp1 rfl rfl rfl hmem₀ hmem₁ hvar₀ hvar₁ rfl rfl
      hθext₀' hθext₁' hwfcf₀1 hwfcf₁1 hqtypPredHolds_mem₀ hqtypPredHolds_mem₁
      hagree_clean_e hres_agree_e
  -- Derive wfConfig for final configs
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved (Expr.newRef e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved (Expr.newRef e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  -- consistentWithRegime for extended realization maps
  -- Key insight: res.regime' = res1.regime' (newRef doesn't change regime)
  -- For newRef:
  -- 1. New location l has a fresh address with storedQt whose pred is gated by ctxᵢ.pc
  -- 2. Old locations transfer from hcwr₀1/hcwr₁1
  -- 3. VarEnv is unchanged
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    classical
    let storedQt : QTyp :=
      ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
    have hPredSat_mem :
        ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
      intro k μ μ' v
      exact predSat_mem_noPred_compat hpredlaws θ₀1 k μ μ' v
    have hqtypPredHolds_mem :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v := by
      intro qt v
      constructor
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cf₀.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).1 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cf₀.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).1 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cfg₀'.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).2 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cfg₀'.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).2 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
    constructor
    · intro l0 qt k hlookup hguard hkR
      by_cases h_eq : l0 = l
      · subst l0
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
        -- New logical location: realized at the freshly allocated address.
        have hreal : θ₀'.lookup l = some cfg₀'.nextAddr := by
          simp [θ₀', RealizationMap.update, RealizationMap.lookup]
        have hmem_new : cf₀.memory.lookup cfg₀'.nextAddr = some n₀ := by
          rw [hmem₀]
          simp [Memory.lookup]
        cases hpred_case : storedQt.pred with
        | noPred =>
            -- Contradiction: no guard tag.
            have hnone : qtypGuardTag storedQt = none := by
              simp [qtypGuardTag, hpred_case]
            have hne : (none : Option Tag) ≠ some k := by simp
            exact (hne (hnone.symm.trans hguard)).elim
        | guardOnly k0 =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            exact locsRegime.guardOnly_ok (l, storedQt) k (by simpa [storedQt, hpred_case])
        | guardClosure k0 arg_name pred_body var_env =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            -- Determine the regime's boolean for k.
            cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
            | none =>
                exact (hkR hk).elim
            | some b =>
                have hval0 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                      res1.qualType cfg₀'.memory θ₀1 (Value.num n₀) := by
                  simpa [hregime_eq] using _hval_consist₀
                have hpc_false : ctxᵢ.pc = false := by
                  cases hpc : ctxᵢ.pc with
                  | false => exact rfl
                  | true =>
                      simp [storedQt, hpc] at hpred_case
                have hpred_res1 :
                    res1.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                  simpa [storedQt, hpc_false] using hpred_case
                have htag_res1 : qtypGuardTag res1.qualType = some k := by
                  simp [qtypGuardTag, hpred_res1]
                have hpredEq : res1.qualType.pred = storedQt.pred := by
                  simp [storedQt, hpc_false]
                have hconsist_old :
                      (b = true → qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀)) := by
                    cases hb : b with
                    | true =>
                        have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                          simpa [hb] using hk
                        have hholds_res1 :
                            qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) := by
                          cases hval0 with
                          | noTag hnotag =>
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeTrue k' htag hkR' hholds =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              -- hkR' must match hktrue
                              have : some true = some true := by
                                calc
                                  some true = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some true := hktrue
                              exact hholds
                          | inRegimeFalse k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              -- Contradiction with hktrue
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by simpa using hkR'
                              simp [this] at hktrue
                        have hholds_stored_old :
                            qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀) :=
                          qtypPredHolds_transport_pred (predSat := predSat) (qt := res1.qualType) (qt' := storedQt)
                            (μ := cfg₀'.memory) (v := Value.num n₀) hpredEq hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro _; exact hholds_stored_old
                        · intro hbfalse; cases hbfalse
                    | false =>
                        have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                          simpa [hb] using hk
                        have hnot_res1 :
                            ¬ qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) := by
                          cases hval0 with
                          | noTag hnotag =>
                              intro _
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeFalse k' htag hkR' hnot =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some false = some false := by
                                calc
                                  some false = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some false := hkfalse
                              exact hnot
                          | inRegimeTrue k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by simpa using hkR'
                              simp [this] at hkfalse
                        have hnot_stored_old :
                            ¬ qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀) := by
                          intro hholds_stored
                          have hholds_res1 :
                              qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := storedQt) (qt' := res1.qualType)
                              (μ := cfg₀'.memory) (v := Value.num n₀) (by simp [hpredEq]) hholds_stored
                          exact hnot_res1 hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro hbtrue; cases hbtrue
                        · intro _; exact hnot_stored_old
                have hconsist :
                    (b = true → qtypPredHolds predSat storedQt cf₀.memory (Value.num n₀)) ∧
                    (b = false → ¬ qtypPredHolds predSat storedQt cf₀.memory (Value.num n₀)) := by
                  constructor
                  · intro hbtrue
                    have hholds_old := hconsist_old.1 hbtrue
                    exact (hqtypPredHolds_mem storedQt (Value.num n₀)).1 hholds_old
                  · intro hbfalse hholds_new
                    have hholds_old := (hqtypPredHolds_mem storedQt (Value.num n₀)).2 hholds_new
                    exact (hconsist_old.2 hbfalse) hholds_old
                exact
                  locsRegime.withPred_ok (l, storedQt) k arg_name pred_body var_env cfg₀'.nextAddr n₀ b
                    (by simpa [storedQt, hpred_case]) hk hreal hmem_new hconsist
      · -- Old location: use IH and transport across the realization-map/memory updates.
        have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l0 = some qt := by
          have hlookup' : res.memEnv'.lookup l0 = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hEq :
              (updateMemEnv res1.memEnv' l storedQt).lookup l0 = res1.memEnv'.lookup l0 :=
            MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq
          have hlookup_old' : res1.memEnv'.lookup l0 = some qt := by
            have htmp := hlookup'
            rw [hEq] at htmp
            exact htmp
          simpa [ctxAfter] using hlookup_old'
        have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hregime_eq] using hkR
        have hloc := hcwr₀1.1 l0 qt k hlookup_old hguard hkR_old
        -- Rebuild locsRegime for the updated θ/memory.
        cases hloc with
        | noPred_ok hnp =>
            exact locsRegime.noPred_ok (l0, qt) hnp
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l0, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
            have hreal' : θ₀'.lookup l0 = some a := by
              -- θ₀' differs from θ₀1 only at l.
              have := RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l0) (addr := cfg₀'.nextAddr) h_eq
              simpa [θ₀', this] using hreal
            have hne : a ≠ cfg₀'.nextAddr := by
              intro hcontra
              have hcontains : cfg₀'.memory.contains cfg₀'.nextAddr := by
                have : cfg₀'.memory.contains a := Memory_contains_of_lookup hmem
                simpa [hcontra] using this
              exact (nextAddr_not_in_memory cfg₀' hwfcf₀1) hcontains
            have hmem' : cf₀.memory.lookup a = some n := by
              have hmem₀' : cf₀.memory = Memory.update cfg₀'.memory cfg₀'.nextAddr n₀ := by
                simpa [Memory.update] using hmem₀
              rw [hmem₀']
              rw [Memory_lookup_update_ne (μ := cfg₀'.memory) (a := a) (a' := cfg₀'.nextAddr) (v := n₀) hne]
              exact hmem
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf₀.memory (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₀.memory (Value.num n)) := by
              constructor
              · intro hbtrue
                have hholds_old := hcons.1 hbtrue
                exact (hqtypPredHolds_mem qt (Value.num n)).1 hholds_old
              · intro hbfalse hholds_new
                have hholds_old := (hqtypPredHolds_mem qt (Value.num n)).2 hholds_new
                exact (hcons.2 hbfalse) hholds_old
            have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq.symm] using hreg
            exact locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
    constructor
    · intro x qt k hlookup hguard hkR
      have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hvars := hcwr₀1.2.1 x qt k (by simpa [ctxAfter] using hlookup) hguard hkR_old
      cases hvars with
      | noPred_ok hnp =>
          exact varsRegime.noPred_ok (x, qt) hnp
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
          have hcons' :
              (b = true → qtypPredHolds predSat qt cf₀.memory v) ∧
              (b = false → ¬ qtypPredHolds predSat qt cf₀.memory v) := by
            constructor
            · intro hbtrue
              have hholds_old := hcons.1 hbtrue
              exact (hqtypPredHolds_mem qt v).1 hholds_old
            · intro hbfalse hholds_new
              have hholds_old := (hqtypPredHolds_mem qt v).2 hholds_new
              exact (hcons.2 hbfalse) hholds_old
          have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
            simpa [hregime_eq.symm] using hreg
          have hvar' : cf₀.varEnv.lookup (x, qt).1 = some v := by
            simpa [hvar₀] using hvar
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregR hvar' hcons'
    · intro x qt v hlookup hlookup_v
      have hlookup_res1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hlookup_v_old : cfg₀'.varEnv.lookup x = some v := by
        simpa [hvar₀] using hlookup_v
      have hcap := hcwr₀1.2.2 x qt v hlookup_res1 hlookup_v_old
      rw [← hregime_eq] at hcap
      exact closureCapturedVarsRegime_transport_μ_θ hqtypPredHolds_mem hθext₀'.1 hcap
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    classical
    let storedQt : QTyp :=
      ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
    have hPredSat_mem :
        ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
      intro k μ μ' v
      exact predSat_mem_noPred_compat hpredlaws θ₁1 k μ μ' v
    have hqtypPredHolds_mem :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v := by
      intro qt v
      constructor
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cf₁.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).1 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cf₁.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).1 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cfg₁'.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).2 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cfg₁'.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).2 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
    constructor
    · intro l0 qt k hlookup hguard hkR
      by_cases h_eq : l0 = l
      · subst l0
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
        have hreal : θ₁'.lookup l = some cfg₁'.nextAddr := by
          simp [θ₁', RealizationMap.update, RealizationMap.lookup]
        have hmem_new : cf₁.memory.lookup cfg₁'.nextAddr = some n₁ := by
          rw [hmem₁]
          simp [Memory.lookup]
        cases hpred_case : storedQt.pred with
        | noPred =>
            have hnone : qtypGuardTag storedQt = none := by
              simp [qtypGuardTag, hpred_case]
            have hne : (none : Option Tag) ≠ some k := by simp
            exact (hne (hnone.symm.trans hguard)).elim
        | guardOnly k0 =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            exact locsRegime.guardOnly_ok (l, storedQt) k (by simpa [storedQt, hpred_case])
        | guardClosure k0 arg_name pred_body var_env =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
            | none =>
                exact (hkR hk).elim
              | some b =>
                  have hval1 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                        res1.qualType cfg₁'.memory θ₁1 (Value.num n₁) := by
                    simpa [hregime_eq] using _hval_consist₁
                  have hpc_false : ctxᵢ.pc = false := by
                    cases hpc : ctxᵢ.pc with
                    | false => exact rfl
                    | true =>
                        simp [storedQt, hpc] at hpred_case
                  have hpred_res1 :
                      res1.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                    simpa [storedQt, hpc_false] using hpred_case
                  have htag_res1 : qtypGuardTag res1.qualType = some k := by
                    simp [qtypGuardTag, hpred_res1]
                  have hpredEq : res1.qualType.pred = storedQt.pred := by
                    simp [storedQt, hpc_false]
                  have hconsist_old :
                      (b = true → qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁)) := by
                    cases hb : b with
                    | true =>
                        have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                          simpa [hb] using hk
                        have hholds_res1 :
                            qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) := by
                          cases hval1 with
                          | noTag hnotag =>
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeTrue k' htag hkR' hholds =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some true = some true := by
                                calc
                                  some true = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some true := hktrue
                              exact hholds
                          | inRegimeFalse k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by simpa using hkR'
                              simp [this] at hktrue
                        have hholds_stored_old :
                            qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁) :=
                          qtypPredHolds_transport_pred (predSat := predSat) (qt := res1.qualType) (qt' := storedQt)
                            (μ := cfg₁'.memory) (v := Value.num n₁) hpredEq hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro _; exact hholds_stored_old
                        · intro hbfalse; cases hbfalse
                    | false =>
                        have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                          simpa [hb] using hk
                        have hnot_res1 :
                            ¬ qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) := by
                          cases hval1 with
                          | noTag hnotag =>
                              intro _
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeFalse k' htag hkR' hnot =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some false = some false := by
                                calc
                                  some false = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some false := hkfalse
                              exact hnot
                          | inRegimeTrue k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by simpa using hkR'
                              simp [this] at hkfalse
                        have hnot_stored_old :
                            ¬ qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁) := by
                          intro hholds_stored
                          have hholds_res1 :
                              qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := storedQt) (qt' := res1.qualType)
                              (μ := cfg₁'.memory) (v := Value.num n₁) (by simp [hpredEq]) hholds_stored
                          exact hnot_res1 hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro hbtrue; cases hbtrue
                        · intro _; exact hnot_stored_old
                  have hconsist :
                      (b = true → qtypPredHolds predSat storedQt cf₁.memory (Value.num n₁)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cf₁.memory (Value.num n₁)) := by
                    constructor
                    · intro hbtrue
                      have hholds_old := hconsist_old.1 hbtrue
                      exact (hqtypPredHolds_mem storedQt (Value.num n₁)).1 hholds_old
                    · intro hbfalse hholds_new
                      have hholds_old := (hqtypPredHolds_mem storedQt (Value.num n₁)).2 hholds_new
                      exact (hconsist_old.2 hbfalse) hholds_old
                  exact
                    locsRegime.withPred_ok (l, storedQt) k arg_name pred_body var_env cfg₁'.nextAddr n₁ b
                      (by simpa [storedQt, hpred_case]) hk hreal hmem_new hconsist
      · have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l0 = some qt := by
          have hlookup' : res.memEnv'.lookup l0 = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hEq :
              (updateMemEnv res1.memEnv' l storedQt).lookup l0 = res1.memEnv'.lookup l0 :=
            MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq
          have hlookup_old' : res1.memEnv'.lookup l0 = some qt := by
            have htmp := hlookup'
            rw [hEq] at htmp
            exact htmp
          simpa [ctxAfter] using hlookup_old'
        have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hregime_eq] using hkR
        have hloc := hcwr₁1.1 l0 qt k hlookup_old hguard hkR_old
        cases hloc with
        | noPred_ok hnp =>
            exact locsRegime.noPred_ok (l0, qt) hnp
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l0, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
            have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq.symm] using hreg
            have hreal' : θ₁'.lookup l0 = some a := by
              have :=
                RealizationMap_lookup_update_ne
                  (θ := θ₁1) (l := l) (l' := l0) (addr := cfg₁'.nextAddr) h_eq
              simpa [θ₁', this] using hreal
            have hne : a ≠ cfg₁'.nextAddr := by
              intro hcontra
              have hcontains : cfg₁'.memory.contains cfg₁'.nextAddr := by
                have : cfg₁'.memory.contains a := Memory_contains_of_lookup hmem
                simpa [hcontra] using this
              exact (nextAddr_not_in_memory cfg₁' hwfcf₁1) hcontains
            have hmem' : cf₁.memory.lookup a = some n := by
              have hmem₁' : cf₁.memory = Memory.update cfg₁'.memory cfg₁'.nextAddr n₁ := by
                simpa [Memory.update] using hmem₁
              rw [hmem₁']
              rw [Memory_lookup_update_ne (μ := cfg₁'.memory) (a := a) (a' := cfg₁'.nextAddr) (v := n₁) hne]
              exact hmem
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf₁.memory (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₁.memory (Value.num n)) := by
              constructor
              · intro hbtrue
                have hholds_old := hcons.1 hbtrue
                exact (hqtypPredHolds_mem qt (Value.num n)).1 hholds_old
              · intro hbfalse hholds_new
                have hholds_old := (hqtypPredHolds_mem qt (Value.num n)).2 hholds_new
                exact (hcons.2 hbfalse) hholds_old
            exact locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
    constructor
    · intro x qt k hlookup hguard hkR
      have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hvars := hcwr₁1.2.1 x qt k (by simpa [ctxAfter] using hlookup) hguard hkR_old
      cases hvars with
      | noPred_ok hnp =>
          exact varsRegime.noPred_ok (x, qt) hnp
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
          have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
            simpa [hregime_eq.symm] using hreg
          have hcons' :
              (b = true → qtypPredHolds predSat qt cf₁.memory v) ∧
              (b = false → ¬ qtypPredHolds predSat qt cf₁.memory v) := by
            constructor
            · intro hbtrue
              have hholds_old := hcons.1 hbtrue
              exact (hqtypPredHolds_mem qt v).1 hholds_old
            · intro hbfalse hholds_new
              have hholds_old := (hqtypPredHolds_mem qt v).2 hholds_new
              exact (hcons.2 hbfalse) hholds_old
          have hvar' : cf₁.varEnv.lookup x = some v := by
            simpa [hvar₁] using hvar
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregR hvar' hcons'
    · intro x qt v hlookup hlookup_v
      have hlookup_res1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hlookup_v_old : cfg₁'.varEnv.lookup x = some v := by
        simpa [hvar₁] using hlookup_v
      have hcap := hcwr₁1.2.2 x qt v hlookup_res1 hlookup_v_old
      rw [← hregime_eq] at hcap
      exact closureCapturedVarsRegime_transport_μ_θ hqtypPredHolds_mem hθext₁'.1 hcap
  let storedQt : QTyp := ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  have hres1_desc :
      ∀ {qt k d}, QTypInQTyp qt res1.qualType →
        qtypGuardDesc? qt = some (k, d) →
        tm1.lookup k = some d := by
    intro qt k d hinq hqd
    exact hresTm1 hinq hqd
  have hstored_desc :
      ∀ {qt k d}, QTypInQTyp qt storedQt →
        qtypGuardDesc? qt = some (k, d) →
        tm1.lookup k = some d := by
    intro qt k d hinq hqd
    have hnotfun : storedQt.etyp.isFunctionType = false := by
      simp [storedQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hEq : qt = storedQt := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
    subst hEq
    have hpc_false : ctxᵢ.pc = false := by
      cases hpc : ctxᵢ.pc with
      | false => exact rfl
      | true =>
          simp [storedQt, qtypGuardDesc?, hpc] at hqd
    have hqd' : qtypGuardDesc? res1.qualType = some (k, d) := by
      simpa [storedQt, qtypGuardDesc?, hpc_false] using hqd
    exact hres1_desc (QTypInQTyp.self res1.qualType) hqd'
  have hEnvTm_res1 : EnvRespectsTagMeaning tm1 ctxᵢ.varEnv res1.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using _hTm1
  have hEnvTm_res : EnvRespectsTagMeaning tm1 ctxᵢ.varEnv res.memEnv' := by
    have hEnvTm_upd : EnvRespectsTagMeaning tm1 ctxᵢ.varEnv (res1.memEnv'.update l storedQt) := by
      exact EnvRespectsTagMeaning_memEnv_ext tm1 ctxᵢ.varEnv res1.memEnv' l storedQt (by simp [storedQt]) hEnvTm_res1 hstored_desc
    simpa [h_mem, storedQt, updateMemEnv] using hEnvTm_upd
  have hresTm : QTypRespectsTagMeaning tm1 res.qualType := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simp [h_etyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm1 res.qualType hnotfun_res hguard) hinq hqd
  have hwfTm_final : wfTagMeaningCtx tm1 (ctxAfter ctxᵢ res) :=
    wfTagMeaningCtx_ctxAfter tm1 ctxᵢ res hEnvTm_res
  have hboundary_newRef : BoundaryTagMeaningPost ctxᵢ res predSat tm tm1 := by
    exact ⟨BoundaryTagMeaningPost.extends_tm hcanon1,
      by simpa [h_ntag] using BoundaryTagMeaningPost.bounded hcanon1,
      hwfTm_final, hresTm, hpredlaws1⟩
  refine ⟨tm1, hboundary_newRef, hpredlaws1, hresTm, ?_⟩
  refine ⟨θ₀', θ₁', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀', hric₁', hreg', hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀'
    exact wfExtendsMap_trans hθext₀1 hθext₀'
  · -- wfExtendsMap θ₁ θ₁'
    exact wfExtendsMap_trans hθext₁1 hθext₁'
  · -- valueHasETyp for run 0
    subst ho₀
    rw [h_etyp]
    have hlookup : θ₀'.lookup l = some cfg₀'.nextAddr := by
      simp [RealizationMap.lookup]
      rw [← ExtTreeMap.get?_eq_getElem?]
      exact ExtTreeMap.getElem?_insert_self
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  · -- valueHasETyp for run 1
    subst ho₁
    rw [h_etyp]
    have hlookup : θ₁'.lookup l = some cfg₁'.nextAddr := by
      simp [RealizationMap.lookup]
      rw [← ExtTreeMap.get?_eq_getElem?]
      exact ExtTreeMap.getElem?_insert_self
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
    exact hwfTm_final
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    exact hwf_result
  · -- TagBoundedCtx (ctxAfter ctxᵢ res)
    exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_pred])
      (.intro (.nonClosure (by intro xp bd rc h; simp [ho₀] at h)
                           (by intro xp bd rc h; simp [ho₀] at h)))
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_pred])
      (.intro (.nonClosure (by intro xp bd rc h; simp [ho₁] at h)
                           (by intro xp bd rc h; simp [ho₁] at h)))
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
