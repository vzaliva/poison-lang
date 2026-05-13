/-
  StepFRVlet.lean - Fault-robustness proof for the vlet case.

  Contains stepFR_vlet, stepFRSingleRunFinalCleanPcTrue_vlet,
  and exclusive vlet-body helpers.
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


private def VletValConsFinish
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (R R' : Regime) (qt qt' : QTyp) (μ μ' : Memory)
    (θ : RealizationMap) (o : Value),
    μ' = μ →
    R' = R →
    qt.etyp = qt'.etyp →
    qt.pred = qt'.pred →
    ValCons R qt μ θ o →
    ValCons R' qt' μ' θ o


private lemma runtimeInstantiatesCtx_vlet_body_start
  (ctx : TypeContext) (result1 : TypeResult) (x : Name)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
  (hric : runtimeInstantiatesCtx (ctxAfter ctx result1) μ ρ θ)
  (hv : valueHasETyp θ v result1.qualType.etyp) :
  let ctx' : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := ctx.varEnv.update x result1.qualType
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime' }
  runtimeInstantiatesCtx ctx' μ (ρ.update x v) θ := by
  intro ctx'
  constructor
  · intro l a hlookup
    simpa [ctxAfter, ctx'] using hric.1 l a hlookup
  · intro y qt hlookup
    by_cases hy : y = x
    · subst y
      have hlookup_x :
          (ctx.varEnv.update x result1.qualType).lookup x = some qt := by
        simpa [ctx'] using hlookup
      have hqt : qt = result1.qualType := by
        have hself :
            (ctx.varEnv.update x result1.qualType).lookup x = some result1.qualType :=
          VarTypeEnv_lookup_update_eq ctx.varEnv x result1.qualType
        exact Option.some.inj (hlookup_x.symm.trans hself)
      refine ⟨v, by simp [VarEnv.update, VarEnv.lookup], ?_⟩
      simpa [hqt] using hv
    · have hlookup_old : ctx.varEnv.lookup y = some qt := by
        have hne :=
          VarTypeEnv_lookup_update_ne ctx.varEnv x y result1.qualType hy
        simpa [ctx', hne] using hlookup
      rcases hric.2 hlookup_old with ⟨v0, hv0, hv0_typed⟩
      refine ⟨v0, ?_, hv0_typed⟩
      have hne := VarEnv_lookup_update_ne ρ x y v hy
      simpa [hne] using hv0


private lemma consistentWithRegimeMasked_vlet_body_start
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx : TypeContext) (result1 : TypeResult) (x : Name)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
  (hcwr : consistentWithRegimeMasked masked predSat (ctxAfter ctx result1).regime (ctxAfter ctx result1) μ ρ θ)
  (hvalc : valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx result1).regime result1.qualType μ θ v) :
  let ctx' : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := ctx.varEnv.update x result1.qualType
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime' }
  consistentWithRegimeMasked masked predSat ctx'.regime ctx' μ (ρ.update x v) θ := by
  intro ctx'
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    have hlookup' : (ctxAfter ctx result1).memEnv.lookup l = some qt := by
      simpa [ctxAfter, ctx'] using hlookup
    have hRdef' : (ctxAfter ctx result1).regime.lookup? k ≠ none := by
      simpa [ctxAfter, ctx'] using hRdef
    simpa [ctxAfter, ctx'] using hcwr.1 l qt k hlookup' hguard hRdef'
  · intro y qt k hlookup hguard hRdef
    by_cases hy : y = x
    · subst y
      have hlookup_x :
          (ctx.varEnv.update x result1.qualType).lookup x = some qt := by
        simpa [ctx'] using hlookup
      have hqt : qt = result1.qualType := by
        have hself :
            (ctx.varEnv.update x result1.qualType).lookup x = some result1.qualType :=
          VarTypeEnv_lookup_update_eq ctx.varEnv x result1.qualType
        exact Option.some.inj (hlookup_x.symm.trans hself)
      subst hqt
      exact
        varsRegime_of_valueConsistentWithRegimeMasked_active
          (masked := masked) (predSat := predSat) (R := result1.regime') (μ := μ)
          (θ := θ) (ρ := ρ.update x v) (x := x) (qt := result1.qualType)
          (v := v) (k := k)
          (by simp [VarEnv.update, VarEnv.lookup])
          hguard
          (by simpa [ctxAfter, ctx'] using hRdef)
          (by simpa [ctxAfter, ctx'] using hvalc)
    · have hlookup_old : ctx.varEnv.lookup y = some qt := by
        have hne :=
          VarTypeEnv_lookup_update_ne ctx.varEnv x y result1.qualType hy
        simpa [ctxAfter, ctx', hne] using hlookup
      have hRdef' : (ctxAfter ctx result1).regime.lookup? k ≠ none := by
        simpa [ctxAfter, ctx'] using hRdef
      have hvars := hcwr.2.1 y qt k hlookup_old hguard hRdef'
      cases hvars with
      | inl hmasked =>
          exact Or.inl hmasked
      | inr hvars =>
          have hne := VarEnv_lookup_update_ne ρ x y v hy
          cases hvars with
          | noPred_ok hnp =>
              exact Or.inr (varsRegime.noPred_ok (y, qt) hnp)
          | guardOnly_ok k' hgo =>
              exact Or.inr (varsRegime.guardOnly_ok (y, qt) k' hgo)
          | withPred_ok k' arg_name pred_body var_env v0 b hpred hreg hlookup_v hcons =>
              have hlookup_v' : (ρ.update x v).lookup y = some v0 := by
                simpa [hne] using hlookup_v
              exact Or.inr <|
                varsRegime.withPred_ok (y, qt) k' arg_name pred_body var_env v0 b hpred hreg hlookup_v' hcons
  · intro y qt v' hlookup hlookup_v
    by_cases hy : y = x
    · subst y
      have hlookup_x :
          (ctx.varEnv.update x result1.qualType).lookup x = some qt := by
        simpa [ctx'] using hlookup
      have hqt : qt = result1.qualType := by
        have hself :
            (ctx.varEnv.update x result1.qualType).lookup x = some result1.qualType :=
          VarTypeEnv_lookup_update_eq ctx.varEnv x result1.qualType
        exact Option.some.inj (hlookup_x.symm.trans hself)
      have hv' : v' = v := by
        have hself : (ρ.update x v).lookup x = some v := by
          simp [VarEnv.update, VarEnv.lookup]
        have hlookup_v' : (ρ.update x v).lookup x = some v' := by
          simpa [VarEnv.update, VarEnv.lookup] using hlookup_v
        exact Option.some.inj (hlookup_v'.symm.trans hself)
      subst hqt hv'
      exact valueConsistentWithRegimeMasked_closureCapturedVarsRegime (by simpa [ctxAfter, ctx'] using hvalc)
    · have hlookup_old : ctx.varEnv.lookup y = some qt := by
        have hne :=
          VarTypeEnv_lookup_update_ne ctx.varEnv x y result1.qualType hy
        simpa [ctxAfter, ctx', hne] using hlookup
      have hlookup_v_old : ρ.lookup y = some v' := by
        have hne := VarEnv_lookup_update_ne ρ x y v hy
        simpa [hne] using hlookup_v
      exact hcwr.2.2 y qt v' hlookup_old hlookup_v_old

private lemma consistentWithRegimeMasked_vlet_finish
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning)
  (ctx ctx' : TypeContext) (result1 result2 result : TypeResult)
  (cfg1 cfg3 cf : Config) (θ1 θ2 : RealizationMap)
  (hpredlaws : PredSatLaws predSat tm)
  (hcf_eq : cf = { cfg3 with varEnv := cfg1.varEnv })
  (h_mem : result.memEnv' = result2.memEnv')
  (h_ret_regime : result.regime' = result2.regime')
  (h_mono_e2 : Regime.monotoneStep (ctxAfter ctx result1).regime (ctxAfter ctx' result2).regime)
  (hcwr1 : consistentWithRegimeMasked masked predSat (ctxAfter ctx result1).regime
    (ctxAfter ctx result1) cfg1.memory cfg1.varEnv θ1)
  (hcwr2 : consistentWithRegimeMasked masked predSat (ctxAfter ctx' result2).regime
    (ctxAfter ctx' result2) cfg3.memory cfg3.varEnv θ2)
  (hθext : wfExtendsMap θ1 θ2) :
  consistentWithRegimeMasked masked predSat (ctxAfter ctx result).regime (ctxAfter ctx result)
    cf.memory cf.varEnv θ2 := by
  have hctxAfter_regime_eq : (ctxAfter ctx result).regime = (ctxAfter ctx' result2).regime := by
    simp [ctxAfter, h_ret_regime]
  have hpred_compat :
      ∀ (qt : QTyp) (v' : Value),
        qtypPredHolds predSat qt cfg1.memory v' ↔ qtypPredHolds predSat qt cf.memory v' := by
    intro qt v'
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ1 cfg1.memory cf.memory qt v'
  have hcwr1_mono :
      consistentWithRegimeMasked masked predSat (ctxAfter ctx' result2).regime
        (ctxAfter ctx result1) cfg1.memory cfg1.varEnv θ1 := by
    exact
      consistentWithRegimeMasked_monotone masked predSat
        (ctxAfter ctx result1).regime (ctxAfter ctx' result2).regime
        (ctxAfter ctx result1) cfg1.memory cfg1.varEnv θ1 h_mono_e2 hcwr1
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hkR
    have hlookup' : (ctxAfter ctx' result2).memEnv.lookup l = some qt := by
      simpa [ctxAfter, h_mem] using hlookup
    have hkR' : (ctxAfter ctx' result2).regime.lookup? k ≠ none := by
      simpa [hctxAfter_regime_eq] using hkR
    have hloc := hcwr2.1 l qt k hlookup' hguard hkR'
    cases hloc with
    | inl hmasked =>
        exact Or.inl hmasked
    | inr hloc =>
        exact Or.inr (by simpa [hctxAfter_regime_eq, hcf_eq] using hloc)
  · intro u qt k hlookup hguard hkR
    have hkR1 : (ctxAfter ctx' result2).regime.lookup? k ≠ none := by
      simpa [hctxAfter_regime_eq] using hkR
    have hlookup1 : (ctxAfter ctx result1).varEnv.lookup u = some qt := by
      simpa [ctxAfter] using hlookup
    have hvar1 := hcwr1_mono.2.1 u qt k hlookup1 hguard hkR1
    cases hvar1 with
    | inl hmasked =>
        exact Or.inl hmasked
    | inr hvar1 =>
        have hvar1' := varsRegime_transport_predHolds hpred_compat hvar1
        exact Or.inr (by simpa [hctxAfter_regime_eq, hcf_eq] using hvar1')
  · intro u qt v_u hlookup hlookup_v
    have hlookup1 : (ctxAfter ctx result1).varEnv.lookup u = some qt := by
      simpa [ctxAfter] using hlookup
    have hlookup_v1 : cfg1.varEnv.lookup u = some v_u := by
      simpa [hcf_eq] using hlookup_v
    have hcap1 := hcwr1_mono.2.2 u qt v_u hlookup1 hlookup_v1
    have hcap1' :
        closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx result).regime qt
          cfg1.memory θ1 v_u := by
      simpa [hctxAfter_regime_eq] using hcap1
    exact closureCapturedVarsRegimeMasked_transport_μ_θ hpred_compat hθext.1 hcap1'

private lemma valueConsistentWithRegimeMasked_vlet_finish
  (masked : Tag → Prop) (predSat : PredSat) :
  VletValConsFinish (fun R qt μ θ o => valueConsistentWithRegimeMasked masked predSat R qt μ θ o) := by
  intro R R' qt qt' μ μ' θ o hμ hR hetyp hpred hval
  subst hμ
  subst R'
  exact
    valueConsistentWithRegimeMasked_transport_pred
      (masked := masked) (predSat := predSat) (R := R)
      (qt := qt) (qt' := qt') (μ := μ') (v := o)
      hpred (hetyp := hetyp) hval


lemma stepFR_vlet_with_expr_proof
  (ctxᵢ : TypeContext) (predSat : PredSat)
    (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
    (tm : TagMeaning) (CanUse : Expr → Prop)
    (CtxReach : TypeContext → Prop)
    (hcan1 : CanUse e1) (hcan2 : CanUse e2)
    (hctxCurrent : CtxReach ctxᵢ)
    (hctxBody :
      ∀ {res1 : TypeResult} {bodyCtx : TypeContext},
        typecheck ctxᵢ e1 fuel' = .ok res1 →
          bodyCtx =
            ({ ctxᵢ with
              memEnv := res1.memEnv'
              varEnv := VarTypeEnv.update ctxᵢ.varEnv vname res1.qualType
              tagEnv := res1.tagEnv'
              nextLoc := res1.nextLoc'
              nextTag := res1.nextTag'
              regime := res1.regime' } : TypeContext) →
        CtxReach ctxᵢ → CtxReach bodyCtx)
    (IH :
      StepFR_IH_WithExprCtx predSat tm (Nat.succ (Nat.succ fuel'))
        CanUse CtxReach (registry := registry))
    (hOp : RegistryOperationalSafe registry)
  (htc : typecheck ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.vlet vname e1 e2) res predSat tm (registry := registry) := by
  -- Parse typecheck result
  have htc' : typecheckVlet ctxᵢ vname e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_vlet_succ] using htc
  obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, h_tag, h_loc, h_ntag,
          h_ret_regime, h_ret_poison, h_ret_pred⟩ :=
    typecheckVlet_structure ctxᵢ vname e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁
    hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm
    hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hctxCurrent hcan1 hwfTm htagBounded res1 htc1'
  -- Use world-free inversion lemma for vlet
  have hstruct₀ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, cfg₀3, ht₀_e1, ht₀_e2, hcf₀_eq, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, cfg₁3, ht₁_e1, ht₁_e2, hcf₁_eq, hpm₁1, hpm₁2⟩
  -- Define intermediate configs with extended varEnv
  let cfg₀2 : Config := { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 }
  let cfg₁2 : Config := { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 }
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed,
    _hTm1, hwf1, _htagBounded1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1,
    hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1,
    hres_agree1⟩
  have hres1_desc :
      ∀ {qt k d}, QTypInQTyp qt res1.qualType →
        qtypGuardDesc? qt = some (k, d) →
        tm1.lookup k = some d := by
    intro qt k d hinq hqd
    exact hresTm1 hinq hqd
  have hwfTm' : wfTagMeaningCtx tm1 ctx' := by
    simp only [hctx']
    exact wfTagMeaningCtx_varEnv_ext tm1 (ctxAfter ctxᵢ res1) vname res1.qualType _hTm1 hres1_desc
  have htagBounded' : TagBoundedCtx ctx' := by
    simp only [hctx']
    exact typecheckExpr_TagBoundedCtx_varEnv_update ctxᵢ e1 fuel' res1 htc1' htagBounded vname
  have hTmBounded' : TagMeaningBounded tm1 ctx'.nextTag := by
    rw [hctx']
    exact BoundaryTagMeaningPost.bounded hcanon1
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' (hctxBody htc1' hctx' hctxCurrent) hcan2 hwfTm' htagBounded' res2 htc2'
  -- Prepare for IH2
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by
    rw [hctx']; simp only [wfTypeContext]
    have hmono1 := typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1'
    exact ⟨hwf1.1,
           varEnvRefLocsBounded_update (varEnvRefLocsBounded_mono hwf.2.1 hmono1)
             (typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e1 fuel' res1 hwf htc1'),
           varEnvClosuresCapturedRefLocsBounded_update (varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono1)
             (typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e1 fuel' res1 hwf htc1')⟩
  have hric₀1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxAfter] using hric₀1
  have hric₁1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxAfter] using hric₁1
  -- hv₀1_typed, hv₁1_typed come from IH1 (StepFR now includes valueHasETyp)
  -- wfValue from wfConfig_preserved (needs terminatesTo)
  have ht₀_e1_w : terminatesTo e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cfg₀1 v₀1 :=
    ht₀_e1
  have ht₁_e1_w : terminatesTo e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cfg₁1 v₁1 :=
    ht₁_e1
  have hv₀1_wf : wfValue cfg₀1.nextAddr v₀1 :=
    (wfConfig_preserved e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm, registry := registry } cfg₀1 v₀1 hOp ht₀_e1_w hwfcfg₀).2
  have hv₁1_wf : wfValue cfg₁1.nextAddr v₁1 :=
    (wfConfig_preserved e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm, registry := registry } cfg₁1 v₁1 hOp ht₁_e1_w hwfcfg₁).2
  have hreg_ctx' : regimeConsistentWithCtx ctx' := by
    -- ctx'.regime = res1.regime', need to derive from htagR1 and regime_monotone
    unfold regimeConsistentWithCtx at htagR1 ⊢
    have h_tagEnv_eq : ctx'.tagEnv = (ctxAfter ctxᵢ res1).tagEnv := by simp [hctx', ctxAfter]
    have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
    rw [h_tagEnv_eq, h_regime_eq]
    exact htagR1
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
    constructor
    · -- locs: unchanged memories, and ctx'.memEnv matches ctxAfter ctxᵢ res1
      intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
        simpa [hctx', ctxAfter] using hclean
      have hagree_loc := hagree_clean1.1 l qt hlookup' hclean'
      simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_loc
    · -- vars: old variables come from hagree_clean1; new binding uses result agreement
      intro x qt hlookup hclean
      by_cases hx : x = vname
      · subst x
        have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have : some qt = some res1.qualType := by
            calc
              some qt = (ctxᵢ.varEnv.update vname res1.qualType).lookup vname := by
                symm; exact hlookup'
              _ = some res1.qualType := by
                exact h
          exact Option.some.inj this
        subst hqt
        have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := by
          simpa [hctx', ctxAfter] using hclean
        have hagree_val :=
          hres_agree1 hclean'
        have hlookup_v₀ : cfg₀2.varEnv.lookup vname = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        have hlookup_v₁ : cfg₁2.varEnv.lookup vname = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        refine agreeVarUnder.agree_values vname res1.qualType v₀1 v₁1 hlookup_v₀ hlookup_v₁ ?_
        simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_val
      · -- x ≠ vname: transport agreeVarUnder through varEnv.update
        have hlookup_update : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_update
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx
        have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
          simpa [hctx', ctxAfter] using hclean
        have hagree_var := hagree_clean1.2 x qt hlookup_ctxAfter hclean'
        cases hagree_var with
        | agree_values x qt v₀ v₁ h₀ h₁ hagree_val =>
            have h₀' : cfg₀2.varEnv.lookup x = some v₀ := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using h₀
            have h₁' : cfg₁2.varEnv.lookup x = some v₁ := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using h₁
            exact
              agreeVarUnder.agree_values x qt v₀ v₁ h₀' h₁'
                (by simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_val)
        | both_none x qt h₀ h₁ =>
            have h₀' : cfg₀2.varEnv.lookup x = none := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using h₀
            have h₁' : cfg₁2.varEnv.lookup x = none := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using h₁
            exact agreeVarUnder.both_none x qt h₀' h₁'
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₀2_eq : cfg₀2 = { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 } := rfl
  have hcfg₁2_eq : cfg₁2 = { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 } := rfl
  -- Convert ht₁_e2 to have matching pureMode
  have ht₁_e2' : terminatesTo e2 { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } cfg₁3 o₁ := by
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
  have h_mono_vlet := regime_monotone ctxᵢ e1 fuel' res1 htc1'
  -- Transfer consistentWithRegime from IH1 result to ctx'
  -- IH1 gives consistentWithRegime predSat (ctxAfter ctxᵢ res1).regime (ctxAfter ctxᵢ res1) ...
  -- Since ctx' = ctxAfter ctxᵢ res1 (structurally), these match
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
    -- cfg₀2 extends cfg₀1 with updated varEnv
    -- ctx' has same memEnv as (ctxAfter ctxᵢ res1) but extended varEnv
    constructor
    · -- locs: memEnv and memory are the same
      intro l qt k hlookup hguard hregime_k
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hctx', ctxAfter] using hregime_k
      have hlocs := hcwr₀1.1 l qt k hlookup' hguard hregime_k'
      cases hlocs with
      | noPred_ok hpred =>
          exact locsRegime.noPred_ok (l, qt) hpred
      | guardOnly_ok k' hgo =>
          exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env a n b hclos hregime' hreal hmem' hconsist =>
          have hmem'' : cfg₀2.memory.lookup a = some n := by
            simpa [cfg₀2] using hmem'
          have hregime'' : ctx'.regime.lookup? k' = some b := by
            simpa [hctx', ctxAfter] using hregime'
          exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregime'' hreal hmem'' hconsist
    constructor
    · -- vars: old variables transfer, new variable from IH1 result
      intro x qt k hlookup hguard hregime_k
      by_cases hx : x = vname
      · -- Case: x = vname (new binding)
        subst hx
        have hlookup_res1 : (ctxᵢ.varEnv.update x res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv x res1.qualType
          have : some qt = some res1.qualType := by
            calc
              some qt = (ctxᵢ.varEnv.update x res1.qualType).lookup x := by
                symm; exact hlookup_res1
              _ = some res1.qualType := by
                exact h
          exact Option.some.inj this
        subst hqt
        have hlookup_v : cfg₀2.varEnv.lookup x = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        have hval_consist :
            valueConsistentWithRegime predSat ctx'.regime res1.qualType cfg₀2.memory θ₀1 v₀1 := by
          simpa [hctx', ctxAfter, cfg₀2] using _hval_consist₀1
        cases hpred_case : res1.qualType.pred with
        | noPred =>
            have hguard' : qtypGuardTag res1.qualType = none := by
              simp [qtypGuardTag, hpred_case]
            rw [hguard'] at hguard
            cases hguard
        | guardOnly k' =>
            exact varsRegime.guardOnly_ok (x, res1.qualType) k' hpred_case
        | guardClosure k' arg_name pred_body var_env =>
            have htag_k' : qtypGuardTag res1.qualType = some k' := by
              simp [qtypGuardTag, hpred_case]
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                  _ = some k := hguard
              exact Option.some.inj this
            have hkR : ctx'.regime.lookup? k' ≠ none := by
              simpa [hk] using hregime_k
            cases hval_consist with
            | noTag hnone =>
                have : some k' = (none : Option Tag) := by
                  calc
                    some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                    _ = none := hnone
                cases this
            | guardOnly_ok k0 hgo =>
                have : Predicate.guardClosure k' arg_name pred_body var_env = Predicate.guardOnly k0 := by
                  calc
                    Predicate.guardClosure k' arg_name pred_body var_env = res1.qualType.pred := by
                      symm; exact hpred_case
                    _ = Predicate.guardOnly k0 := hgo
                cases this
            | notInRegime k0 htag0 hnone =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have : False := hkR (by simpa [hk0] using hnone)
                cases this
            | inRegimeTrue k0 htag0 hRtrue hholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRtrue' : ctx'.regime.lookup? k' = some true := by
                  simpa [hk0] using hRtrue
                refine
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₀1 true
                    hpred_case hRtrue' hlookup_v ?_
                constructor
                · intro _; exact hholds
                · intro hb; cases hb
            | inRegimeFalse k0 htag0 hRfalse hnholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRfalse' : ctx'.regime.lookup? k' = some false := by
                  simpa [hk0] using hRfalse
                refine
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₀1 false
                    hpred_case hRfalse' hlookup_v ?_
                constructor
                · intro hb; cases hb
                · intro _; exact hnholds
      · -- Case: x ≠ vname (old variable)
        have hlookup_old : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_old' : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_old
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simp [ctxAfter]; exact hlookup_old'
        have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hctx', ctxAfter] using hregime_k
        have hvars := hcwr₀1.2.1 x qt k hlookup_ctxAfter hguard hregime_k'
        cases hvars with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hregime' hlookup_v hconsist =>
            have hlookup_v' : cfg₀2.varEnv.lookup x = some v := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hlookup_v
            have hregime'' : ctx'.regime.lookup? k' = some b := by
              simpa [hctx', ctxAfter] using hregime'
            have hconsist' : (b = true → qtypPredHolds predSat (x, qt).snd cfg₀2.memory v) ∧
                           (b = false → ¬qtypPredHolds predSat (x, qt).snd cfg₀2.memory v) := by
              have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
              simpa [h_mem_eq] using hconsist
            exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregime'' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: the newly bound variable from e1
        rw [hx] at hlookup hlookup_v
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
            simpa [hctx'] using hlookup
          exact Option.some.inj (hlookup'.symm.trans h)
        have hv_eq : v = v₀1 := by
          have h : cfg₀2.varEnv.lookup vname = some v₀1 := by
            simp [cfg₀2, VarEnv.update, VarEnv.lookup]
          exact Option.some.inj (hlookup_v.symm.trans h)
        subst hqt_eq hv_eq
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
        exact valueConsistentWithRegime_closureCapturedVarsRegime
          (by simpa [h_regime_eq, h_mem_eq] using _hval_consist₀1)
      · -- x ≠ vname: old variable unchanged
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
            have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
              simpa [hctx'] using hlookup
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using this
          simpa [ctxAfter] using hlookup_old
        have hlookup_v_old : cfg₀1.varEnv.lookup x = some v := by
          simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hlookup_v
        have hcap := hcwr₀1.2.2 x qt v hlookup_ctxAfter hlookup_v_old
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
        rwa [h_regime_eq, h_mem_eq]
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    -- cfg₁2 extends cfg₁1 with updated varEnv
    constructor
    · -- locs: memEnv and memory are the same
      intro l qt k hlookup hguard hregime_k
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hctx', ctxAfter] using hregime_k
      have hlocs := hcwr₁1.1 l qt k hlookup' hguard hregime_k'
      cases hlocs with
      | noPred_ok hpred =>
          exact locsRegime.noPred_ok (l, qt) hpred
      | guardOnly_ok k' hgo =>
          exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env a n b hclos hregime' hreal hmem' hconsist =>
          have hmem'' : cfg₁2.memory.lookup a = some n := by
            simpa [cfg₁2] using hmem'
          have hregime'' : ctx'.regime.lookup? k' = some b := by
            simpa [hctx', ctxAfter] using hregime'
          have hconsist' : (b = true → qtypPredHolds predSat (l, qt).snd cfg₁2.memory (Value.num n)) ∧
                         (b = false → ¬qtypPredHolds predSat (l, qt).snd cfg₁2.memory (Value.num n)) := by
            have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
            simpa [h_mem_eq] using hconsist
          exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregime'' hreal hmem'' hconsist'
    constructor
    · -- vars: old variables transfer, new variable from IH1 result
      intro x qt k hlookup hguard hregime_k
      by_cases hx : x = vname
      · -- Case: x = vname (new binding)
        subst hx
        -- After subst, vname is replaced by x everywhere
        have hlookup_res1 : (ctxᵢ.varEnv.update x res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv x res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update x res1.qualType).lookup x := by symm; exact hlookup_res1
                 _ = some res1.qualType := h
          exact Option.some.inj this
        subst hqt_eq
        have hlookup_v : cfg₁2.varEnv.lookup x = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        cases hpred_case : res1.qualType.pred with
        | noPred =>
            have hguard' : qtypGuardTag res1.qualType = none := by simp [qtypGuardTag, hpred_case]
            rw [hguard'] at hguard; cases hguard
        | guardOnly k' =>
            exact varsRegime.guardOnly_ok (x, res1.qualType) k' hpred_case
        | guardClosure k' arg_name pred_body var_env =>
            -- TODO(vlet/valueConsistentWithRegime): symmetric to the cfg₀2 case above.
            -- We need return-value regime-consistency for `v₁1` to discharge the new-binding
            -- `varsRegime` obligation when the guard tag is in the regime domain.
            have hval_consist :
                valueConsistentWithRegime predSat ctx'.regime res1.qualType cfg₁2.memory θ₁1 v₁1 := by
              simpa [hctx', ctxAfter, cfg₁2] using _hval_consist₁1
            have htag_k' : qtypGuardTag res1.qualType = some k' := by
              simp [qtypGuardTag, hpred_case]
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                  _ = some k := hguard
              exact Option.some.inj this
            have hkR : ctx'.regime.lookup? k' ≠ none := by
              simpa [hk] using hregime_k
            cases hval_consist with
            | noTag hnone =>
                have : some k' = (none : Option Tag) := by
                  calc
                    some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                    _ = none := hnone
                cases this
            | guardOnly_ok k0 hgo =>
                have : Predicate.guardClosure k' arg_name pred_body var_env = Predicate.guardOnly k0 := by
                  calc
                    Predicate.guardClosure k' arg_name pred_body var_env = res1.qualType.pred := by
                      symm; exact hpred_case
                    _ = Predicate.guardOnly k0 := by
                      exact hgo
                cases this
            | notInRegime k0 htag0 hnone =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have : False := hkR (by simpa [hk0] using hnone)
                cases this
            | inRegimeTrue k0 htag0 hRtrue hholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRtrue' : ctx'.regime.lookup? k' = some true := by
                  simpa [hk0] using hRtrue
                exact
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₁1 true
                    hpred_case hRtrue' hlookup_v
                    ⟨(by intro _; exact hholds), (by intro hb; cases hb)⟩
            | inRegimeFalse k0 htag0 hRfalse hnholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRfalse' : ctx'.regime.lookup? k' = some false := by
                  simpa [hk0] using hRfalse
                exact
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₁1 false
                    hpred_case hRfalse' hlookup_v
                    ⟨(by intro hb; cases hb), (by intro _; exact hnholds)⟩
      · -- Case: x ≠ vname (old variable)
        have hlookup_old : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_old' : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_old
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simp [ctxAfter]; exact hlookup_old'
        have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hctx', ctxAfter] using hregime_k
        have hvars := hcwr₁1.2.1 x qt k hlookup_ctxAfter hguard hregime_k'
        cases hvars with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hregime' hlookup_v hconsist =>
            have hlookup_v' : cfg₁2.varEnv.lookup x = some v := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hlookup_v
            have hregime'' : ctx'.regime.lookup? k' = some b := by
              simpa [hctx', ctxAfter] using hregime'
            have hconsist' : (b = true → qtypPredHolds predSat (x, qt).snd cfg₁2.memory v) ∧
                           (b = false → ¬qtypPredHolds predSat (x, qt).snd cfg₁2.memory v) := by
              have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
              simpa [h_mem_eq] using hconsist
            exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregime'' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: the newly bound variable from e1
        rw [hx] at hlookup hlookup_v
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
            simpa [hctx'] using hlookup
          exact Option.some.inj (hlookup'.symm.trans h)
        have hv_eq : v = v₁1 := by
          have h : cfg₁2.varEnv.lookup vname = some v₁1 := by
            simp [cfg₁2, VarEnv.update, VarEnv.lookup]
          exact Option.some.inj (hlookup_v.symm.trans h)
        subst hqt_eq hv_eq
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
        exact valueConsistentWithRegime_closureCapturedVarsRegime
          (by simpa [h_regime_eq, h_mem_eq] using _hval_consist₁1)
      · -- x ≠ vname: old variable unchanged
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
            have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
              simpa [hctx'] using hlookup
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using this
          simpa [ctxAfter] using hlookup_old
        have hlookup_v_old : cfg₁1.varEnv.lookup x = some v := by
          simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hlookup_v
        have hcap := hcwr₁1.2.2 x qt v hlookup_ctxAfter hlookup_v_old
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
        rwa [h_regime_eq, h_mem_eq]
  -- Thread extern registry: cfg₀1 and cfg₁1 inherit default registry from
  -- initial config (via beval_preserves_registry). cfg₀2/cfg₁2 are updates of
  -- these so their registry field is also the default.
  have hreg_cfg₀1 : cfg₀1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₀_e1
  have hreg_cfg₁1 : cfg₁1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht₁_e1
  have ht₀_e2_ih : terminatesTo e2
      { memory := cfg₀2.memory, varEnv := cfg₀2.varEnv, nextAddr := cfg₀2.nextAddr, pureMode := cfg₀2.pureMode, registry := registry }
      cfg₀3 o₀ := by
    have h : cfg₀1.registry = registry := hreg_cfg₀1
    have tmp := ht₀_e2
    rw [h] at tmp
    show terminatesTo e2 { memory := cfg₀1.memory, varEnv := cfg₀1.varEnv.update vname v₀1, nextAddr := cfg₀1.nextAddr, pureMode := cfg₀1.pureMode, registry := registry } cfg₀3 o₀
    exact tmp
  have ht₁_e2_ih : terminatesTo e2
      { memory := cfg₁2.memory, varEnv := cfg₁2.varEnv, nextAddr := cfg₁2.nextAddr, pureMode := cfg₀2.pureMode, registry := registry }
      cfg₁3 o₁ := by
    have h : cfg₁1.registry = registry := hreg_cfg₁1
    have tmp := ht₁_e2'
    rw [h] at tmp
    exact tmp
  have hstep_e2 :=
    hIH2 hpredlaws1 hExtTyping hwfTm' hTmBounded' cfg₀2.memory cfg₁2.memory
      cfg₀2.varEnv cfg₁2.varEnv θ₀1 θ₁1
      cfg₀3 cfg₁3 o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' htagBounded' hric₀1' hric₁1' hreg_ctx' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
      ht₀_e2_ih ht₁_e2_ih
  rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2,
    _hTm2, hwf2, _htagBounded2, hwfcf₀3, hwfcf₁3, hric₀2, hric₁2, htagR2,
    hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2,
    hres_agree2⟩
  -- Combine map extensions
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  -- VarEnv preservation through e2
  have ht₀_e2_w : terminatesTo e2 cfg₀2 cfg₀3 o₀ := ht₀_e2
  have ht₁_e2_w : terminatesTo e2 cfg₁2 cfg₁3 o₁ := ht₁_e2
  have hvar_pres₀ : cfg₀3.varEnv = cfg₀2.varEnv := by
    symm
    rcases ht₀_e2_w with ⟨fuel₀', verbose₀', heval₀⟩
    exact beval_preserves_varEnv e2 fuel₀' verbose₀' cfg₀2 cfg₀3 o₀ heval₀
  have hvar_pres₁ : cfg₁3.varEnv = cfg₁2.varEnv := by
    symm
    rcases ht₁_e2_w with ⟨fuel₁', verbose₁', heval₁⟩
    exact beval_preserves_varEnv e2 fuel₁' verbose₁' cfg₁2 cfg₁3 o₁ heval₁
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
  -- With new StepFR using output regime, we need (ctxAfter ctxᵢ res).regime
  have hreg'' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    -- IH2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) (ctxAfter ctx' res2).regime
    -- The relevant fields match by structure lemma
    have h_tagEnv_eq : (ctxAfter ctxᵢ res).tagEnv = (ctxAfter ctx' res2).tagEnv := by simp [ctxAfter, h_tag]
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by simp [ctxAfter, h_ret_regime]
    have h_nextTag_eq : (ctxAfter ctxᵢ res).nextTag = (ctxAfter ctx' res2).nextTag := by simp [ctxAfter, h_ntag]
    unfold regimeConsistentWithCtx at htagR2 ⊢
    rw [h_tagEnv_eq, h_regime_eq]; exact htagR2
  -- Final agreeOnClean (using output regime)
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    -- IH2 gives agreeOnClean for extended context, but TypeResult doesn't include varEnv'
    -- So (ctxAfter ctxᵢ res).varEnv = ctxᵢ.varEnv (original, NOT extended)
    -- And (ctxAfter ctx' res2).varEnv = ctx'.varEnv (extended with vname)
    -- Runtime: cf₀.varEnv = cfg₀1.varEnv (restored), not the extended cfg₀2.varEnv
    have h_mem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
    have h_mem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
    have h_var₀_eq : cf₀.varEnv = cfg₀1.varEnv := by simp [hcf₀_eq]
    have h_var₁_eq : cf₁.varEnv = cfg₁1.varEnv := by simp [hcf₁_eq]
    have h_mem_eq : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctx' res2).memEnv := by simp [ctxAfter, h_mem]
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by simp [ctxAfter, h_ret_regime]
    constructor
    · -- locs: memEnv matches by structure lemma
      intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by simpa [h_mem_eq] using hlookup
      have hclean' : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by simpa [h_regime_eq] using hclean
      have hagree_loc := hagree_clean2.1 l qt hlookup' hclean'
      have hagree_loc' : agreeLocUnder predSat (ctxAfter ctxᵢ res).regime cfg₀3.memory cfg₁3.memory θ₀2 θ₁2 (l, qt) := by
        simpa [h_regime_eq] using hagree_loc
      simpa [h_mem₀_eq, h_mem₁_eq] using hagree_loc'
    · -- vars: Complex - varEnv is restored, needs careful reasoning about variable shadowing
      intro x qt hlookup hclean
      -- Helper: clean-under is preserved backwards along a regime monotone step (entries can only be dropped).
      have cleanUnder_of_monotone {R R' : Regime} {qt : QTyp} :
          Regime.monotoneStep R R' → qtypCleanUnder R' qt → qtypCleanUnder R qt := by
        intro h_mono h_clean
        cases h_clean with
        | clean hpoison =>
            exact qtypCleanUnder.clean hpoison
        | guard k htag hkR' hnotfun =>
            -- Since R'.lookup? k = some true, monotonicity implies R.lookup? k = some true as well.
            have hRdef : R.lookup? k ≠ none := h_mono.2 k (by simp [hkR'])
            cases hkR : R.lookup? k with
            | none => exact (hRdef hkR).elim
            | some b =>
                have h_cases := h_mono.1 k b hkR
                cases h_cases with
                | inl hkR'_preserved =>
                    have hb : b = true := by
                      have : some b = some true := hkR'_preserved.symm.trans hkR'
                      exact Option.some.inj this
                    subst hb
                    exact qtypCleanUnder.guard k htag hkR hnotfun
                | inr hkR'_none =>
                    -- Contradiction: hkR' says R'.lookup? k = some true.
                    simp [hkR'_none] at hkR'
      -- Helper: transfer agreeValueUnder across a monotone regime step, assuming the type is clean under the target.
      -- We prove this by induction on agreement; the recursor provides the needed IH for captured environments.
      have agreeValueUnder_clean_monotoneRegime
          {R R' : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
            Regime.monotoneStep R R' →
              qtypCleanUnder R' qt →
                agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
                  agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
          intro h_mono hclean hagree
          exact
            agreeValueUnder_clean_transport_by_cleanBack
              (fun qt hclean' => cleanUnder_of_monotone (R := R) (R' := R') h_mono hclean')
              (fun h => memberVarsRegimeEvidence_monotone h_mono h)
              (fun h => memberCvcrEvidence_monotone h_mono h)
              (fun h => memberVarsRegimeEvidence_monotone h_mono h)
              (fun h => memberCvcrEvidence_monotone h_mono h)
              hclean hagree
      -- Establish the regime monotone step from after-e1 to after-e2 (typechecking can only drop regime entries).
      have h_mono_e2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
        have h := regime_monotone ctx' e2 fuel' res2 htc2'
        have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
        simpa [hR1] using h
      -- Split on shadowing: the only variable affected by the let-binding is `vname`.
      by_cases hx : x = vname
      · subst x
        -- Use IH1 agreement for the original variable binding (since the runtime varEnv is restored).
        have hlookup1 : (ctxAfter ctxᵢ res1).varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have hclean_final : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          -- Final regime is the e2 output regime.
          simpa [h_regime_eq] using hclean
        have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt :=
          cleanUnder_of_monotone h_mono_e2 hclean_final
        have hagree_var1 := hagree_clean1.2 vname qt hlookup1 hclean1
        cases hagree_var1 with
        | both_none _ _ hnone₀ hnone₁ =>
            refine agreeVarUnder.both_none vname qt ?_ ?_
            · simpa [h_var₀_eq] using hnone₀
            · simpa [h_var₁_eq] using hnone₁
        | agree_values _ _ v₀ v₁ hv₀ hv₁ hagree_val =>
            -- Transfer value agreement to the final regime, extended realisation maps, and final memories.
            have hagree_val' : agreeValueUnder predSat (ctxAfter ctx' res2).regime cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
              agreeValueUnder_clean_monotoneRegime h_mono_e2 hclean_final hagree_val
            have hqtypPredHolds_mem_vlet₀ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' cfg₀1.memory v' ↔
                    qtypPredHolds predSat qt' cf₀.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₀1) (μ := cfg₀1.memory) (μ' := cf₀.memory)
            have hqtypPredHolds_mem_vlet₁ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' cfg₁1.memory v' ↔
                    qtypPredHolds predSat qt' cf₁.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₁1) (μ := cfg₁1.memory) (μ' := cf₁.memory)
            have hagree_val'' :
                agreeValueUnder predSat (ctxAfter ctx' res2).regime cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ :=
              agreeValueUnder_clean_extends_transport_mem
                hqtypPredHolds_mem_vlet₀ hqtypPredHolds_mem_vlet₁
                hclean_final hθext₀2.1 hθext₁2.1 hagree_val'
            refine agreeVarUnder.agree_values vname qt v₀ v₁ ?_ ?_ ?_
            · simpa [h_var₀_eq] using hv₀
            · simpa [h_var₁_eq] using hv₁
            · simpa [h_mem₀_eq, h_mem₁_eq, h_regime_eq] using hagree_val''
      · -- x ≠ vname: use IH2 agreement in the extended context, then transport lookups back to the restored varEnvs.
        have hlookup_ctx' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          -- ctx'.varEnv is ctxᵢ.varEnv updated at vname; lookup at x is unchanged.
          have hlookup_ctx : ctxᵢ.varEnv.lookup x = some qt := by
            simpa [ctxAfter] using hlookup
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctx
          simpa [ctxAfter, hctx'] using this
        have hclean_ctx' : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          simpa [h_regime_eq] using hclean
        have hagree_var := hagree_clean2.2 x qt hlookup_ctx' hclean_ctx'
        cases hagree_var with
        | both_none _ _ hnone₀ hnone₁ =>
            refine agreeVarUnder.both_none x qt ?_ ?_
            · -- Transport the `none` lookup across the let-bound update and varEnv restoration.
              have : cfg₀3.varEnv.lookup x = none := hnone₀
              have : cfg₀1.varEnv.lookup x = none := by
                -- cfg₀3.varEnv = cfg₀2.varEnv = cfg₀1.varEnv.update vname v₀1
                have hx' : cfg₀2.varEnv.lookup x = none := by
                  simpa [hvar_pres₀] using this
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hx'
              simpa [h_var₀_eq] using this
            · have : cfg₁3.varEnv.lookup x = none := hnone₁
              have : cfg₁1.varEnv.lookup x = none := by
                have hx' : cfg₁2.varEnv.lookup x = none := by
                  simpa [hvar_pres₁] using this
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hx'
              simpa [h_var₁_eq] using this
        | agree_values _ _ v₀ v₁ hv₀ hv₁ hagree_val =>
            refine agreeVarUnder.agree_values x qt v₀ v₁ ?_ ?_ ?_
            · -- lookup in restored env equals lookup in extended env for x ≠ vname
              have : cfg₀3.varEnv.lookup x = some v₀ := hv₀
              have : cfg₀1.varEnv.lookup x = some v₀ := by
                have hx' : cfg₀2.varEnv.lookup x = some v₀ := by
                  simpa [hvar_pres₀] using this
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hx'
              simpa [h_var₀_eq] using this
            · have : cfg₁3.varEnv.lookup x = some v₁ := hv₁
              have : cfg₁1.varEnv.lookup x = some v₁ := by
                have hx' : cfg₁2.varEnv.lookup x = some v₁ := by
                  simpa [hvar_pres₁] using this
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hx'
              simpa [h_var₁_eq] using this
            · -- agreeValueUnder is insensitive to varEnvs; just rewrite memories/regime to match the goal.
              simpa [h_mem₀_eq, h_mem₁_eq, h_regime_eq] using hagree_val
  -- Final wfConfig
  have hwfcf₀_final : wfConfig cf₀ :=
    (wfConfig_preserved (Expr.vlet vname e1 e2) _ cf₀ o₀ hOp ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ :=
    (wfConfig_preserved (Expr.vlet vname e1 e2) _ cf₁ o₁ hOp ht₁ hwfcfg₁).1
  -- Need consistentWithRegime for both runs
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    have h_mem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
    have h_var₀_eq : cf₀.varEnv = cfg₀1.varEnv := by simp [hcf₀_eq]
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    constructor
    · intro l qt k hlookup hguard hkR
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        simpa [ctxAfter, h_mem] using hlookup
      have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
        simpa [hR_eq] using hkR
      have hloc := hcwr₀2.1 l qt k hlookup' hguard hkR'
      simpa [hR_eq, h_mem₀_eq] using hloc
    constructor
    · intro x qt k hlookup hguard hkR
      by_cases hx : x = vname
      · subst x
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        cases hpred : qt.pred with
        | noPred =>
            exact varsRegime.noPred_ok (vname, qt) (by simp [qtypGuardTag, hpred])
        | guardOnly k0 =>
            exact varsRegime.guardOnly_ok (vname, qt) k0 hpred
        | guardClosure k0 arg_name pred_body var_env =>
            -- Ruled out by the vlet shadowing restriction in the typechecker.
            exfalso
            have hk0 : k0 = k := by
              have : qtypGuardTag qt = some k0 := by simp [qtypGuardTag, hpred]
              exact Option.some.inj (this.symm.trans hguard)
            have hkR_e2 : (ctxAfter ctx' res2).regime.lookup? k0 ≠ none := by
              simpa [hk0, hR_eq] using hkR
            have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
              simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
            have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
              have h := regime_monotone ctx' e2 fuel' res2 htc2'
              have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
              simpa [hR1, ctxAfter] using h
            have hkR_after1 : (ctxAfter ctxᵢ res1).regime.lookup? k0 ≠ none :=
              h_mono2.2 k0 hkR_e2
            have hkR_ctxᵢ : ctxᵢ.regime.lookup? k0 ≠ none :=
              h_mono1.2 k0 hkR_after1
            have hk_isSome : (ctxᵢ.regime.lookup? k0).isSome = true := by
              cases hk : ctxᵢ.regime.lookup? k0 with
              | none => exact (hkR_ctxᵢ hk).elim
              | some b => simp
            have htc_bad := htc'
            simp [typecheckVlet, hlookup_ctxᵢ, hpred, hk_isSome] at htc_bad
            cases htc_bad
      · have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
          simpa [hR_eq] using hkR
        have hvars2 := hcwr₀2.2.1 x qt k hlookup_ctxAfter' hguard hkR'
        cases hvars2 with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hlookup_v hconsist =>
            have hlookup_v' : cf₀.varEnv.lookup x = some v := by
              have : cfg₀3.varEnv.lookup x = some v := hlookup_v
              have : cfg₀2.varEnv.lookup x = some v := by
                simpa [hvar_pres₀] using this
              have : cfg₀1.varEnv.lookup x = some v := by
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using this
              simpa [h_var₀_eq] using this
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hR_eq] using hreg
            have hconsist' :
                (b = true → qtypPredHolds predSat qt cf₀.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₀.memory v) := by
              simpa [h_mem₀_eq] using hconsist
            exact
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: use initial hcwr₀; transport regime via monotonicity, memory via predSat independence
        rw [hx] at hlookup hlookup_v
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have h_varEnv_pres₀ : ρ₀ = cfg₀1.varEnv := by
          rcases ht₀_e1_w with ⟨fuel_w, verbose_w, h_beval_w⟩
          exact beval_preserves_varEnv e1 fuel_w verbose_w _ _ _ h_beval_w
        have hlookup_v_ρ₀ : ρ₀.lookup vname = some v := by
          rw [h_varEnv_pres₀]; simpa [h_var₀_eq] using hlookup_v
        have hcap₀ := hcwr₀.2.2 vname qt v hlookup_ctxᵢ hlookup_v_ρ₀
        have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
          simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
        have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
          have h := regime_monotone ctx' e2 fuel' res2 htc2'
          have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
          simpa [hR1, ctxAfter] using h
        have hcap₂ := closureCapturedVarsRegime_monotone h_mono2
          (closureCapturedVarsRegime_monotone h_mono1 hcap₀)
        rw [← hR_eq] at hcap₂
        have hPredSat_mem₀ : ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
          predSat_mem_noPred_compat hpredlaws θ₀
        exact closureCapturedVarsRegime_transport_μ_θ (fun qt' v' =>
          ⟨fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').1 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').1 hs),
           fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').2 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').2 hs)⟩)
          hθext₀.1 hcap₂
      · -- x ≠ vname: use hcwr₀2 from IH2 and transport regimes/memory
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hlookup_v_cfg₀3 : cfg₀3.varEnv.lookup x = some v := by
          have hcf₀_v : cf₀.varEnv.lookup x = some v := hlookup_v
          have : cfg₀1.varEnv.lookup x = some v := by simpa [h_var₀_eq] using hcf₀_v
          have h2 : cfg₀2.varEnv.lookup x = some v := by
            simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using this
          rw [hvar_pres₀]; exact h2
        have hcap := hcwr₀2.2.2 x qt v hlookup_ctxAfter' hlookup_v_cfg₀3
        rw [← hR_eq] at hcap
        rw [← h_mem₀_eq] at hcap
        exact hcap
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    have h_mem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
    have h_var₁_eq : cf₁.varEnv = cfg₁1.varEnv := by simp [hcf₁_eq]
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    constructor
    · intro l qt k hlookup hguard hkR
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        simpa [ctxAfter, h_mem] using hlookup
      have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
        simpa [hR_eq] using hkR
      have hloc := hcwr₁2.1 l qt k hlookup' hguard hkR'
      simpa [hR_eq, h_mem₁_eq] using hloc
    constructor
    · intro x qt k hlookup hguard hkR
      by_cases hx : x = vname
      · subst x
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        cases hpred : qt.pred with
        | noPred =>
            exact varsRegime.noPred_ok (vname, qt) (by simp [qtypGuardTag, hpred])
        | guardOnly k0 =>
            exact varsRegime.guardOnly_ok (vname, qt) k0 hpred
        | guardClosure k0 arg_name pred_body var_env =>
            exfalso
            have hk0 : k0 = k := by
              have : qtypGuardTag qt = some k0 := by simp [qtypGuardTag, hpred]
              exact Option.some.inj (this.symm.trans hguard)
            have hkR_e2 : (ctxAfter ctx' res2).regime.lookup? k0 ≠ none := by
              simpa [hk0, hR_eq] using hkR
            have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
              simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
            have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
              have h := regime_monotone ctx' e2 fuel' res2 htc2'
              have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
              simpa [hR1, ctxAfter] using h
            have hkR_after1 : (ctxAfter ctxᵢ res1).regime.lookup? k0 ≠ none :=
              h_mono2.2 k0 hkR_e2
            have hkR_ctxᵢ : ctxᵢ.regime.lookup? k0 ≠ none :=
              h_mono1.2 k0 hkR_after1
            have hk_isSome : (ctxᵢ.regime.lookup? k0).isSome = true := by
              cases hk : ctxᵢ.regime.lookup? k0 with
              | none => exact (hkR_ctxᵢ hk).elim
              | some b => simp
            have htc_bad := htc'
            simp [typecheckVlet, hlookup_ctxᵢ, hpred, hk_isSome] at htc_bad
            cases htc_bad
      · have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
          simpa [hR_eq] using hkR
        have hvars2 := hcwr₁2.2.1 x qt k hlookup_ctxAfter' hguard hkR'
        cases hvars2 with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hlookup_v hconsist =>
            have hlookup_v' : cf₁.varEnv.lookup x = some v := by
              have : cfg₁3.varEnv.lookup x = some v := hlookup_v
              have : cfg₁2.varEnv.lookup x = some v := by
                simpa [hvar_pres₁] using this
              have : cfg₁1.varEnv.lookup x = some v := by
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using this
              simpa [h_var₁_eq] using this
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hR_eq] using hreg
            have hconsist' :
                (b = true → qtypPredHolds predSat qt cf₁.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₁.memory v) := by
              simpa [h_mem₁_eq] using hconsist
            exact
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: use initial hcwr₁; transport regime via monotonicity, memory via predSat independence
        rw [hx] at hlookup hlookup_v
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have h_varEnv_pres₁ : ρ₁ = cfg₁1.varEnv := by
          rcases ht₁_e1_w with ⟨fuel_w, verbose_w, h_beval_w⟩
          exact beval_preserves_varEnv e1 fuel_w verbose_w _ _ _ h_beval_w
        have hlookup_v_ρ₁ : ρ₁.lookup vname = some v := by
          rw [h_varEnv_pres₁]; simpa [h_var₁_eq] using hlookup_v
        have hcap₀ := hcwr₁.2.2 vname qt v hlookup_ctxᵢ hlookup_v_ρ₁
        have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
          simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
        have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
          have h := regime_monotone ctx' e2 fuel' res2 htc2'
          have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
          simpa [hR1, ctxAfter] using h
        have hcap₂ := closureCapturedVarsRegime_monotone h_mono2
          (closureCapturedVarsRegime_monotone h_mono1 hcap₀)
        rw [← hR_eq] at hcap₂
        have hPredSat_mem₁ : ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
          predSat_mem_noPred_compat hpredlaws θ₁
        exact closureCapturedVarsRegime_transport_μ_θ (fun qt' v' =>
          ⟨fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').1 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').1 hs),
           fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').2 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').2 hs)⟩)
          hθext₁.1 hcap₂
      · -- x ≠ vname: use hcwr₁2 from IH2 and transport regimes/memory
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hlookup_v_cfg₁3 : cfg₁3.varEnv.lookup x = some v := by
          have hcf₁_v : cf₁.varEnv.lookup x = some v := hlookup_v
          have : cfg₁1.varEnv.lookup x = some v := by simpa [h_var₁_eq] using hcf₁_v
          have h2 : cfg₁2.varEnv.lookup x = some v := by
            simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using this
          rw [hvar_pres₁]; exact h2
        have hcap := hcwr₁2.2.2 x qt v hlookup_ctxAfter' hlookup_v_cfg₁3
        rw [← hR_eq] at hcap
        rw [← h_mem₁_eq] at hcap
        exact hcap
  have hresTm : QTypRespectsTagMeaning tm2 res.qualType := by
    have hetyp : res.qualType.etyp = res2.qualType.etyp := by
      simp [h_ret_etyp]
    have hpredEq : res.qualType.pred = res2.qualType.pred := by
      simp [h_ret_pred]
    exact fun {qt'} {k} {d} hinq hqd =>
      (QTypRespectsTagMeaning_transport_etyp_pred
        (tm := tm2) (qt := res2.qualType) (qt' := res.qualType) hresTm2 hetyp hpredEq) hinq hqd
  have hext_tm_tm2 : tm ⊑ tm2 :=
    TagMeaningExtends.trans
      (BoundaryTagMeaningPost.extends_tm hcanon1)
      (BoundaryTagMeaningPost.extends_tm hcanon2)
  have hTm_final : wfTagMeaningCtx tm2 (ctxAfter ctxᵢ res) := by
    unfold wfTagMeaningCtx at _hTm2 ⊢
    simp only [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
    have _hTm2' : EnvRespectsTagMeaning tm2 (ctxᵢ.varEnv.update vname res1.qualType) res2.memEnv' := by
      simpa [hctx'] using _hTm2
    refine EnvRespectsTagMeaning_of_update tm2 vname ctxᵢ.varEnv res1.qualType res2.memEnv' _hTm2' ?_
    intro qt hlookup
    exact QTypRespectsTagMeaning_mono hext_tm_tm2
      (wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ vname qt hwfTm hlookup)
  have hboundary_vlet : BoundaryTagMeaningPost ctxᵢ res predSat tm tm2 := by
    exact ⟨hext_tm_tm2, by rw [h_ntag]; exact BoundaryTagMeaningPost.bounded hcanon2,
      hTm_final, hresTm, hpredlaws2⟩
  refine ⟨tm2, hboundary_vlet, hpredlaws2, hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, ?_, hwfcf₀_final,
    hwfcf₁_final, hric₀'', hric₁'', hreg'', hcwr₀_final, hcwr₁_final,
    hagree_clean, ?_, ?_, ?_⟩
  · rw [h_ret_etyp]
    exact _hvtyp₀2
  · rw [h_ret_etyp]
    exact _hvtyp₁2
  · exact hTm_final
  · -- wfTypeContext
    simp only [wfTypeContext, ctxAfter, h_mem, h_loc]
    have hmono_res : ctxᵢ.nextLoc ≤ res.nextLoc' :=
      typecheck_nextLoc_mono ctxᵢ (Expr.vlet vname e1 e2) (fuel' + 2) res htc
    exact ⟨fun l hcontains => hwf2.1 l (by simpa [ctxAfter, h_mem, h_loc] using hcontains),
           varEnvRefLocsBounded_mono hwf.2.1 (h_loc ▸ hmono_res),
           varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 (h_loc ▸ hmono_res)⟩
  · -- TagBoundedCtx
    exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.vlet vname e1 e2) (fuel' + 2) res htc htagBounded
  · -- valueConsistentWithRegime for cf₀
    -- Reuse IH2's value consistency for `res2.qualType`, then transport across
    -- the vlet result's predicate threading and varEnv restoration.
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    have hpred_eq : res2.qualType.pred = res.qualType.pred := by
      simpa using h_ret_pred.symm
    have hmem_eq : cf₀.memory = cfg₀3.memory := by
      simp [hcf₀_eq]
    have hv2 : valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res2.qualType cfg₀3.memory θ₀2 o₀ :=
      _hval_consist₀2
    have hv' :
        valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res.qualType cfg₀3.memory θ₀2 o₀ :=
      valueConsistentWithRegime_transport_pred (predSat := predSat) (R := (ctxAfter ctx' res2).regime)
        (qt := res2.qualType) (qt' := res.qualType) (μ := cfg₀3.memory) (v := o₀) hpred_eq (hetyp := h_ret_etyp.symm) hv2
    simpa [hR_eq, hmem_eq] using hv'
  · -- valueConsistentWithRegime for cf₁
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    have hpred_eq : res2.qualType.pred = res.qualType.pred := by
      simpa using h_ret_pred.symm
    have hmem_eq : cf₁.memory = cfg₁3.memory := by
      simp [hcf₁_eq]
    have hv2 : valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res2.qualType cfg₁3.memory θ₁2 o₁ :=
      _hval_consist₁2
    have hv' :
        valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res.qualType cfg₁3.memory θ₁2 o₁ :=
      valueConsistentWithRegime_transport_pred (predSat := predSat) (R := (ctxAfter ctx' res2).regime)
        (qt := res2.qualType) (qt' := res.qualType) (μ := cfg₁3.memory) (v := o₁) hpred_eq (hetyp := h_ret_etyp.symm) hv2
    simpa [hR_eq, hmem_eq] using hv'
  -- resultAgreesIfClean
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
        calc joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by symm; exact h_ret_poison
             _ = false := by exact hpoison_res
      exact (joinPoison_eq_false hjoin).2
    -- hclean uses (ctxAfter ctxᵢ res).regime = res.regime' = res2.regime'
    -- We need hclean2' : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType for IH2
    -- Since (ctxAfter ctx' res2).regime = res2.regime' = res.regime' = (ctxAfter ctxᵢ res).regime
    -- First, prove regime equality from typechecker structure lemma
    have h_res_regime_eq : res.regime' = res2.regime' := h_ret_regime
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp only [ctxAfter, h_res_regime_eq]
    have hclean2' : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType := by
      cases hclean with
      | clean hpoison_res => exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k htag hreg hnotfun =>
          have htag' : qtypGuardTag res2.qualType = some k := by
            simpa [qtypGuardTag, h_ret_pred] using htag
          have hnotfun' : res2.qualType.etyp.isFunctionType = false := by
            simpa [h_ret_etyp] using hnotfun
          -- hreg : (ctxAfter ctxᵢ res).regime.lookup? k = some true
          -- Need: (ctxAfter ctx' res2).regime.lookup? k = some true
          exact qtypCleanUnder.guard k htag' (h_regime_eq ▸ hreg) hnotfun'
    have hagree2_ctx' := hres_agree2 hclean2'
    -- hagree2_ctx' : agreeValueUnder predSat (ctxAfter ctx' res2).regime cfg₀3.memory cfg₁3.memory ... res2.qualType o₀ o₁
    -- Need: agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory ... res2.qualType o₀ o₁
    -- Note: cf₀.memory = cfg₀3.memory (from hcf₀_eq) and cf₁.memory = cfg₁3.memory
    have hagree2 : agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      have hmem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
      have hmem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
      rw [hmem₀_eq, hmem₁_eq, h_regime_eq]
      exact hagree2_ctx'
    exact agreeValueUnder_transport_clean hclean h_ret_etyp hpoison_imp hagree2

lemma stepFR_vlet
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')) (registry := registry))
  (hOp : RegistryOperationalSafe registry)
  (htc : typecheck ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.vlet vname e1 e2) res predSat tm (registry := registry) := by
    exact
      stepFR_vlet_with_expr_proof
        ctxᵢ predSat vname e1 e2 fuel' res tm
        (fun _ => True) (fun _ => True) trivial trivial trivial
        (fun _ _ _ => trivial)
        (fun m hm {tmᵢ} e ctx _hctx _hcan hwfTm htagBounded res htc =>
          IH m hm (tmᵢ := tmᵢ) e ctx hwfTm htagBounded res htc)
        hOp
        htc

-- World-free version of stepFRW_fn


lemma stepFRSingleRunFinalCleanPcTrue_vlet_maskedReg_with_expr_proof
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (hcan1 : CanUse e1) (hcan2 : CanUse e2)
  (hctxCurrent : CtxReach ctxᵢ)
  (hctxBody :
    ∀ {res1 : TypeResult} {bodyCtx : TypeContext},
      typecheck ctxᵢ e1 fuel' = .ok res1 →
      bodyCtx =
        ({ ctxᵢ with
          memEnv := res1.memEnv',
          varEnv := VarTypeEnv.update ctxᵢ.varEnv vname res1.qualType,
          tagEnv := res1.tagEnv',
          nextLoc := res1.nextLoc',
          nextTag := res1.nextTag',
          regime := res1.regime' } : TypeContext) →
      CtxReach ctxᵢ → CtxReach bodyCtx)
  (IH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_WithExprCtx
      predSat tm (Nat.succ (Nat.succ fuel')) CanUse
      CtxReach
      masked
      (fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v) (registry := registry))
  (hOp : RegistryOperationalSafe registry)
  (htc : typecheck ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.vlet vname e1 e2) res predSat tm (registry := registry) := by
  have htc' : typecheckVlet ctxᵢ vname e1 e2 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_vlet_succ] using htc
  obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, _h_tag, _h_loc, _h_ntag,
      h_ret_regime, _h_ret_poison, h_ret_pred⟩ :=
    typecheckVlet_structure ctxᵢ vname e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck ctx' e2 fuel' = .ok res2 := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves hExtTyping predSat tm ctxᵢ
        (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric hregCtx hmasked_none hmasked_absent hctxCons a pm hwfcfg ht hpc
  have hstruct := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } cf o ht
  rcases hstruct with ⟨cfg1, v1, cfg3, ht_e1, ht_e2, hcf_eq, _hpm1, _hpm_final⟩
  let cfg2 : Config := { cfg1 with varEnv := cfg1.varEnv.update vname v1 }
  have hIH1 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hctxCurrent hcan1 hwfTm hTmBounded res1 htc1'
  have hIH1Inst := hIH1 hpredlaws hExtTyping hwfTm hTmBounded
  rcases hIH1Inst.1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hTm1⟩
  have hwf1 : wfTypeContext (ctxAfter ctxᵢ res1) :=
    wfTypeContext_of_wfTypeResult ctxᵢ res1
      (typecheckExpr_preserves_wfTypeResult ctxᵢ e1 fuel' res1 hwf htc1')
      hwf (typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1')
  have hreg1 : regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ res1) :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked
      (masked := masked) ctxᵢ e1 fuel' res1 hregCtx htc1'
  have hwfcfg1 : wfConfig cfg1 := by
    exact (wfConfig_preserved e1 _ cfg1 _ hOp ht_e1 hwfcfg).1
  rcases
    hIH1Inst.2 μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hmasked_none hmasked_absent hctxCons a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hv1, hric1, hctxCons1, hvalc1, hpres1, _hfresh1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm1 ctx' := by
    simpa [hctx', ctxAfter] using
      wfTagMeaningCtx_varEnv_ext tm1 (ctxAfter ctxᵢ res1) vname res1.qualType hTm1 hresTm1
  have hTmBounded' : TagMeaningBounded tm1 ctx'.nextTag := by
    simpa [hctx', ctxAfter] using
      IsCanonicalExtension.bounded hcanon1
  have hpc1 : ctx'.pc = true := by
    simpa [hctx', ctxAfter, updateCtxFromResult] using hpc
  have hmono1 : Regime.monotoneStep ctxᵢ.regime res1.regime' :=
    regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hmasked_none1 : ∀ k, masked k → (ctxAfter ctxᵢ res1).regime.lookup? k = none := by
    intro k hk
    simpa [ctxAfter] using
      masked_lookup_none_of_monotoneStep
        (R := ctxᵢ.regime) (R' := res1.regime')
        hmasked_none hmono1 k hk
  have hric1' : runtimeInstantiatesCtx ctx' cfg2.memory cfg2.varEnv θ1 := by
    simpa [cfg2, hctx', ctxAfter] using
      runtimeInstantiatesCtx_vlet_body_start ctxᵢ res1 vname cfg1.memory cfg1.varEnv θ1 v1 hric1 hv1
  have hreg1' : regimeConsistentWithCtxMasked masked ctx' := by
    simpa [hctx', ctxAfter, updateCtxFromResult, regimeConsistentWithCtxMasked] using hreg1
  have hmasked_none1' : ∀ k, masked k → ctx'.regime.lookup? k = none := by
    intro k hk
    simpa [hctx', ctxAfter, updateCtxFromResult] using hmasked_none1 k hk
  have hmasked_absent1 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ res1) :=
    typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
      masked ctxᵢ e1 fuel' res1 hmasked_absent hmasked_none htc1'
  have hmasked_absent1' : MaskedTagsAbsentFromTrueTagEnv masked ctx' := by
    simpa [hctx', ctxAfter, updateCtxFromResult, MaskedTagsAbsentFromTrueTagEnv] using
      hmasked_absent1
  have hctxCons1' :
      consistentWithRegimeMasked masked predSat ctx'.regime ctx' cfg2.memory cfg2.varEnv θ1 := by
    simpa [cfg2, hctx', ctxAfter] using
      consistentWithRegimeMasked_vlet_body_start
        masked predSat
        ctxᵢ res1 vname cfg1.memory cfg1.varEnv θ1 v1 hctxCons1 hvalc1
  have hwf1' : wfTypeContext ctx' := by
    rw [hctx']; simp only [wfTypeContext]
    have hmono1 := typecheck_nextLoc_mono ctxᵢ e1 fuel' res1 htc1'
    exact ⟨hwf1.1,
           varEnvRefLocsBounded_update (varEnvRefLocsBounded_mono hwf.2.1 hmono1)
             (typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e1 fuel' res1 hwf htc1'),
           varEnvClosuresCapturedRefLocsBounded_update (varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono1)
             (typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e1 fuel' res1 hwf htc1')⟩
  have hv1_wf : wfValue cfg1.nextAddr v1 := by
    exact (wfConfig_preserved e1 _ cfg1 _ hOp ht_e1 hwfcfg).2
  have hwfcfg2 : wfConfig cfg2 := by
    rcases hwfcfg1 with ⟨hwfmem1, hwfenv1⟩
    refine ⟨?_, ?_⟩
    · simpa [cfg2] using hwfmem1
    ·
      have hwfenv2 : wfVarEnv cfg1.nextAddr ((vname, v1) :: cfg1.varEnv) :=
        wfVarEnv.cons vname v1 cfg1.varEnv hv1_wf hwfenv1
      simpa [cfg2, VarEnv.update] using hwfenv2
  have hIH2 := IH fuel' (by simpa using Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' (hctxBody htc1' hctx' hctxCurrent) hcan2 hwfTm' hTmBounded' res2 htc2'
  -- Thread extern registry: cfg1 inherits default registry from initial config.
  have hreg_cfg1 : cfg1.registry = registry := by
    simpa using terminatesTo_preserves_registry ht_e1
  have ht_e2_ih : terminatesTo e2
      { memory := cfg2.memory, varEnv := cfg2.varEnv, nextAddr := cfg1.nextAddr, pureMode := cfg1.pureMode, registry := registry }
      cfg3 o := by
    have tmp := ht_e2
    rw [hreg_cfg1] at tmp
    exact tmp
  rcases
    (hIH2 hpredlaws1 hExtTyping hwfTm' hTmBounded').2 cfg2.memory cfg2.varEnv θ1 cfg3 o
      hθ1wf hwf1' hric1' hreg1' hmasked_none1' hmasked_absent1' hctxCons1'
      cfg1.nextAddr cfg1.pureMode hwfcfg2 ht_e2_ih hpc1
    with ⟨θ2, hθext2, hv2, hric2, hctxCons2, hvalc2, hpres2, _hfresh2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hctxAfter_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
    simp [ctxAfter, h_ret_regime]
  have hric_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ2 := by
    rcases hric2 with ⟨hmem2, _hvars2⟩
    rcases hric1 with ⟨_hmem1, hvars1⟩
    constructor
    · intro l a hlookup
      have hmem := hmem2 l a hlookup
      simpa [ctxAfter, h_mem, hcf_eq] using hmem
    · intro u qt hlookup
      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
        simpa [ctxAfter] using hlookup
      rcases hvars1 hlookup' with ⟨v_u, hvlookup, hvtyp⟩
      refine ⟨v_u, ?_, valueHasETyp_extends hθext2.1 hvtyp⟩
      simpa [hcf_eq] using hvlookup
  have h_mono_e2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
    have h := regime_monotone ctx' e2 fuel' res2 htc2'
    have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
      simp [hctx', ctxAfter]
    simpa [hR1] using h
  have hctxCons_final :
      consistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ2 := by
    exact
      consistentWithRegimeMasked_vlet_finish
        (masked := masked) (predSat := predSat) (tm := tm1)
        (ctx := ctxᵢ) (ctx' := ctx') (result1 := res1) (result2 := res2) (result := res)
        (cfg1 := cfg1) (cfg3 := cfg3) (cf := cf) (θ1 := θ1) (θ2 := θ2)
        hpredlaws1 hcf_eq h_mem h_ret_regime h_mono_e2 hctxCons1 hctxCons2 hθext2
  have hvalc_final :
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter ctxᵢ res).regime res.qualType cf.memory θ2 o := by
    exact
      valueConsistentWithRegimeMasked_vlet_finish masked predSat
        (ctxAfter ctx' res2).regime (ctxAfter ctxᵢ res).regime
        res2.qualType res.qualType cfg3.memory cf.memory θ2 o
        (by simp [hcf_eq])
        hctxAfter_regime_eq
        h_ret_etyp.symm h_ret_pred.symm hvalc2
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctxᵢ res1) res2
        cfg1.memory cfg3.memory θ1 θ2 := by
    refine ⟨?_⟩
    intro l qt_in qt_out hlookup_in hlookup_out hclean_out
    exact
      PreservesInheritedFinalCleanLocsOneRun.apply
        (ctx := ctx') (res := res2)
        (μ_in := cfg1.memory) (μ_out := cfg3.memory)
        (θ_in := θ1) (θ_out := θ2)
        hpres2
        (by simpa [hctx', ctxAfter] using hlookup_in)
        hlookup_out hclean_out
  have hclean_back :
      ∀ l qt_in qt_out,
        ctxᵢ.memEnv.lookup l = some qt_in →
        res2.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res2.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true hExtTyping
        (ctx := ctx') (e := e2) (fuel := fuel') (res := res2)
        htc2' hwf1' hpc1 l qt_out
        hlookup_out
        (by simpa [hctx'] using typecheckExpr_mem_contains_preserved ctxᵢ e1 fuel' res1 htc1' l (memEnv_contains_of_lookup_some ctxᵢ.memEnv l _qt_in _hlookup_in))
        hclean_out
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [hctx', ctxAfter] using hlookup_mid, by simpa [hctx', ctxAfter] using hclean_mid⟩
  have hpres_final_cfg3 :
      PreservesInheritedFinalCleanLocsOneRun ctxᵢ res2 μ cfg3.memory θ θ2 := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctxᵢ) (res1 := res1) (res2 := res2)
        hclean_back hpres1 hpres2'
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ2 := by
    refine ⟨?_⟩
    intro l qt_in qt_out hlookup_in hlookup_out hclean_out
    have hlookup_out2 : res2.memEnv'.lookup l = some qt_out := by
      simpa [h_mem] using hlookup_out
    have hclean_out2 : qtypCleanUnder res2.regime' qt_out := by
      simpa [h_ret_regime] using hclean_out
    have hpres := PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctxᵢ) (res := res2) (μ_in := μ) (μ_out := cfg3.memory)
      (θ_in := θ) (θ_out := θ2) hpres_final_cfg3 hlookup_in hlookup_out2 hclean_out2
    simpa [hcf_eq] using hpres
  have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ2 := by
    intro l qt hnotIn hlookup hclean
    have hlookup2 : res2.memEnv'.lookup l = some qt := by simpa [h_mem] using hlookup
    have hclean2 : qtypCleanUnder res2.regime' qt := by simpa [h_ret_regime] using hclean
    by_cases hcontains_mid : (ctxAfter ctxᵢ res1).memEnv.contains l
    · obtain ⟨qt_mid, hlookup_mid, hclean_mid⟩ :=
        typecheckExpr_clean_lookup_origin_of_pc_true hExtTyping
          (ctx := ctx') (e := e2) (fuel := fuel') (res := res2)
          htc2' hwf1' hpc1 l qt hlookup2
          (by simpa [hctx', ctxAfter] using hcontains_mid)
          hclean2
      have hθ1_none := _hfresh1 l qt_mid hnotIn
        (by simpa [hctx', ctxAfter] using hlookup_mid)
        (by simpa [hctx', ctxAfter] using hclean_mid)
      have hpres_loc := PreservesInheritedFinalCleanLocsOneRun.apply hpres2'
        (show (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt_mid from
          by simpa [hctx', ctxAfter] using hlookup_mid)
        hlookup2 hclean2
      cases hpres_loc with
      | both_unrealized _ hout => exact hout
      | preserve_value a n hin _ _ _ => simp [hθ1_none] at hin
    · exact _hfresh2 l qt
        (show ¬ ctx'.memEnv.contains l from
          by simpa [hctx', ctxAfter] using hcontains_mid)
        hlookup2 hclean2
  refine ⟨θ2, hθext, ?_, hric_final, hctxCons_final, hvalc_final, hpres_final, hfresh_final⟩
  rw [h_ret_etyp]
  exact hv2

