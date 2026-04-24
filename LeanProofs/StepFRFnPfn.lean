/-
  Auto-extracted from FaultRobustnessProofs.lean during StepFR operator refactor.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

lemma stepFRSingleRunFinalCleanPcTrue_fn_maskedReg
  (masked : Tag → Prop)
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.fn x paramType body returnType) res predSat tm := by
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
  intro _hpredlaws _hExtTyping hwfTm μ ρ θ cf o hθwf hwf hric hreg hmasked_none hcwr a pm hwfcfg ht _hpc
  have ⟨hcf, ho⟩ := terminatesTo_fn_inv' x paramType body returnType
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  subst hcf
  have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
    subst ho
    have hcover : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure
      (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp) (hcover := hcover) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ.lookup y := by symm; exact hvlookup
          _ = some v := hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  have hvalc :
      valueConsistentWithRegimeMasked masked predSat ctxᵢ.regime res.qualType μ θ o := by
    subst ho
    refine valueConsistentWithRegimeMasked.noTag
      (by simp [qtypGuardTag, hres, res_expected]) ?_
    apply deepValueQTypProperty.closure x body ρ
      (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
      [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
    · rfl
    · simp [hres, res_expected]
    · simp
    · constructor
      · intro y qt_y k_y hlookup_σ hguard hkR
        exact hcwr.2.1 y qt_y k_y
          (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
          hguard hkR
      · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
          fun y qt hlookup_σ =>
            let ⟨v, hv, _⟩ := hric.2
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
            ⟨v, hv⟩,
          fun y qt v hlookup_σ hlookup_ρ =>
            let ⟨v', hv', htyp⟩ := hric.2
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
            by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
    · intro y qt_y v_y hlookup_σ hlookup_ρ
      exact hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
        hlookup_ρ
  exact
    singleRunFinalCleanWitness_of_same_state_maskedReg_param
      (masked := masked)
      (CtxCons := fun ctx μ ρ θ =>
        consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (ValCons := fun R qt μ θ v =>
        valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      (_predSat := predSat) (ctx := ctxᵢ) (res := res) (tm := tm)
      (μ := μ) (ρ := ρ) (θ := θ)
      (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
      (o := o) (a := a) (pm := pm)
      hctxAfter rfl hvaltyp hcwr hvalc hwfTm hwf hric hreg hmasked_none hwfcfg


lemma stepFRSingleRunFinalCleanPcTrue_pfn_maskedReg
  (masked : Tag → Prop)
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.pfn x paramType body returnType) res predSat tm := by
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
      intro _hpredlaws _hExtTyping hwfTm μ ρ θ cf o hθwf hwf hric hreg hmasked_none hcwr a pm hwfcfg ht _hpc
      have ⟨hcf, ho⟩ := terminatesTo_pfn_inv' x paramType body returnType
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
      subst hcf
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
        subst ho
        have hcover : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure
          (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv)
          (hpure := hto) (htcl := by simp) (hcover := hcover) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ.lookup y := by symm; exact hvlookup
              _ = some v := hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      have hvalc :
          valueConsistentWithRegimeMasked masked predSat ctxᵢ.regime res.qualType μ θ o := by
        subst ho
        refine valueConsistentWithRegimeMasked.noTag
          (by simp [qtypGuardTag, hres, res_expected]) ?_
        apply deepValueQTypProperty.peClosure x body pbody ρ
          (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
          [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · exact hto
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric.2
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric.2
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          exact hcwr.2.2 y qt_y v_y
            (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
            hlookup_ρ
      exact
        singleRunFinalCleanWitness_of_same_state_maskedReg_param
          (masked := masked)
          (CtxCons := fun ctx μ ρ θ =>
            consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
          (ValCons := fun R qt μ θ v =>
            valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
          (_predSat := predSat) (ctx := ctxᵢ) (res := res) (tm := tm)
          (μ := μ) (ρ := ρ) (θ := θ)
          (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
          (o := o) (a := a) (pm := pm)
          hctxAfter rfl hvaltyp hcwr hvalc hwfTm hwf hric hreg hmasked_none hwfcfg


lemma stepFR_fn
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR ctxᵢ (Expr.fn x paramType body returnType) res predSat tm := by
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
  intro hpredlaws hExtTyping hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma
  have ⟨hcf₀, ho₀⟩ := terminatesTo_fn_inv' x paramType body returnType
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_fn_inv' x paramType body returnType
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hcap' :
      agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
    agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
  -- Convert to use output regime (which equals input regime for fn)
  have h_regime_eq : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [hctxAfter]
  have hcap :
      agreeCapturedEnv predSat (ctxAfter ctxᵢ res).regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ := by
    rw [h_regime_eq]; exact hcap'
  have hresTm_expected : QTypRespectsTagMeaning tm res_expected.qualType := by
    intro qt' k d hinq hqd
    exact
      (QTypRespectsTagMeaning_fn_regular
        (tm := tm) (ctx := ctxᵢ) (x := x)
        (st₁ := paramType) (st₂ := returnType) (p := ctxᵢ.pc) (body := body) hwfTm)
        (by simpa [res_expected] using hinq)
        (by simpa [res_expected] using hqd)
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    intro qt' k d hinq hqd
    exact hresTm_expected (by simpa [hres] using hinq) (by simpa [hres] using hqd)
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · have hcover₀ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ₀.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric₀.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    subst ho₀
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp)
        (hcover := hcover₀) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric₀.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ₀.lookup y := by symm; exact hvlookup
          _ = some v := by exact hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  · have hcover₁ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ₁.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric₁.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    subst ho₁
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp)
        (hcover := hcover₁) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric₁.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ₁.lookup y := by symm; exact hvlookup
          _ = some v := by exact hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using hwfTm
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using hwf
  · -- TagBoundedCtx (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using htagBounded
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
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
      (.intro (by
        rw [ho₀, h_regime_eq]
        apply deepValueQTypProperty.closure x body ρ₀
            (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr₀.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          cases hcwr₀.2.2 y qt_y v_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hlookup_ρ with
          | intro h => exact h))
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
      (.intro (by
        rw [ho₁, h_regime_eq]
        apply deepValueQTypProperty.closure x body ρ₁
            (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr₁.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          cases hcwr₁.2.2 y qt_y v_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hlookup_ρ with
          | intro h => exact h))
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
        have hmemberVars₀ :
            MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₀
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
          simpa [hctxAfter] using
            (memberVarsRegimeEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
        have hmemberVars₁ :
            MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₁
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
          simpa [hctxAfter] using
            (memberVarsRegimeEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
        have hmemberCvcr₀ :
            MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₀ θ₀
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
          simpa [hctxAfter] using
            (memberCvcrEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
        have hmemberCvcr₁ :
            MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₁ θ₁
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
          simpa [hctxAfter] using
            (memberCvcrEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
        exact
          agreeValueUnder.clean_internal_arrow
            (tcl := FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv))
            (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
            hclean_internal hetyp (by simp) rfl hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
            (by simp [ho₀]) (by simp [ho₁])
    | guard k htag _hregime _ =>
        have : False := by
          have hpred : qtypGuardTag res.qualType = none := by
            simp [qtypGuardTag, hres, res_expected]
          simp [hpred] at htag
        exact False.elim this

-- World-free version of stepFRW_pfn

lemma stepFR_pfn
  
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR ctxᵢ (Expr.pfn x paramType body returnType) res predSat tm := by
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
      intro hpredlaws hExtTyping hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
      -- Use world-free inversion lemma
      have ⟨hcf₀, ho₀⟩ := terminatesTo_pfn_inv' x paramType body returnType
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
      have ⟨hcf₁, ho₁⟩ := terminatesTo_pfn_inv' x paramType body returnType
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
      subst hcf₀ hcf₁
      have hcap' :
          agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
        agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
      -- Convert to use output regime (which equals input regime for pfn)
      have h_regime_eq : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [hctxAfter]
      have hcap :
          agreeCapturedEnv predSat (ctxAfter ctxᵢ res).regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ := by
        rw [h_regime_eq]; exact hcap'
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hresTm_expected : QTypRespectsTagMeaning tm res_expected.qualType := by
        intro qt' k d hinq hqd
        exact
          (QTypRespectsTagMeaning_pfn_regular
            (tm := tm) (ctx := ctxᵢ) (x := x)
            (st₁ := paramType) (st₂ := returnType) (p := ctxᵢ.pc) (body := pbody) hwfTm)
            (by simpa [res_expected] using hinq)
            (by simpa [res_expected] using hqd)
      have hresTm : QTypRespectsTagMeaning tm res.qualType := by
        intro qt' k d hinq hqd
        exact hresTm_expected (by simpa [hres] using hinq) (by simpa [hres] using hqd)
      refine ⟨hresTm, ?_⟩
      refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · have hcover₀ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ₀.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric₀.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        subst ho₀
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (hpure := hto) (htcl := by simp)
            (hcover := hcover₀) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric₀.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ₀.lookup y := by symm; exact hvlookup
              _ = some v := by exact hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      · have hcover₁ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ₁.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric₁.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        subst ho₁
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (hpure := hto) (htcl := by simp)
            (hcover := hcover₁) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric₁.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ₁.lookup y := by symm; exact hvlookup
              _ = some v := by exact hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using hwfTm
      · -- wfTypeContext (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using hwf
      · -- TagBoundedCtx (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using htagBounded
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
      · -- valueConsistentWithRegime for cf₀
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
          (.intro (by
            rw [ho₀, h_regime_eq]
            apply deepValueQTypProperty.peClosure x body pbody ρ₀
                (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
            · rfl
            · simp [hres, res_expected]
            · exact hto
            · simp
            · constructor
              · intro y qt_y k_y hlookup_σ hguard hkR
                exact hcwr₀.2.1 y qt_y k_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hguard hkR
              · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
                  fun y qt hlookup_σ =>
                    let ⟨v, hv, _⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    ⟨v, hv⟩,
                  fun y qt v hlookup_σ hlookup_ρ =>
                    let ⟨v', hv', htyp⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
            · intro y qt_y v_y hlookup_σ hlookup_ρ
              cases hcwr₀.2.2 y qt_y v_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hlookup_ρ with
              | intro h => exact h))
      · -- valueConsistentWithRegime for cf₁
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
          (.intro (by
            rw [ho₁, h_regime_eq]
            apply deepValueQTypProperty.peClosure x body pbody ρ₁
                (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
            · rfl
            · simp [hres, res_expected]
            · exact hto
            · simp
            · constructor
              · intro y qt_y k_y hlookup_σ hguard hkR
                exact hcwr₁.2.1 y qt_y k_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hguard hkR
              · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
                  fun y qt hlookup_σ =>
                    let ⟨v, hv, _⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    ⟨v, hv⟩,
                  fun y qt v hlookup_σ hlookup_ρ =>
                    let ⟨v', hv', htyp⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
            · intro y qt_y v_y hlookup_σ hlookup_ρ
              cases hcwr₁.2.2 y qt_y v_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hlookup_ρ with
              | intro h => exact h))
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
                  PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) :=
              ⟨hto, rfl⟩
            -- Same reasoning as stepFR_fn: outer poison = ctxᵢ.pc = false, so internal clean
            have hpc_clean : ctxᵢ.pc = false := by
              have hqt_poison : res.qualType.poison = ctxᵢ.pc := by
                simp [hres, res_expected]
              calc
                ctxᵢ.pc = res.qualType.poison := by symm; exact hqt_poison
                _ = false := by exact hpoison
            have hclean_internal : internalPoisonClean res.qualType := by
              simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
            have hmemberVars₀ :
                MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₀
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
              simpa [hctxAfter] using
                (memberVarsRegimeEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
            have hmemberVars₁ :
                MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₁
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
              simpa [hctxAfter] using
                (memberVarsRegimeEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
            have hmemberCvcr₀ :
                MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₀ θ₀
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
              simpa [hctxAfter] using
                (memberCvcrEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
            have hmemberCvcr₁ :
                MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₁ θ₁
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
              simpa [hctxAfter] using
                (memberCvcrEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
            exact
              agreeValueUnder.clean_internal_parrow
                (pbody := pbody)
                (tcl := PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv))
                (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
                hclean_internal hetyp htcl hmatch hcap
                hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
                (by simp [ho₀]) (by simp [ho₁])
        | guard k htag _hregime _ =>
            have : False := by
              have hpred : qtypGuardTag res.qualType = none := by
                simp [qtypGuardTag, hres, res_expected]
              simp [hpred] at htag
            exact False.elim this
