/-
  StepFRApp.lean - Fault-robustness proof for function application (stepFR_app).

  Contains the stepFR_app lemma and all helper lemmas used exclusively by it,
  including join-transport lemmas, applyFnTClosure/applyPFnTClosure infrastructure,
  and joinTypeResults compatibility lemmas.
-/
import LeanProofs.StepFR
import LeanProofs.JoinMemberTransport

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

private def AppClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext) (result2 result1 : TypeResult)
    (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
    (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
    (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value),
    PredSatLaws predSat tm →
    result2.qualType = ⟨etyp2, p2, pred2⟩ →
    result1.qualType.etyp = ETyp.arrow st1 st2 p tcls →
    Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime' →
    wfExtendsMap θ_arg θ →
    CtxCons (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ →
    ValCons (ctxAfter ctx result2).regime result2.qualType μ_arg θ_arg vArg →
    ValCons (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
      (Value.closure x body ρcap) →
    ∃ σcap,
      FnTClosure.regular x body σcap ∈ tcls ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      CtxCons bodyCtx μ (ρcap.update x vArg) θ

private def AppPClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext) (result2 result1 : TypeResult)
    (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
    (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
    (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
    (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value),
    PredSatLaws predSat tm →
    result2.qualType = ⟨etyp2, p2, pred2⟩ →
    result1.qualType.etyp = ETyp.parrow st1 st2 p tcls →
    Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime' →
    wfExtendsMap θ_arg θ →
    CtxCons (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ →
    ValCons (ctxAfter ctx result2).regime result2.qualType μ_arg θ_arg vArg →
    ValCons (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
      (Value.peClosure x body ρcap) →
    ∃ σcap pbody,
      Expr.toPExpr? body = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      CtxCons bodyCtx μ (ρcap.update x vArg) θ

private def AppMemberCtxCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) : Prop :=
  ∀ (ctx bodyCtx : TypeContext)
    (result2 result1 src result3 : TypeResult) (qtSrc : QTyp)
    (cpre cbody cfinal : Config) (θpre θfinal : RealizationMap),
    (∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt cpre.memory v ↔ qtypPredHolds predSat qt cfinal.memory v) →
    src = { result3 with qualType := qtSrc } →
    cfinal.memory = cbody.memory →
    cfinal.varEnv = cpre.varEnv →
    (∀ k b,
      (ctxAfter ctx src).regime.lookup? k = some b →
      (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b) →
    wfExtendsMap θpre θfinal →
    CtxCons (ctxAfter (ctxAfter ctx result2) result1) cpre.memory cpre.varEnv θpre →
    CtxCons (ctxAfter bodyCtx result3) cbody.memory cbody.varEnv θfinal →
    CtxCons (ctxAfter ctx src) cfinal.memory cfinal.varEnv θfinal

private def AppBodyResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx bodyCtx : TypeContext) (src result3 : TypeResult)
    (p p1 : Poison) (μ_src μ_body : Memory) (θ : RealizationMap) (v : Value),
    src =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } →
    μ_src = μ_body →
    ValCons (ctxAfter bodyCtx result3).regime result3.qualType μ_body θ v →
    ValCons (ctxAfter ctx src).regime src.qualType μ_src θ v

private def AppJoinCtxConsFromMember
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop) : Prop :=
  ∀ (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap),
    joinTypeResults ctx first rest = .ok res →
    src ∈ first :: rest →
    CtxCons (ctxAfter ctx src) μ ρ θ →
    CtxCons (ctxAfter ctx res) μ ρ θ

private def AppJoinValConsFromMember
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  ∀ (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (μ : Memory) (θ : RealizationMap) (v : Value),
    joinTypeResults ctx first rest = .ok res →
    src ∈ first :: rest →
    ValCons (ctxAfter ctx src).regime src.qualType μ θ v →
    ValCons (ctxAfter ctx res).regime res.qualType μ θ v

-- Helper lemmas for stepFR_app: join-lifting and body-context bridges.
--
-- Join-transport lemmas: when `joinTypeResults ctx first rest = .ok res`, transport
-- properties from `(ctxAfter ctx first)` to `(ctxAfter ctx res)`. Used by both peClosure
-- and closure branches.

private lemma join_transport_wfTypeContext
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_mem : ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l)
  (h_first : wfTypeContext (ctxAfter ctx first))
  (h_rest_wf : ∀ r ∈ rest, wfTypeResult r) :
  wfTypeContext (ctxAfter ctx res) := by
  simp only [wfTypeContext, ctxAfter]
  have hfirst_le_res : first.nextLoc' ≤ res.nextLoc' :=
    joinTypeResults_member_nextLoc_le ctx first rest res h_join first (List.Mem.head _)
  refine ⟨?_, varEnvRefLocsBounded_mono h_first.2.1 (by simpa [ctxAfter] using hfirst_le_res),
           varEnvClosuresCapturedRefLocsBounded_mono h_first.2.2 (by simpa [ctxAfter] using hfirst_le_res)⟩
  intro l hcontains
  rcases h_mem l hcontains with hfirst | ⟨r, hr_mem, h_in⟩
  · -- l in first
    have hlt := h_first.1 l (by simp only [ctxAfter]; exact hfirst)
    rw [joinTypeResults_nextLoc_eq_max _ _ _ _ h_join]
    have hle : first.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem
      simp
    exact Nat.lt_of_lt_of_le hlt hle
  · -- l in some r ∈ rest
    have hwf := h_rest_wf r hr_mem
    have hlt := hwf l h_in
    rw [joinTypeResults_nextLoc_eq_max _ _ _ _ h_join]
    have hle : r.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem
      simp only [List.mem_cons, List.mem_map]
      right
      exact ⟨r, hr_mem, rfl⟩
    exact Nat.lt_of_lt_of_le hlt hle

private lemma join_transport_regimeConsistentWithCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_tag_join : tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime)
  (_h_first : regimeConsistentWithCtx (ctxAfter ctx first)) :
  regimeConsistentWithCtx (ctxAfter ctx res) := by
  simp only [regimeConsistentWithCtx, ctxAfter]
  exact h_tag_join

private lemma join_transport_valueConsistentWithRegime
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_first : valueConsistentWithRegime predSat (ctxAfter ctx first).regime qt μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime qt μ θ v :=
  valueConsistentWithRegime_monotone h_regime_mono h_first

-- Transport closureCapturedVarsRegime from first.qualType to res.qualType when joinTypeResults succeeds.
-- Proved by induction on the join fold; each step uses closureCapturedVarsRegime_joinETyps_step.
private lemma joinTypeResults_closure_cvcr_transport
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hcap : closureCapturedVarsRegime predSat R first.qualType μ θ v) :
  closureCapturedVarsRegime predSat R res.qualType μ θ v := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_cvcr :
      ∀ (rs' : List TypeResult) (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        closureCapturedVarsRegime predSat R ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' hcompat hfold hcap_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hcap_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 := (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 x.regime',
              max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcap1 := closureCapturedVarsRegime_joinETyps_step predSat R μ θ v acc.1 resEtyp
              acc.2.2.1 resPoison acc.2.2.2.1 resPred hcompat_x hcap_acc
            have hcap1' : closureCapturedVarsRegime predSat R ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
              simpa [acc1] using hcap1
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by simpa [acc1] using hfold
            exact ih acc1 hcompat_tail hfold_tail hcap1'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ => erw [hcheck] at h_join; contradiction
      | ok _ =>
          erw [hcheck] at h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ => erw [hfold] at h_join; contradiction
          | ok a =>
              erw [hfold] at h_join
              have heq := Except.ok.inj h_join
              have hetyp : (⟨a.1, a.2.2.1, a.2.2.2.1⟩ : QTyp).etyp = res.qualType.etyp :=
                congr_arg (·.qualType.etyp) heq
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              have hcvcr_acc := h_fold_cvcr rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') a hcompat hfold
                (hqt ▸ hcap)
              exact closureCapturedVarsRegime_transport_etyp hetyp hcvcr_acc
-- Transport valueConsistentWithRegime when qualType changes from first to res (via pred transport).
private lemma join_transport_valueConsistentWithRegime_resQual
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hpred : res.qualType.pred = first.qualType.pred)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_first : valueConsistentWithRegime predSat (ctxAfter ctx first).regime first.qualType μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v := by
  have h_mono := valueConsistentWithRegime_monotone h_regime_mono h_first
  refine valueConsistentWithRegime_transport_pred' (hpred.symm)
    (fun hcap => joinTypeResults_closure_cvcr_transport predSat ctx first rest res
      (ctxAfter ctx res).regime μ θ v h_join hcap) h_mono

-- Weaken runtimeInstantiatesCtx when going from post-e1 context to post-e2 context.
-- Requires memEnv equality (holds when e1 is var/fn/pfn producing arrow).
private lemma runtimeInstantiatesCtx_weaken_ctx
  (ctx : TypeContext) (res_outer res_inner : TypeResult) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (h_mem_eq : res_outer.memEnv' = res_inner.memEnv')
  (hric : runtimeInstantiatesCtx (ctxAfter ctx res_inner) μ ρ θ) :
  runtimeInstantiatesCtx (ctxAfter ctx res_outer) μ ρ θ := by
  unfold runtimeInstantiatesCtx
  simp only [ctxAfter, h_mem_eq]
  exact hric

-- Obtain runtimeInstantiatesCtx for closure env from post-e1 instantiation and closure typing.
-- The body context needs env₀ (closure's captured env), not c₁₀.varEnv.
-- Requires memEnv equality and that env₀ realises the context's varEnv.
private lemma runtimeInstantiatesCtx_of_closure_env
  (ctx : TypeContext) (res2 res1 : TypeResult) (μ : Memory) (env₀ ρ : VarEnv) (θ : RealizationMap)
  (h_mem_eq : res2.memEnv' = res1.memEnv')
  (hric : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx res2) res1) μ ρ θ)
  (h_env : ∀ x qt, (ctxAfter ctx res2).varEnv.lookup x = some qt →
    ∃ v, env₀.lookup x = some v ∧ valueHasETyp θ v qt.etyp) :
  runtimeInstantiatesCtx (ctxAfter ctx res2) μ env₀ θ := by
  unfold runtimeInstantiatesCtx at hric ⊢
  simp only [ctxAfter] at hric ⊢
  constructor
  · intro l a hθ
    obtain ⟨hctx, hμ⟩ := hric.1 l a hθ
    rw [h_mem_eq]; exact ⟨hctx, hμ⟩
  · intro x qt h
    exact h_env x qt h

private lemma consistentWithRegime_app_closure_body_start
  (predSat : PredSat)
  (ctx : TypeContext) (result2 result1 : TypeResult)
  (σcap : CapturedVarEnv) (x : Name) (argQt : QTyp)
  (μ : Memory) (θ : RealizationMap) (ρpre ρcap : VarEnv) (vArg : Value)
  (hpre :
    consistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hσcap_regime :
    ∀ y qt k,
      σcap.lookup y = some qt →
      qtypGuardTag qt = some k →
      result1.regime'.lookup? k ≠ none →
      varsRegime predSat result1.regime' μ ρcap (y, qt))
  (hσcap_rec :
    ∀ y qt v,
      σcap.lookup y = some qt →
      ρcap.lookup y = some v →
      closureCapturedVarsRegime predSat result1.regime' qt μ θ v)
  (harg_vars :
    ∀ k,
      qtypGuardTag argQt = some k →
      result1.regime'.lookup? k ≠ none →
      varsRegime predSat result1.regime' μ (ρcap.update x vArg) (x, argQt))
  (harg_cvcr :
    closureCapturedVarsRegime predSat result1.regime' argQt μ θ vArg) :
  let bodyCtx : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' }
  consistentWithRegime predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  intro bodyCtx
  have hlocs_src :
      ∀ l qt k,
        result1.memEnv'.lookup l = some qt →
        qtypGuardTag qt = some k →
        result1.regime'.lookup? k ≠ none →
        locsRegime predSat result1.regime' μ θ (l, qt) :=
    fun l qt k hlookup hguard hRdef =>
      hpre.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
  have hvars_cap :
      ∀ y qt k,
        (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
        qtypGuardTag qt = some k →
        result1.regime'.lookup? k ≠ none →
        varsRegime predSat result1.regime' μ ρcap (y, qt) :=
    fun y qt k hlookup hguard hRdef =>
      hσcap_regime y qt k
        (list_lookup_of_ofCaptured_lookup σcap y qt hlookup) hguard hRdef
  have h_cap_cvcr :
      ∀ y qt v,
        (VarTypeEnv.ofCaptured σcap).lookup y = some qt →
        ρcap.lookup y = some v →
        closureCapturedVarsRegime predSat result1.regime' qt μ θ v :=
    fun y qt v hlookup hv =>
      hσcap_rec y qt v
        (list_lookup_of_ofCaptured_lookup σcap y qt hlookup) hv
  simpa [bodyCtx] using
    consistentWithRegime_closure_body_start
      predSat ctx result1
      σcap x argQt μ θ ρcap vArg
      hlocs_src hvars_cap harg_vars h_cap_cvcr harg_cvcr

private lemma consistentWithRegimeMasked_app_closure_body_start
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx : TypeContext) (result2 result1 : TypeResult)
  (σcap : CapturedVarEnv) (x : Name) (argQt : QTyp)
  (μ : Memory) (θ : RealizationMap) (ρpre ρcap : VarEnv) (vArg : Value)
  (hpre :
    consistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hσcap_regime :
    ∀ y qt k,
      σcap.lookup y = some qt →
      qtypGuardTag qt = some k →
      result1.regime'.lookup? k ≠ none →
      masked k ∨ varsRegime predSat result1.regime' μ ρcap (y, qt))
  (hσcap_rec :
    ∀ y qt v,
      σcap.lookup y = some qt →
      ρcap.lookup y = some v →
      closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v)
  (harg_vars :
    ∀ k,
      qtypGuardTag argQt = some k →
      result1.regime'.lookup? k ≠ none →
      masked k ∨ varsRegime predSat result1.regime' μ (ρcap.update x vArg) (x, argQt))
  (harg_cvcr :
    closureCapturedVarsRegimeMasked masked predSat result1.regime' argQt μ θ vArg) :
  let bodyCtx : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' }
  consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  intro bodyCtx
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    exact hpre.1 l qt k (by simpa [bodyCtx, ctxAfter] using hlookup) (by simpa [bodyCtx] using hguard)
      (by simpa [bodyCtx] using hRdef)
  · intro y qt k hlookup hguard hRdef
    by_cases hy : y = x
    · have hlookup_xarg :
          (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x = some qt := by
        simpa [bodyCtx, hy] using hlookup
      have hqt : qt = argQt := by
        have hself :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured σcap) x argQt
        have : (some qt : Option QTyp) = some argQt := by
          calc
            some qt =
                (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x := by
                  symm
                  exact hlookup_xarg
            _ = some argQt := hself
        exact Option.some.inj this
      subst hqt
      have hRdef' : result1.regime'.lookup? k ≠ none := by
        simpa [bodyCtx] using hRdef
      simpa [bodyCtx, hy] using (harg_vars k hguard hRdef')
    · have hlookup_cap : (VarTypeEnv.ofCaptured σcap).lookup y = some qt := by
        have hne_lookup :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup y =
              (VarTypeEnv.ofCaptured σcap).lookup y :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured σcap) x y argQt hy
        simpa [bodyCtx, hne_lookup] using hlookup
      have hvars := hσcap_regime y qt k
        (list_lookup_of_ofCaptured_lookup σcap y qt hlookup_cap) hguard (by simpa [bodyCtx] using hRdef)
      cases hvars with
      | inl hmasked =>
          exact Or.inl hmasked
      | inr hvars =>
          cases hvars with
          | noPred_ok hnp =>
              exact Or.inr (varsRegime.noPred_ok (y, qt) hnp)
          | guardOnly_ok k' hgo =>
              exact Or.inr (varsRegime.guardOnly_ok (y, qt) k' hgo)
          | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
              have hvar' : (VarEnv.update ρcap x vArg).lookup y = some v := by
                have hne := VarEnv_lookup_update_ne ρcap x y vArg hy
                simpa [hne] using hvar
              exact Or.inr <|
                varsRegime.withPred_ok (y, qt) k' arg_name pred_body var_env v b hclos hreg hvar' hcons
  · intro y qt v hlookup hlookup_v
    by_cases hy : y = x
    · have hlookup_xarg :
          (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x = some qt := by
        simpa [bodyCtx, hy] using hlookup
      have hqt : qt = argQt := by
        have hself :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured σcap) x argQt
        have : (some qt : Option QTyp) = some argQt := by
          calc
            some qt =
                (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup x := by
                  symm
                  exact hlookup_xarg
            _ = some argQt := hself
        exact Option.some.inj this
      subst hqt
      have hv : v = vArg := by
        have hself : (VarEnv.update ρcap x vArg).lookup x = some vArg := by
          simp [VarEnv.update, VarEnv.lookup]
        have hlookup_v_xarg : (VarEnv.update ρcap x vArg).lookup x = some v := by
          simpa [hy, VarEnv.update, VarEnv.lookup] using hlookup_v
        exact Option.some.inj (hlookup_v_xarg.symm.trans hself)
      subst hv
      exact harg_cvcr
    · have hlookup_cap : (VarTypeEnv.ofCaptured σcap).lookup y = some qt := by
        have hne_lookup :
            (VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt).lookup y =
              (VarTypeEnv.ofCaptured σcap).lookup y :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured σcap) x y argQt hy
        simpa [bodyCtx, hne_lookup] using hlookup
      have hlookup_v_cap : ρcap.lookup y = some v := by
        have hne := VarEnv_lookup_update_ne ρcap x y vArg hy
        simpa [hne] using hlookup_v
      exact hσcap_rec y qt v (list_lookup_of_ofCaptured_lookup σcap y qt hlookup_cap) hlookup_v_cap

private lemma consistentWithRegime_app_member_from_body
  (predSat : PredSat)
  (ctx bodyCtx : TypeContext)
  (result2 result1 src result3 : TypeResult) (qtSrc : QTyp)
  (cpre cbody cfinal : Config) (θpre θfinal : RealizationMap)
  (hpred_compat :
    ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt cpre.memory v ↔ qtypPredHolds predSat qt cfinal.memory v)
  (hsrc_eq : src = { result3 with qualType := qtSrc })
  (hμ_eq : cfinal.memory = cbody.memory)
  (hρ_eq : cfinal.varEnv = cpre.varEnv)
  (hlookup_back :
    ∀ k b,
      (ctxAfter ctx src).regime.lookup? k = some b →
      (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b)
  (hθext : wfExtendsMap θpre θfinal)
  (hpre :
    consistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) cpre.memory cpre.varEnv θpre)
  (hbody :
    consistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      (ctxAfter bodyCtx result3) cbody.memory cbody.varEnv θfinal) :
  consistentWithRegime predSat (ctxAfter ctx src).regime
    (ctxAfter ctx src) cfinal.memory cfinal.varEnv θfinal := by
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    have hlookup_body :
        (ctxAfter bodyCtx result3).memEnv.lookup l = some qt := by
      simpa [ctxAfter, hsrc_eq] using hlookup
    have hguard_body : qtypGuardTag qt = some k := by
      simpa [ctxAfter, hsrc_eq] using hguard
    have hRdef_body :
        (ctxAfter bodyCtx result3).regime.lookup? k ≠ none := by
      simpa [ctxAfter, hsrc_eq] using hRdef
    simpa [ctxAfter, hsrc_eq, hμ_eq] using
      hbody.1 l qt k hlookup_body hguard_body hRdef_body
  · intro y qt k hlookup hguard hRdef
    cases hk_src : (ctxAfter ctx src).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hk_src)
    | some b =>
        have hRdef_pre :
            (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k ≠ none := by
          intro hnone
          have hk_back := hlookup_back k b hk_src
          rw [hk_back] at hnone
          contradiction
        have hlookup_pre_ctx :
            (ctxAfter (ctxAfter ctx result2) result1).varEnv.lookup y = some qt := by
          simpa [ctxAfter] using hlookup
        have hvar_pre :=
          hpre.2.1 y qt k hlookup_pre_ctx hguard hRdef_pre
        have hvar_pre_mem :=
          varsRegime_transport_predHolds hpred_compat hvar_pre
        simpa [hρ_eq] using
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter (ctxAfter ctx result2) result1).regime)
            (R' := (ctxAfter ctx src).regime)
            (μ := cfinal.memory) (ρ := cpre.varEnv) (entry := (y, qt))
            hlookup_back hguard hk_src hvar_pre_mem
  · intro y qt v hlookup hlookup_v
    have hcvcr :=
      hpre.2.2 y qt v
        (by simpa [ctxAfter] using hlookup)
        (by simpa [hρ_eq] using hlookup_v)
    exact
      closureCapturedVarsRegime_transport_μ_θ hpred_compat hθext.1
        (closureCapturedVarsRegime_transport_lookup_back hlookup_back hcvcr)

private lemma consistentWithRegimeMasked_app_member_from_body
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx bodyCtx : TypeContext)
  (result2 result1 src result3 : TypeResult) (qtSrc : QTyp)
  (cpre cbody cfinal : Config) (θpre θfinal : RealizationMap)
  (hpred_compat :
    ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt cpre.memory v ↔ qtypPredHolds predSat qt cfinal.memory v)
  (hsrc_eq : src = { result3 with qualType := qtSrc })
  (hμ_eq : cfinal.memory = cbody.memory)
  (hρ_eq : cfinal.varEnv = cpre.varEnv)
  (hlookup_back :
    ∀ k b,
      (ctxAfter ctx src).regime.lookup? k = some b →
      (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b)
  (hθext : wfExtendsMap θpre θfinal)
  (hpre :
    consistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) cpre.memory cpre.varEnv θpre)
  (hbody :
    consistentWithRegimeMasked masked predSat (ctxAfter bodyCtx result3).regime
      (ctxAfter bodyCtx result3) cbody.memory cbody.varEnv θfinal) :
  consistentWithRegimeMasked masked predSat (ctxAfter ctx src).regime
    (ctxAfter ctx src) cfinal.memory cfinal.varEnv θfinal := by
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    have hlookup_body :
        (ctxAfter bodyCtx result3).memEnv.lookup l = some qt := by
      simpa [ctxAfter, hsrc_eq] using hlookup
    have hguard_body : qtypGuardTag qt = some k := by
      simpa [ctxAfter, hsrc_eq] using hguard
    have hRdef_body :
        (ctxAfter bodyCtx result3).regime.lookup? k ≠ none := by
      simpa [ctxAfter, hsrc_eq] using hRdef
    have hloc_body := hbody.1 l qt k hlookup_body hguard_body hRdef_body
    cases hloc_body with
    | inl hmasked =>
        exact Or.inl hmasked
    | inr hloc =>
        exact Or.inr (by simpa [ctxAfter, hsrc_eq, hμ_eq] using hloc)
  · intro y qt k hlookup hguard hRdef
    cases hk_src : (ctxAfter ctx src).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hk_src)
    | some b =>
        have hRdef_pre :
            (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k ≠ none := by
          intro hnone
          have hk_back := hlookup_back k b hk_src
          rw [hk_back] at hnone
          contradiction
        have hlookup_pre_ctx :
            (ctxAfter (ctxAfter ctx result2) result1).varEnv.lookup y = some qt := by
          simpa [ctxAfter] using hlookup
        have hvar_pre :=
          hpre.2.1 y qt k hlookup_pre_ctx hguard hRdef_pre
        cases hvar_pre with
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvar_pre =>
            have hvar_pre_mem :=
              varsRegime_transport_predHolds hpred_compat hvar_pre
            exact Or.inr <|
              (by
                simpa [hρ_eq] using
                  varsRegime_transport_active_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter (ctxAfter ctx result2) result1).regime)
                    (R' := (ctxAfter ctx src).regime)
                    (μ := cfinal.memory) (ρ := cpre.varEnv) (entry := (y, qt))
                    hlookup_back hguard hk_src hvar_pre_mem)
  · intro y qt v hlookup hlookup_v
    have hcvcr :=
      hpre.2.2 y qt v
        (by simpa [ctxAfter] using hlookup)
        (by simpa [hρ_eq] using hlookup_v)
    exact
      closureCapturedVarsRegimeMasked_transport_μ_θ hpred_compat hθext.1
        (closureCapturedVarsRegimeMasked_transport_lookup_back hlookup_back hcvcr)

private lemma consistentWithRegime_app_arrow_body_start
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
  (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
  (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value)
  (hpredlaws : PredSatLaws predSat tm)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmono1 : Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime')
  (hθext : wfExtendsMap θ_arg θ)
  (hcwr :
    consistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hval_arg :
    valueConsistentWithRegime predSat (ctxAfter ctx result2).regime
      result2.qualType μ_arg θ_arg vArg)
  (hval_fun :
    valueConsistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      result1.qualType μ θ (Value.closure x body ρcap)) :
  ∃ σcap,
    FnTClosure.regular x body σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    let bodyCtx : TypeContext :=
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        tagEnv := result1.tagEnv'
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' }
    consistentWithRegime predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  rcases valueConsistentWithRegime_closureCapturedVarsRegime hval_fun with ⟨hdeep_fun⟩
  cases hdeep_fun with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x body ρcap)
  | closure xp bp rp σ s1 s2 pp tcl hveq hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.arrow s1 s2 pp tcl = ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      have hvars_arg :
          ∀ k,
            qtypGuardTag ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ = some k →
            result1.regime'.lookup? k ≠ none →
            varsRegime predSat result1.regime' μ
              (ρcap.update x vArg) (x, ⟨etyp2, joinPoison ctx.pc p2, pred2⟩) := by
        intro k hguard hRdef
        have hval_arg_e2 :
            valueConsistentWithRegime predSat (ctxAfter ctx result2).regime
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ_arg θ_arg vArg :=
          valueConsistentWithRegime_transport_pred
            (predSat := predSat) (R := (ctxAfter ctx result2).regime)
            (qt := result2.qualType)
            (qt' := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (μ := μ_arg) (θ := θ_arg) (v := vArg)
            (by simp [hqt2]) (hetyp := by simp [hqt2]) hval_arg
        have hval_arg_e1 :=
          valueConsistentWithRegime_monotone hmono1 hval_arg_e2
        exact
          varsRegime_transport_predHolds
            (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
            (varsRegime_of_valueConsistentWithRegime_active
              (predSat := predSat) (R := result1.regime')
              (μ := μ_arg) (ρ := ρcap.update x vArg)
              (x := x) (qt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
              (v := vArg) (k := k)
              (by simp [VarEnv.update, VarEnv.lookup])
              hguard hRdef hval_arg_e1)
      have harg_cvcr :
          closureCapturedVarsRegime predSat result1.regime'
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ θ vArg :=
        closureCapturedVarsRegime_transport_μ_θ
          (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
          hθext.1
          (closureCapturedVarsRegime_monotone hmono1
            (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
              (valueConsistentWithRegime_closureCapturedVarsRegime hval_arg)))
      have hσcap_rec :
          ∀ y qt v,
            σ.lookup y = some qt →
            ρcap.lookup y = some v →
            closureCapturedVarsRegime predSat result1.regime' qt μ θ v := by
        intro y qt v hy hv
        exact closureCapturedVarsRegime.intro (hrec y qt v hy hv)
      refine ⟨σ, hmem, hP.2, ?_⟩
      simpa using
        consistentWithRegime_app_closure_body_start
          (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma consistentWithRegimeMasked_app_arrow_body_start
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
  (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
  (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value)
  (hpredlaws : PredSatLaws predSat tm)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmono1 : Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime')
  (hθext : wfExtendsMap θ_arg θ)
  (hcwr :
    consistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hval_arg :
    valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx result2).regime
      result2.qualType μ_arg θ_arg vArg)
  (hval_fun :
    valueConsistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      result1.qualType μ θ (Value.closure x body ρcap)) :
  ∃ σcap,
    FnTClosure.regular x body σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    let bodyCtx : TypeContext :=
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        tagEnv := result1.tagEnv'
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' }
    consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  cases valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_fun with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x body ρcap)
  | closure xp bp rp σ s1 s2 pp tcl hval hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hval
      obtain ⟨rfl, rfl, rfl⟩ := hval
      have htcl_eq : ETyp.arrow s1 s2 pp tcl = ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      have hvars_arg :
          ∀ k,
            qtypGuardTag ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ = some k →
            result1.regime'.lookup? k ≠ none →
            masked k ∨ varsRegime predSat result1.regime' μ
              (ρcap.update x vArg) (x, ⟨etyp2, joinPoison ctx.pc p2, pred2⟩) := by
        intro k hguard hRdef
        have hval_arg_e2 :
            valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx result2).regime
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ_arg θ_arg vArg :=
          valueConsistentWithRegimeMasked_transport_pred
            (masked := masked) (predSat := predSat) (R := (ctxAfter ctx result2).regime)
            (qt := result2.qualType)
            (qt' := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (μ := μ_arg) (θ := θ_arg) (v := vArg)
            (by simp [hqt2]) (hetyp := by simp [hqt2]) hval_arg
        have hval_arg_e1 :=
          valueConsistentWithRegimeMasked_monotone hmono1 hval_arg_e2
        have hvars_or :=
          varsRegime_of_valueConsistentWithRegimeMasked_active
            (masked := masked) (predSat := predSat) (R := result1.regime')
            (μ := μ_arg) (θ := θ_arg) (ρ := ρcap.update x vArg)
            (x := x) (qt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (v := vArg) (k := k)
            (by simp [VarEnv.update, VarEnv.lookup])
            hguard hRdef hval_arg_e1
        cases hvars_or with
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvars =>
            exact Or.inr <|
              varsRegime_transport_predHolds
                (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
                hvars
      have harg_cvcr :
          closureCapturedVarsRegimeMasked masked predSat result1.regime'
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ θ vArg :=
        closureCapturedVarsRegimeMasked_transport_μ_θ
          (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
          hθext.1
          (closureCapturedVarsRegimeMasked_monotone hmono1
            (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hqt2])
              (valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_arg)))
      have hσcap_rec :
          ∀ y qt v,
            σ.lookup y = some qt →
            ρcap.lookup y = some v →
            closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v := by
        intro y qt v hy hv
        exact hrec y qt v hy hv
      refine ⟨σ, hmem, hP.2, ?_⟩
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma consistentWithRegime_app_parrow_body_start
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
  (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
  (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value)
  (hpredlaws : PredSatLaws predSat tm)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmono1 : Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime')
  (hθext : wfExtendsMap θ_arg θ)
  (hcwr :
    consistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hval_arg :
    valueConsistentWithRegime predSat (ctxAfter ctx result2).regime
      result2.qualType μ_arg θ_arg vArg)
  (hval_fun :
    valueConsistentWithRegime predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      result1.qualType μ θ (Value.peClosure x body ρcap)) :
  ∃ σcap pbody,
    Expr.toPExpr? body = some pbody ∧
    PFnTClosure.regular x pbody σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    let bodyCtx : TypeContext :=
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        tagEnv := result1.tagEnv'
        pureCtx := true
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' }
    consistentWithRegime predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  rcases valueConsistentWithRegime_closureCapturedVarsRegime hval_fun with ⟨hdeep_fun⟩
  cases hdeep_fun with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x body ρcap)
  | closure _ _ _ _ _ _ _ _ _ hteq _ _ _ =>
      exfalso
      have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hteq.symm.trans hetyp1
      simp at this
  | peClosure xp bp pbody rp σ s1 s2 pp tcl hveq hteq hpure hmem hP hrec =>
      rw [Value.peClosure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.parrow s1 s2 pp tcl = ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      have hvars_arg :
          ∀ k,
            qtypGuardTag ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ = some k →
            result1.regime'.lookup? k ≠ none →
            varsRegime predSat result1.regime' μ
              (ρcap.update x vArg) (x, ⟨etyp2, joinPoison ctx.pc p2, pred2⟩) := by
        intro k hguard hRdef
        have hval_arg_e2 :
            valueConsistentWithRegime predSat (ctxAfter ctx result2).regime
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ_arg θ_arg vArg :=
          valueConsistentWithRegime_transport_pred
            (predSat := predSat) (R := (ctxAfter ctx result2).regime)
            (qt := result2.qualType)
            (qt' := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (μ := μ_arg) (θ := θ_arg) (v := vArg)
            (by simp [hqt2]) (hetyp := by simp [hqt2]) hval_arg
        have hval_arg_e1 :=
          valueConsistentWithRegime_monotone hmono1 hval_arg_e2
        exact
          varsRegime_transport_predHolds
            (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
            (varsRegime_of_valueConsistentWithRegime_active
              (predSat := predSat) (R := result1.regime')
              (μ := μ_arg) (ρ := ρcap.update x vArg)
              (x := x) (qt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
              (v := vArg) (k := k)
              (by simp [VarEnv.update, VarEnv.lookup])
              hguard hRdef hval_arg_e1)
      have harg_cvcr :
          closureCapturedVarsRegime predSat result1.regime'
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ θ vArg :=
        closureCapturedVarsRegime_transport_μ_θ
          (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
          hθext.1
          (closureCapturedVarsRegime_monotone hmono1
            (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
              (valueConsistentWithRegime_closureCapturedVarsRegime hval_arg)))
      have hσcap_rec :
          ∀ y qt v,
            σ.lookup y = some qt →
            ρcap.lookup y = some v →
            closureCapturedVarsRegime predSat result1.regime' qt μ θ v := by
        intro y qt v hy hv
        exact closureCapturedVarsRegime.intro (hrec y qt v hy hv)
      refine ⟨σ, pbody, hpure, hmem, hP.2, ?_⟩
      simpa using
        consistentWithRegime_app_closure_body_start
          (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr

private lemma consistentWithRegimeMasked_app_parrow_body_start
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
  (x : Name) (body : Expr) (ρpre ρcap : VarEnv)
  (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value)
  (hpredlaws : PredSatLaws predSat tm)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmono1 : Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime')
  (hθext : wfExtendsMap θ_arg θ)
  (hcwr :
    consistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ)
  (hval_arg :
    valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx result2).regime
      result2.qualType μ_arg θ_arg vArg)
  (hval_fun :
    valueConsistentWithRegimeMasked masked predSat (ctxAfter (ctxAfter ctx result2) result1).regime
      result1.qualType μ θ (Value.peClosure x body ρcap)) :
  ∃ σcap pbody,
    Expr.toPExpr? body = some pbody ∧
    PFnTClosure.regular x pbody σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    let bodyCtx : TypeContext :=
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        tagEnv := result1.tagEnv'
        pureCtx := true
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' }
    consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ (ρcap.update x vArg) θ := by
  cases valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_fun with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x body ρcap)
  | closure _ _ _ _ _ _ _ _ _ hteq _ _ _ =>
      exfalso
      have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hteq.symm.trans hetyp1
      simp at this
  | peClosure xp bp pbody rp σ s1 s2 pp tcl hval hteq hpure hmem hP hrec =>
      rw [Value.peClosure.injEq] at hval
      obtain ⟨rfl, rfl, rfl⟩ := hval
      have htcl_eq : ETyp.parrow s1 s2 pp tcl = ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      have hvars_arg :
          ∀ k,
            qtypGuardTag ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ = some k →
            result1.regime'.lookup? k ≠ none →
            masked k ∨ varsRegime predSat result1.regime' μ
              (ρcap.update x vArg) (x, ⟨etyp2, joinPoison ctx.pc p2, pred2⟩) := by
        intro k hguard hRdef
        have hval_arg_e2 :
            valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx result2).regime
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ_arg θ_arg vArg :=
          valueConsistentWithRegimeMasked_transport_pred
            (masked := masked) (predSat := predSat) (R := (ctxAfter ctx result2).regime)
            (qt := result2.qualType)
            (qt' := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (μ := μ_arg) (θ := θ_arg) (v := vArg)
            (by simp [hqt2]) (hetyp := by simp [hqt2]) hval_arg
        have hval_arg_e1 :=
          valueConsistentWithRegimeMasked_monotone hmono1 hval_arg_e2
        have hvars_or :=
          varsRegime_of_valueConsistentWithRegimeMasked_active
            (masked := masked) (predSat := predSat) (R := result1.regime')
            (μ := μ_arg) (θ := θ_arg) (ρ := ρcap.update x vArg)
            (x := x) (qt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
            (v := vArg) (k := k)
            (by simp [VarEnv.update, VarEnv.lookup])
            hguard hRdef hval_arg_e1
        cases hvars_or with
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvars =>
            exact Or.inr <|
              varsRegime_transport_predHolds
                (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
                hvars
      have harg_cvcr :
          closureCapturedVarsRegimeMasked masked predSat result1.regime'
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ μ θ vArg :=
        closureCapturedVarsRegimeMasked_transport_μ_θ
          (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ μ_arg μ)
          hθext.1
          (closureCapturedVarsRegimeMasked_monotone hmono1
            (closureCapturedVarsRegimeMasked_transport_etyp (by simp [hqt2])
              (valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_arg)))
      have hσcap_rec :
          ∀ y qt v,
            σ.lookup y = some qt →
            ρcap.lookup y = some v →
            closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v := by
        intro y qt v hy hv
        exact hrec y qt v hy hv
      refine ⟨σ, pbody, hpure, hmem, hP.2, ?_⟩
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr

private lemma valueConsistentWithRegime_app_body_result_member
  (predSat : PredSat)
  (ctx bodyCtx : TypeContext) (src result3 : TypeResult)
  (p p1 : Poison) (μ_src μ_body : Memory) (θ : RealizationMap) (v : Value)
  (hsrc :
    src =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
  (hμ : μ_src = μ_body)
  (hval :
    valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      result3.qualType μ_body θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx src).regime src.qualType μ_src θ v := by
  have hval_first :
      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
        (normalizeAppResultByProvenance (joinPoison p1 p)
          { result3.qualType with
            poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
        μ_body θ v := by
    unfold normalizeAppResultByProvenance
    split
    · have hcap_src : closureCapturedVarsRegime predSat (ctxAfter bodyCtx result3).regime
          result3.qualType μ_body θ v := by
        exact valueConsistentWithRegime_closureCapturedVarsRegime hval
      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag])
        (closureCapturedVarsRegime_transport_etyp (by simp) hcap_src)
    · rename_i hp1p_false
      have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
      have hand : p1 = false ∧ p = false := (Bool.or_eq_false_iff).mp (by simpa [joinPoison] using hp1p)
      rw [hand.1, hand.2]
      simp only [joinPoison, Bool.false_or]
      set qt' : QTyp := { result3.qualType with poison := joinPoison false result3.qualType.poison } with hqt'_def
      cases hval with
      | noTag htag hcap =>
          exact valueConsistentWithRegime.noTag
            (show qtypGuardTag qt' = none by simp [qtypGuardTag, hqt'_def]; exact htag)
            (closureCapturedVarsRegime_transport_pred hcap)
      | guardOnly_ok k hgo hcap =>
          exact valueConsistentWithRegime.guardOnly_ok k
            (show qt'.pred = Predicate.guardOnly k from hgo)
            (closureCapturedVarsRegime_transport_pred hcap)
      | notInRegime k htag hlookup hcap =>
          exact valueConsistentWithRegime.notInRegime k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (closureCapturedVarsRegime_transport_pred hcap)
      | inRegimeTrue k htag hlookup hpred hcap =>
          exact valueConsistentWithRegime.inRegimeTrue k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (qtypPredHolds_transport_pred (qt := result3.qualType) (qt' := qt')
              (show result3.qualType.pred = qt'.pred from rfl) hpred)
            (closureCapturedVarsRegime_transport_pred hcap)
      | inRegimeFalse k htag hlookup hnpred hcap =>
          exact valueConsistentWithRegime.inRegimeFalse k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (fun habs => hnpred (qtypPredHolds_transport_pred (qt := qt') (qt' := result3.qualType)
              (show qt'.pred = result3.qualType.pred from rfl) habs))
            (closureCapturedVarsRegime_transport_pred hcap)
  simpa [ctxAfter, hsrc, hμ] using hval_first

-- Inversion for regular closures: from
-- `applyFnTClosure (FnTClosure.regular x body tenv) ... fuel = .ok first`,
-- extract that the application ran with positive fuel.
--
-- Suggested proof strategy:
-- unfold `applyFnTClosure` and split on fuel.
private lemma applyFnTClosure_ok_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          -- r = { result3 with qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt }
          -- ctxAfter ctx r has varEnv = ctx.varEnv, memEnv = result3.memEnv'
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          -- Body context wfTagMeaningCtx
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          -- Body preservation gives wfTagMeaningCtx for post-body context
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            typecheckExpr_preserves_wfTagMeaningCtx tm bodyCtx body fuel' result3 hwf_body htcBody'
          -- Mix: inVar from hctxTm1 (ctx.varEnv), inMem from hIH (result3.memEnv')
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec effects capturedEnv =>
    exact applyFnTClosure_extern_ok_wfTagMeaningCtx tm ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 fuel x retSpec effects capturedEnv r hctxTm1 happly

private lemma applyFnTClosure_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      -- Split on typecheckExpr result in happly
      split at happly
      · -- error case: happly is Except.error = .ok, contradiction
        exact absurd happly (Except.error_ne_ok _ _)
      · -- ok case
        next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          have hreg_body : regimeConsistentWithCtx bodyCtx := by
            simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using hreg1
          have hIH := typecheckExpr_preserves_regimeConsistentWithCtx bodyCtx body fuel' result3 hreg_body htcBody'
          apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
          · simp [ctxAfter]
          · simp [ctxAfter]
          · simp [ctxAfter]
          · exact hIH
  | extern x retSpec effects capturedEnv =>
    have htag := applyFnTClosure_extern_tagEnv_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel x retSpec effects capturedEnv happly
    have hreg := applyFnTClosure_extern_regime_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel x retSpec effects capturedEnv happly
    simp only [regimeConsistentWithCtx, ctxAfter]
    rw [htag, hreg]
    exact hreg1

private lemma applyFnTClosure_ok_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          -- r.qualType = normalizeAppResultByProvenance (joinPoison p1 p) { result3.qualType with poison := taintedPoison }
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact typecheckExpr_preserves_QTypRespectsTagMeaning tm bodyCtx body fuel' result3 hwf_body htcBody'
          -- Transport through normalizeAppResultByProvenance
          simp only [normalizeAppResultByProvenance]
          split
          · -- p1 = true: pred becomes noPred
            intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · -- p1 = false: same etyp and pred, only poison differs
            intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec effects capturedEnv =>
    have hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt := by
      intro name qt hmem
      intro qtDeep k d hinqDeep hqd
      have hmemCap : (name, qt) ∈ fnCapturedEnv (FnTClosure.extern x retSpec effects capturedEnv) :=
        by simpa [fnCapturedEnv] using hmem
      have hroot : QTypInQTyp qt result1.qualType :=
        QTypInQTyp.in_arrow qt result1.qualType st1 st2 p tcls
          (FnTClosure.extern x retSpec effects capturedEnv) name hetyp1 hmem_tcl hmemCap
      exact hresTm1 (QTypInQTyp.trans qtDeep qt result1.qualType hinqDeep hroot) hqd
    have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
      QTypRespectsTagMeaning_transport_etyp_pred tm
        ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        hargTm rfl rfl
    intro qt' k d hinq hqd
    exact (applyFnTClosure_extern_ok_qualTypeRespects tm ctx st1 st2 p p1 argEtyp argPoison
      argPred result1 fuel x retSpec effects capturedEnv r hctxTm1 hcapTm hargTm' happly) hinq hqd

private lemma mapM_applyFnTClosure_forall_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  simpa using
    applyFnTClosure_ok_wfTagMeaningCtx
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma mapM_applyFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  simpa using
    applyFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma mapM_applyFnTClosure_forall_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_QTypRespectsTagMeaning
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma joinTypeResults_tagEnvConsistentWithRegime
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime :=
  joinTypeResults_tagEnvConsistentWithRegime' ctx first rest res h_join h_first h_rest

-- Any deep sub-type of a tag-meaning-respecting type also respects tag meaning.
private lemma QTypRespectsTagMeaning_sub (tm : TagMeaning) {qt qt' : QTyp}
    (h : QTypRespectsTagMeaning tm qt) (hinq : QTypInQTyp qt' qt) :
    QTypRespectsTagMeaning tm qt' :=
  fun hinq'' hqd => h (QTypInQTyp.trans _ qt' qt hinq'' hinq) hqd

private lemma joinTypeResults_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : QTypRespectsTagMeaning tm first.qualType)
  (h_rest : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType) :
  QTypRespectsTagMeaning tm res.qualType := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  -- Fold invariant: the accumulated (etyp, poison, pred) satisfies QTypRespectsTagMeaning.
  have h_fold_qtm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        QTypRespectsTagMeaning tm ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ →
        (∀ r ∈ rs', QTypRespectsTagMeaning tm r.qualType) →
        QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold; exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx : QTypRespectsTagMeaning tm x.qualType := hrs x (by simp)
            -- Use term-mode proof to avoid simpa + @[reducible] metavariable issues
            have hacc1 : QTypRespectsTagMeaning tm ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ :=
              QTypRespectsTagMeaning_joinStep tm acc.1 resEtyp acc.2.2.1 resPoison
                acc.2.2.2.1 resPred hacc (hqx ▸ hx)
            have hrs_tail : ∀ r ∈ xs, QTypRespectsTagMeaning tm r.qualType := by
              intro r hr; exact hrs r (by simp [hr])
            -- Use show to force correct return type; avoids @[reducible] expansion issues
            show QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  -- Apply the fold lemma and handle the finalPred adjustment.
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck : (List.foldlM (fun x result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
          if beqETypSignature etyp resEtyp = false then
            Except.error (toString "Closure alternatives produced incompatible result types: " ++
              toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
          else Except.ok ()) () rest : Except String Unit) with
      | error _ => erw [hcheck] at h_join; simp at h_join
      | ok _ =>
          erw [hcheck] at h_join; simp at h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ => erw [hfold] at h_join; simp at h_join
          | ok a =>
              erw [hfold] at h_join; simp at h_join; subst res
              -- Pre-compute to avoid metavariable issues with simpa + reducible def
              have h_first_qtm : QTypRespectsTagMeaning tm ⟨etyp, poison, pred⟩ :=
                hqt ▸ h_first
              -- Get QTypRespectsTagMeaning for the fold result
              have h_fold_result :
                  QTypRespectsTagMeaning tm ⟨a.1, a.2.2.1, a.2.2.2.1⟩ :=
                h_fold_qtm rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_qtm h_rest
              -- Decompose a and reduce tuple projections
              obtain ⟨e, m, p, pred', te, r, l, t⟩ := a
              simp only at h_fold_result ⊢
              -- Case-split on the etyp to reduce the match and pick the right transport lemma.
              -- Each branch uses `show` to reduce `match e with ...` to a concrete pred.
              cases e with
              | int =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.int, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.int, p, pred'⟩ ⟨ETyp.int, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | bool =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.bool, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.bool, p, pred'⟩ ⟨ETyp.bool, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | unit =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.unit, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.unit, p, pred'⟩ ⟨ETyp.unit, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | string =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.string, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.string, p, pred'⟩ ⟨ETyp.string, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | ref ls =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.ref ls, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.ref ls, p, pred'⟩ ⟨ETyp.ref ls, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | arrow st1 st2 pa tcls =>
                  -- finalPred = noPred for arrow types; use noGuard transport
                  show QTypRespectsTagMeaning tm
                    ⟨ETyp.arrow st1 st2 pa tcls, joinPoison ctx.pc p, Predicate.noPred⟩
                  exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                    ⟨ETyp.arrow st1 st2 pa tcls, p, pred'⟩
                    ⟨ETyp.arrow st1 st2 pa tcls, joinPoison ctx.pc p, Predicate.noPred⟩
                    h_fold_result rfl (by simp [qtypGuardDesc?])
              | parrow st1 st2 pa ptcls =>
                  -- finalPred = noPred for parrow types; use noGuard transport
                  show QTypRespectsTagMeaning tm
                    ⟨ETyp.parrow st1 st2 pa ptcls, joinPoison ctx.pc p, Predicate.noPred⟩
                  exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                    ⟨ETyp.parrow st1 st2 pa ptcls, p, pred'⟩
                    ⟨ETyp.parrow st1 st2 pa ptcls, joinPoison ctx.pc p, Predicate.noPred⟩
                    h_fold_result rfl (by simp [qtypGuardDesc?])
-- Inversion for regular pure-closures: from
-- `applyPFnTClosure (PFnTClosure.regular x pbody tenv) ... fuel = .ok first`,
-- extract that the application ran with positive fuel.
private lemma applyPFnTClosure_regular_structure
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate) (result2 : TypeResult) (fuel : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (_happly : applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok first) :
  ∃ fuelBody, fuel = Nat.succ fuelBody := by
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at _happly
  | succ fuelBody =>
      exact ⟨fuelBody, rfl⟩

-- Inversion for regular pure-closures: successful application exposes the body typing
-- derivation and successful return-type subtype check.

-- Specialized extraction for pure-closure application maps used in `stepFR_app`.
private lemma applyPFnTClosure_ok_of_mem_mapM
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult) (tcl : PFnTClosure)
  (hmap : List.mapM
      (fun tcl' => applyPFnTClosure tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      tcls = .ok results)
  (hmem : tcl ∈ tcls) :
  ∃ r, r ∈ results ∧
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r := by
  simpa using
    (list_mapM_ok_mem_input_exists_output
      (f := fun tcl' => applyPFnTClosure tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      (xs := tcls) (ys := results) (x := tcl) hmap hmem)

-- Combined extraction for regular pure-closures from a successful application map.
-- Gives the selected closure's successful application together with body-typing inversion.
private lemma applyPFnTClosure_regular_inv_of_mapM_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (hmap : List.mapM
      (fun tcl' => applyPFnTClosure tcl' st1 st2 p p1 argEtyp argPoison argPred ctx bodyState fuel)
      tcls = .ok results)
  (hmem : PFnTClosure.regular x pbody tenv ∈ tcls) :
  ∃ fuelBody first result3,
    applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx bodyState fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := bodyState.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := bodyState.tagEnv'
        pureCtx := true
        nextTag := bodyState.nextTag'
        nextLoc := bodyState.nextLoc'
        regime := bodyState.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases applyPFnTClosure_ok_of_mem_mapM
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel tcls results
      (PFnTClosure.regular x pbody tenv) hmap hmem with
    ⟨first, _hfirst_mem, happly⟩
  rcases applyPFnTClosure_regular_structure
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel x pbody tenv first happly with
    ⟨fuelBody, hfuel⟩
  have happly_succ :
      applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx bodyState (Nat.succ fuelBody) = .ok first := by
    simpa [hfuel] using happly
  rcases applyPFnTClosure_regular_inv
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuelBody x pbody tenv first happly_succ with
    ⟨result3, htc_body, hsub, hfirst_eq⟩
  exact ⟨fuelBody, first, result3, happly, hfuel, htc_body, hsub, hfirst_eq⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Parrow (PFnTClosure) versions of the per-member preservation lemmas.
-- These mirror the FnTClosure versions above, using applyPFnTClosure.
-- ═══════════════════════════════════════════════════════════════════════════


private lemma applyPFnTClosure_regular_body_wfTypeResult
  (ctx : TypeContext) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuelBody : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (hwf1 : wfTypeResult result1)
  (hCaptFull : CapturedEnvRefLocsFullBounded tenv result1.nextLoc')
  (hArgRL : etypRefLocsBounded argEtyp result1.nextLoc')
  (hArgCRL : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
  (ctx'' : TypeContext)
  (hctx'' : ctx'' = { ctx with
      pc := joinPoison p (joinPoison ctx.pc p1)
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      tagEnv := result1.tagEnv'
      pureCtx := true
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' })
  (result3 : TypeResult)
  (htc : typecheckExpr ctx'' (PExpr.toExpr pbody) fuelBody = .ok result3) :
  wfTypeResult result3 := by
  have hwf_ctx'' : wfTypeContext ctx'' := by
    rw [hctx'']
    simp only [wfTypeContext]
    exact ⟨hwf1,
      varEnvRefLocsBounded_update
        (varEnvRefLocsBounded_ofCaptured (capturedEnvRefLocsBounded_of_fullBounded_refLocs hCaptFull)) hArgRL,
      varEnvClosuresCapturedRefLocsBounded_update
        (varEnvClosuresCapturedRefLocsBounded_ofCaptured hCaptFull) hArgCRL⟩
  exact typecheckExpr_preserves_wfTypeResult ctx'' (PExpr.toExpr pbody) fuelBody result3 hwf_ctx''
    (by simpa [typecheck] using htc)

private lemma applyPFnTClosure_ok_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf1 : wfTypeResult result1)
  (tcl : PFnTClosure)
  (hcaptLocs : match tcl with
    | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
    | .extern _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
  (hArgRL : etypRefLocsBounded argEtyp result1.nextLoc')
  (hArgCRL : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
  (r : TypeResult)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTypeResult r := by
  cases fuel with
  | zero =>
    unfold applyPFnTClosure at happly
    simp at happly
  | succ fuelBody =>
    cases tcl with
    | regular x pbody tenv =>
      rcases applyPFnTClosure_regular_inv ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuelBody
          x pbody tenv r (by simpa using happly) with
        ⟨result3, htc_body, _hsub, hfirst⟩
      have hwf3 := applyPFnTClosure_regular_body_wfTypeResult ctx p p1 argEtyp argPoison argPred
        result1 fuelBody x pbody tenv hwf1
        hcaptLocs hArgRL hArgCRL
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
        rfl result3 htc_body
      rw [hfirst]
      exact hwf3
    | extern x retSpec capturedEnv =>
      -- For PFnTClosure.extern, memEnv' is unchanged; nextLoc' = result1.nextLoc' in all branches
      unfold applyPFnTClosure at happly
      simp only [bind, Except.bind] at happly
      split at happly
      · -- ExternReturn.simple: collectAndAllocExternTags, resolveSyntaxPred, returnSpecToQTyp
        split at happly
        · simp at happly
        · split at happly
          · simp at happly
          · -- returnSpecToQTyp result is in scope as the innermost match
            -- use simp to propagate; we need nextLoc' from returnSpecToQTyp = result1.nextLoc'
            split at happly
            · simp at happly
            · simp only [pure, Except.pure] at happly
              -- happly: Except.ok { memEnv' = result1.memEnv', nextLoc' = retQtPair.2 } = Except.ok r
              -- Extract r = { ... } from happly, then use returnSpecToQTyp to get nextLoc'
              have hr := Except.ok.inj happly
              -- Get the returnSpecToQTyp equation from the split context
              -- It's in context as something like heq✝ : returnSpecToQTyp typ₀ poi pred nextLoc' = ok retQtPair
              -- Use 'next' with wildcards to find the right hypothesis name
              -- and show retQtPair.2 = result1.nextLoc'
              simp only [wfTypeResult] at hwf1 ⊢
              intro l hl
              -- r.memEnv' = result1.memEnv' (from hr, since both sides have result1.memEnv')
              have hmemr : r.memEnv' = result1.memEnv' := by
                have := congrArg TypeResult.memEnv' hr.symm; simpa using this
              -- r.nextLoc' = retQtPair.2 (from hr.symm)
              have hnlocr : r.nextLoc' = _ := congrArg TypeResult.nextLoc' hr.symm
              -- retQtPair.2 = result1.nextLoc' from the returnSpecToQTyp equation
              -- All equations in scope; use simp_all after case-split on Typ
              rw [← hr]; simp only []
              -- Now goal is l < retQtPair.2; use hwf1 l and hnloc
              -- We need: forall non-ref Typ, returnSpecToQTyp returns nextLoc unchanged
              -- Derive this by case-splitting on the actual return type Typ in scope
              -- rename_i to get the returnSpecToQTyp equation
              rename_i _ _ _ _ _ _ _ _ _ retQtPair hrsq
              -- hrsq : returnSpecToQTyp a✝¹ a✝ v✝ result1.nextLoc' = Except.ok retQtPair
              have hnloc : retQtPair.2 = result1.nextLoc' := by
                unfold returnSpecToQTyp at hrsq
                split at hrsq
                · simp only [pure, Except.pure, bind, Except.bind] at hrsq
                  exact (congrArg Prod.snd (Except.ok.inj hrsq)).symm
                · simp only [pure, Except.pure, bind, Except.bind] at hrsq
                  exact (congrArg Prod.snd (Except.ok.inj hrsq)).symm
                · simp only [pure, Except.pure, bind, Except.bind] at hrsq
                  exact (congrArg Prod.snd (Except.ok.inj hrsq)).symm
                · simp only [pure, Except.pure, bind, Except.bind] at hrsq
                  exact (congrArg Prod.snd (Except.ok.inj hrsq)).symm
                · simp [Functor.map, Except.map] at hrsq
                · simp [Functor.map, Except.map] at hrsq
              rw [hnloc]; exact hwf1 l (by rwa [hmemr] at hl)
      · -- ExternReturn.nestedFn: nextLoc' = result1.nextLoc', memEnv' = result1.memEnv'
        simp only [pure, Except.pure] at happly
        cases happly
        exact hwf1
      · -- ExternReturn.nestedPfn: nextLoc' = result1.nextLoc', memEnv' = result1.memEnv'
        simp only [pure, Except.pure] at happly
        cases happly
        exact hwf1

private lemma applyPFnTClosure_ok_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            typecheckExpr_preserves_wfTagMeaningCtx tm bodyCtx (PExpr.toExpr body) fuel' result3 hwf_body htcBody'
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec capturedEnv =>
    have hmem := applyPFnTClosure_extern_memEnv_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel x retSpec capturedEnv happly
    simp only [wfTagMeaningCtx, ctxAfter] at hctxTm1 ⊢
    rwa [hmem]

private lemma applyPFnTClosure_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hreg_body : regimeConsistentWithCtx bodyCtx := by
            simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using hreg1
          have hIH := typecheckExpr_preserves_regimeConsistentWithCtx bodyCtx (PExpr.toExpr body) fuel' result3 hreg_body htcBody'
          apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
          · simp [ctxAfter]
          · simp [ctxAfter]
          · simp [ctxAfter]
          · exact hIH
  | extern x retSpec capturedEnv =>
    have htag := applyPFnTClosure_extern_tagEnv_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel x retSpec capturedEnv happly
    have hreg := applyPFnTClosure_extern_regime_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel x retSpec capturedEnv happly
    simp only [regimeConsistentWithCtx, ctxAfter]
    rw [htag, hreg]
    exact hreg1

private lemma applyPFnTClosure_ok_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact typecheckExpr_preserves_QTypRespectsTagMeaning tm bodyCtx (PExpr.toExpr body) fuel' result3 hwf_body htcBody'
          simp only [normalizeAppResultByProvenance]
          split
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec capturedEnv =>
    have hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt := by
      intro name qt hmem qt' k d hinq' hqd'
      exact hresTm1
        (QTypInQTyp.trans qt' qt result1.qualType hinq'
          (QTypInQTyp.in_parrow qt result1.qualType st1 st2 p tcls
            (PFnTClosure.extern x retSpec capturedEnv) name hetyp1 hmem_tcl hmem))
        hqd'
    have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
      QTypRespectsTagMeaning_transport_etyp_pred tm
        ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        hargTm rfl rfl
    intro qt' k d hinq hqd
    exact (applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_corollary tm ctx st1 st2 p p1 argEtyp
      argPoison argPred result1 fuel x retSpec capturedEnv r hctxTm1 hcapTm hargTm' happly) hinq hqd

private lemma mapM_applyPFnTClosure_forall_wfTypeResult'
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf_result1 : wfTypeResult result1)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (hcaptAll : ∀ tcl ∈ tcls, match tcl with
    | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
    | .extern _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
  (hArgRL : etypRefLocsBounded argEtyp result1.nextLoc')
  (hArgCRL : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTypeResult r := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  simpa using
    applyPFnTClosure_ok_wfTypeResult
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel)
      hwf_result1 (tcl := tcl) (hcaptLocs := hcaptAll tcl htcl_mem)
      (hArgRL := hArgRL) (hArgCRL := hArgCRL) (r := r) happly

private lemma mapM_applyPFnTClosure_forall_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  simpa using
    applyPFnTClosure_ok_wfTagMeaningCtx
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma mapM_applyPFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  simpa using
    applyPFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_QTypRespectsTagMeaning
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

-- Body context instantiation: establishing runtimeInstantiatesCtx for the closure body
-- context. Requires strengthening valueHasETyp.closure (henv) to existential form.
--
-- Suggested proof strategy:
-- use `valueHasETyp.closure` to recover captured-env typing, then build the two
-- conjuncts of `runtimeInstantiatesCtx` for the body context:
-- 1) location/memory part is inherited from `_hric` (memEnv is `result2.memEnv'`);
-- 2) variable part combines captured bindings + updated argument binding.
--
-- Helpful already-proven ingredients:
-- * `runtimeInstantiatesCtx_of_closure_env` in this file (for env substitution),
-- * var-env update lookup lemmas from `RegimeConsistency.lean`.
private lemma runtimeInstantiatesCtx_closure_body
  (ctx : TypeContext) (result2 : TypeResult) (x : Name) (tenv : CapturedVarEnv)
  (argQt : QTyp) (argVal : Value) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hric : runtimeInstantiatesCtx (ctxAfter ctx result2) μ ρ θ)
  (harg : valueHasETyp θ argVal argQt.etyp)
  (hcap : ∀ y qt, (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ∃ v, ρ.lookup y = some v ∧ valueHasETyp θ v qt.etyp) :
  let bodyVarEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x argQt
  let bodyCtx : TypeContext := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime', varEnv := bodyVarEnv }
  runtimeInstantiatesCtx bodyCtx μ (VarEnv.update ρ x argVal) θ := by
  intro bodyVarEnv bodyCtx
  constructor
  · intro l a hθ
    -- memEnv/heap obligations are inherited from the post-`e2` context.
    exact hric.1 l a hθ
  · intro y qt hlookup
    have hlookup_var : bodyVarEnv.lookup y = some qt := by
      simpa [bodyCtx] using hlookup
    by_cases hyx : y = x
    · subst y
      refine ⟨argVal, ?_⟩
      constructor
      · simp [VarEnv.update, VarEnv.lookup]
      · have hx_lookup : bodyVarEnv.lookup x = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured tenv) x argQt
        have hqt : qt = argQt := by
          have : some qt = some argQt := by
            calc
              some qt = bodyVarEnv.lookup x := by symm; exact hlookup_var
              _ = some argQt := hx_lookup
          exact Option.some.inj this
        simpa [hqt] using harg
    · have hlookup_cap : (VarTypeEnv.ofCaptured tenv).lookup y = some qt := by
        have hne_lookup :
            bodyVarEnv.lookup y = (VarTypeEnv.ofCaptured tenv).lookup y :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured tenv) x y argQt hyx
        simpa [hne_lookup] using hlookup_var
      rcases hcap y qt hlookup_cap with ⟨v, hlookupρ, hvtyp⟩
      refine ⟨v, ?_⟩
      constructor
      · have hne_lookup :
            (VarEnv.update ρ x argVal).lookup y = ρ.lookup y :=
          VarEnv_lookup_update_ne ρ x y argVal hyx
        simpa [hne_lookup] using hlookupρ
      · exact hvtyp

-- Bridge from closure typing's captured-env implication (`henv`) to the existential
-- payload required by `runtimeInstantiatesCtx_closure_body`, under an explicit
-- captured-env domain coverage assumption.
--
-- This isolates the known blocker:
-- `valueHasETyp.closure` gives only
--   `tenv.lookup y = some qt → env.lookup y = some v → valueHasETyp ...`
-- whereas runtime instantiation needs
--   `tenv.lookup y = some qt → ∃ v, env.lookup y = some v ∧ valueHasETyp ...`.
--
-- The missing ingredient is exactly `_hcover`: every typed captured binding is
-- actually present in the runtime captured environment.
private lemma runtimeInstantiatesCtx_closure_body_from_henv
  (ctx : TypeContext) (result2 : TypeResult) (x : Name) (tenv : CapturedVarEnv)
  (argQt : QTyp) (argVal : Value) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hric : runtimeInstantiatesCtx (ctxAfter ctx result2) μ ρ θ)
  (harg : valueHasETyp θ argVal argQt.etyp)
  (henv : ∀ y qt v, (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ρ.lookup y = some v → valueHasETyp θ v qt.etyp)
  (hcover : ∀ y qt, (VarTypeEnv.ofCaptured tenv).lookup y = some qt → ∃ v, ρ.lookup y = some v) :
  let bodyVarEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x argQt
  let bodyCtx : TypeContext := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime', varEnv := bodyVarEnv }
  runtimeInstantiatesCtx bodyCtx μ (VarEnv.update ρ x argVal) θ := by
  apply runtimeInstantiatesCtx_closure_body
    (ctx := ctx) (result2 := result2) (x := x) (tenv := tenv)
    (argQt := argQt) (argVal := argVal) (μ := μ) (ρ := ρ) (θ := θ)
    hric harg
  intro y qt hlookup
  rcases hcover y qt hlookup with ⟨v, hlookupρ⟩
  exact ⟨v, hlookupρ, henv y qt v hlookup hlookupρ⟩

-- Extract per-member evidence from closureCapturedVarsRegime for a closure value.
-- Given that the value is a closure with arrow type, the deepValueQTypProperty
-- must use the .closure constructor, yielding σcap with regime, typing, and recursive
-- evidence. This avoids the σcap matching problem between valueHasETyp.closure
-- and closureCapturedVarsRegime.
private lemma closureCapturedVarsRegime_closure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (h : closureCapturedVarsRegime predSat R qt μ θ (Value.closure x body env)) :
    ∃ σcap,
      FnTClosure.regular x body σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (y : Name) (qt_y : QTyp) (v_y : Value),
        σcap.lookup y = some qt_y →
        env.lookup y = some v_y →
        closureCapturedVarsRegime predSat R qt_y μ θ v_y) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x body env)
  | closure xp bp rp σ s1 s2 pp tcl hveq hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.arrow s1 s2 pp tcl = ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      exact ⟨σ, hmem, hP.1, hP.2, fun y qt_y v_y hy hv =>
        closureCapturedVarsRegime.intro (hrec y qt_y v_y hy hv)⟩
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma closureCapturedVarsRegime_peClosure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
    (h : closureCapturedVarsRegime predSat R qt μ θ (Value.peClosure x body env)) :
    ∃ σcap pbody,
      Expr.toPExpr? body = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (y : Name) (qt_y : QTyp) (v_y : Value),
        σcap.lookup y = some qt_y →
        env.lookup y = some v_y →
        closureCapturedVarsRegime predSat R qt_y μ θ v_y) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x body env)
  | closure _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)
  | peClosure xp bp pbody ρ σ s1 s2 pp tcl hveq hteq hpure hmem hP hrec =>
      rw [Value.peClosure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.parrow s1 s2 pp tcl = ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      exact ⟨σ, pbody, hpure, hmem, hP.1, hP.2, fun y qt_y v_y hy hv =>
        closureCapturedVarsRegime.intro (hrec y qt_y v_y hy hv)⟩

private lemma join_transport_wfTagMeaningCtx
  (tm : TagMeaning) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : wfTagMeaningCtx tm (ctxAfter ctx first)) :
  wfTagMeaningCtx tm (ctxAfter ctx res) := by
  unfold wfTagMeaningCtx
  rw [ctxAfter]
  have h_first_env : EnvRespectsTagMeaning tm ctx.varEnv first.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using h_first
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  -- Guard descriptors in joinMemEnvsStrong are a subset of the left side's:
  -- single-sided entries get noPred (no guard); both-sided entries preserve guardClosure
  -- only on exact match (same as left). So only first member's EnvRespectsTagMeaning is needed.
  have h_fold_tm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        EnvRespectsTagMeaning tm ctx.varEnv acc.2.1 →
        EnvRespectsTagMeaning tm ctx.varEnv acc'.2.1 := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hacc1 : EnvRespectsTagMeaning tm ctx.varEnv (joinMemEnvsStrong acc.2.1 x.memEnv') :=
              EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv acc.2.1 x.memEnv' hacc
            exact ih _ hfold hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr etyp) ++
                        toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              exact h_fold_tm rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') a
                hfold h_first_env

private lemma join_transport_consistentWithRegime
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_mem_guarded_from_first :
    ∀ l qt k,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypGuardTag qt = some k →
      (ctxAfter ctx res).regime.lookup? k ≠ none →
      (ctxAfter ctx first).memEnv.lookup l = some qt)
  (h_first : consistentWithRegime predSat (ctxAfter ctx first).regime (ctxAfter ctx first) μ ρ θ) :
  consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  simp only [consistentWithRegime, ctxAfter]
  constructor
  · intro l qt k hlookup hguard hR'def
    have hlookup_first := h_mem_guarded_from_first l qt k hlookup hguard hR'def
    have hRdef : first.regime'.lookup? k ≠ none := h_regime_mono.2 k hR'def
    cases hk' : res.regime'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        cases hk : first.regime'.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h_eq := h_regime_mono.1 k b' hk
            cases h_eq with
            | inl heq =>
                have hb : b' = b := Option.some.inj (heq.symm.trans hk')
                have h_locsR := h_first.1 l qt k hlookup_first hguard hRdef
                exact locsRegime_monotone h_regime_mono hguard hk' h_locsR
            | inr h_none => simp [h_none] at hk'
  constructor
  · intro x qt k hlookup hguard hR'def
    have hRdef : first.regime'.lookup? k ≠ none := h_regime_mono.2 k hR'def
    cases hk' : res.regime'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        cases hk : first.regime'.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h_eq := h_regime_mono.1 k b' hk
            cases h_eq with
            | inl heq =>
                have hb : b' = b := Option.some.inj (heq.symm.trans hk')
                have h_varsR := h_first.2.1 x qt k hlookup hguard hRdef
                exact varsRegime_monotone h_regime_mono hguard hk' h_varsR
            | inr h_none => simp [h_none] at hk'
  · intro x qt v hlookup hlookup_v
    exact closureCapturedVarsRegime_monotone h_regime_mono
      (h_first.2.2 x qt v hlookup hlookup_v)



private lemma join_transport_agreeOnClean
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_clean_res_to_first :
    ∀ qt,
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      qtypCleanUnder (ctxAfter ctx first).regime qt)
  (h_mem_clean_from_first :
    ∀ l qt,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      (ctxAfter ctx first).memEnv.lookup l = some qt)
  (h_first : agreeOnClean predSat (ctxAfter ctx first).regime (ctxAfter ctx first) μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
  agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  simp only [agreeOnClean, ctxAfter]
  constructor
  · intro l qt hlookup hclean
    have hlookup_first := h_mem_clean_from_first l qt hlookup hclean
    have hclean_first := h_clean_res_to_first qt hclean
    have hagree_first := h_first.1 l qt hlookup_first hclean_first
    cases hagree_first with
    | both_unrealized _ _ hnone₀ hnone₁ =>
        exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
    | agree_values _ _ a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
        have hagree' := agreeValueUnder_clean_monotoneRegime h_regime_mono hclean hagree
        exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree'
  · intro x qt hlookup hclean
    have hclean_first := h_clean_res_to_first qt hclean
    have hagree_first := h_first.2 x qt hlookup hclean_first
    cases hagree_first with
    | both_none _ _ hnone₀ hnone₁ =>
        exact agreeVarUnder.both_none x qt hnone₀ hnone₁
    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
        have hagree' := agreeValueUnder_clean_monotoneRegime h_regime_mono hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'

private lemma join_transport_resultAgreesIfClean
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (qt : QTyp) (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_clean_res_to_first :
    qtypCleanUnder (ctxAfter ctx res).regime qt →
    qtypCleanUnder (ctxAfter ctx first).regime qt)
  (h_first : resultAgreesIfClean predSat (ctxAfter ctx first).regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁) :
  resultAgreesIfClean predSat (ctxAfter ctx res).regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hclean_res
  have hclean_first := h_clean_res_to_first hclean_res
  have hagree_first := h_first hclean_first
  exact agreeValueUnder_clean_monotoneRegime h_regime_mono hclean_res hagree_first

-- App-closure normalization transport stubs (`result3` -> `firstShared`).
private lemma valueConsistentWithRegime_transport_normalizeAppResultByProvenance
  (predSat : PredSat) (R : Regime) (p p1 : Poison) (qt : QTyp)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  valueConsistentWithRegime predSat R
    (normalizeAppResultByProvenance (joinPoison p1 p)
      { qt with poison := joinPoison p1 (joinPoison p qt.poison) }) μ θ v := by
  unfold normalizeAppResultByProvenance
  split
  · -- joinPoison p1 p = true: result has pred := noPred, etyp unchanged
    have hcap_src : closureCapturedVarsRegime predSat R qt μ θ v := by
      cases h with
      | noTag _ hcap => exact hcap
      | guardOnly_ok _ _ hcap => exact hcap
      | notInRegime _ _ _ hcap => exact hcap
      | inRegimeTrue _ _ _ _ hcap => exact hcap
      | inRegimeFalse _ _ _ _ hcap => exact hcap
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag])
      (closureCapturedVarsRegime_transport_etyp (by simp) hcap_src)
  · rename_i hp1p_false
    have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
    have hand : p1 = false ∧ p = false := (Bool.or_eq_false_iff).mp (by simpa [joinPoison] using hp1p)
    rw [hand.1, hand.2]
    simp only [joinPoison, Bool.false_or]
    set qt' : QTyp := { qt with poison := joinPoison false qt.poison } with hqt'_def
    cases h with
    | noTag htag hcap =>
        exact valueConsistentWithRegime.noTag
          (show qtypGuardTag qt' = none by simp [qtypGuardTag, hqt'_def]; exact htag)
          (closureCapturedVarsRegime_transport_pred hcap)
    | guardOnly_ok k hgo hcap =>
        exact valueConsistentWithRegime.guardOnly_ok k
          (show qt'.pred = Predicate.guardOnly k from hgo)
          (closureCapturedVarsRegime_transport_pred hcap)
    | notInRegime k htag hlookup hcap =>
        exact valueConsistentWithRegime.notInRegime k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (closureCapturedVarsRegime_transport_pred hcap)
    | inRegimeTrue k htag hlookup hpred hcap =>
        exact valueConsistentWithRegime.inRegimeTrue k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (qtypPredHolds_transport_pred (qt := qt) (qt' := qt')
            (show qt.pred = qt'.pred from rfl) hpred)
          (closureCapturedVarsRegime_transport_pred hcap)
    | inRegimeFalse k htag hlookup hnpred hcap =>
        exact valueConsistentWithRegime.inRegimeFalse k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (fun habs => hnpred (qtypPredHolds_transport_pred (qt := qt') (qt' := qt)
            (show qt'.pred = qt.pred from rfl) habs))
          (closureCapturedVarsRegime_transport_pred hcap)

private lemma resultAgreesIfClean_transport_normalizeAppResultByProvenance
  (predSat : PredSat) (R : Regime) (p p1 : Poison) (qt : QTyp)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (h : resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁) :
  resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁
    (normalizeAppResultByProvenance (joinPoison p1 p)
      { qt with poison := joinPoison p1 (joinPoison p qt.poison) }) o₀ o₁ := by
  intro hclean_norm
  unfold normalizeAppResultByProvenance at hclean_norm
  split at hclean_norm
  · exfalso
    cases hclean_norm with
    | clean hpoison => simp at hpoison
    | guard k htag => simp [qtypGuardTag] at htag
  · rename_i hp1p_false
    have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
    obtain ⟨hp1, hp⟩ := Bool.or_eq_false_iff.mp (by simpa [joinPoison] using hp1p)
    subst hp1; subst hp
    simp only [joinPoison, Bool.false_or] at hclean_norm
    have hclean_qt : qtypCleanUnder R qt := by
      convert hclean_norm using 1; cases qt; rfl
    have hagree := h hclean_qt
    unfold normalizeAppResultByProvenance
    simp [joinPoison]
    convert hagree using 1
    cases qt; rfl

-- Join-compatibility helpers for transporting clean location agreement from the
-- join result back to the head seed `first` in app-closure proofs.
private lemma valueConsistentWithRegimeMasked_app_body_result_member
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx bodyCtx : TypeContext) (src result3 : TypeResult)
  (p p1 : Poison) (μ_src μ_body : Memory) (θ : RealizationMap) (v : Value)
  (hsrc :
    src =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
  (hμ : μ_src = μ_body)
  (hval :
    valueConsistentWithRegimeMasked masked predSat (ctxAfter bodyCtx result3).regime
      result3.qualType μ_body θ v) :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx src).regime src.qualType μ_src θ v := by
  have hval_first :
      valueConsistentWithRegimeMasked masked predSat (ctxAfter bodyCtx result3).regime
        (normalizeAppResultByProvenance (joinPoison p1 p)
          { result3.qualType with
            poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
        μ_body θ v := by
    unfold normalizeAppResultByProvenance
    split
    · have hcap_src : closureCapturedVarsRegimeMasked masked predSat (ctxAfter bodyCtx result3).regime
          result3.qualType μ_body θ v := by
        exact valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval
      exact valueConsistentWithRegimeMasked.noTag (by simp [qtypGuardTag])
        (closureCapturedVarsRegimeMasked_transport_etyp (by simp) hcap_src)
    · rename_i hp1p_false
      have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
      have hand : p1 = false ∧ p = false := (Bool.or_eq_false_iff).mp (by simpa [joinPoison] using hp1p)
      rw [hand.1, hand.2]
      simp only [joinPoison, Bool.false_or]
      set qt' : QTyp := { result3.qualType with poison := joinPoison false result3.qualType.poison } with hqt'_def
      cases hval with
      | noTag htag hcap =>
          exact valueConsistentWithRegimeMasked.noTag
            (show qtypGuardTag qt' = none by simp [qtypGuardTag, hqt'_def]; exact htag)
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
      | guardOnly_ok k hgo hcap =>
          exact valueConsistentWithRegimeMasked.guardOnly_ok k
            (show qt'.pred = Predicate.guardOnly k from hgo)
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
      | maskedTag k htag hmasked hcap =>
          exact valueConsistentWithRegimeMasked.maskedTag k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag)
            hmasked
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
      | notInRegime k htag hlookup hcap =>
          exact valueConsistentWithRegimeMasked.notInRegime k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
      | inRegimeTrue k htag hlookup hpred hcap =>
          exact valueConsistentWithRegimeMasked.inRegimeTrue k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (qtypPredHolds_transport_pred (qt := result3.qualType) (qt' := qt')
              (show result3.qualType.pred = qt'.pred from rfl) hpred)
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
      | inRegimeFalse k htag hlookup hnpred hcap =>
          exact valueConsistentWithRegimeMasked.inRegimeFalse k
            (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
            (fun habs => hnpred (qtypPredHolds_transport_pred (qt := qt') (qt' := result3.qualType)
              (show qt'.pred = result3.qualType.pred from rfl) habs))
            (closureCapturedVarsRegimeMasked_transport_pred hcap)
  simpa [ctxAfter, hsrc, hμ] using hval_first

private lemma applyPFnTClosure_ok_poison_pred_of_p1_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (h_p1 : p1 = true)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  subst h_p1
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind, normalizeAppResultByProvenance] at happly
          cases htc :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc true)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  pureCtx := true
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } (PExpr.toExpr body) fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec capturedEnv =>
          -- normalizeAppResultByProvenance (joinPoison true p) = { poison := true, pred := noPred }
          -- since joinPoison true p = true || p = true
          simp only [normalizeAppResultByProvenance, joinPoison, Bool.true_or, ite_true,
            bind, Except.bind, pure, Except.pure] at happly
          -- happly: match retSpec with ... (each branch has poison := true, pred := noPred)
          split at happly
          · -- ExternReturn.simple: bind chain; innermost Except.ok has poison := true, pred := noPred
            split at happly
            · simp at happly
            · split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · have hr := Except.ok.inj happly; subst hr; simp
          · -- ExternReturn.nestedFn: Except.ok { poison := true, pred := noPred }
            have hr := Except.ok.inj happly; subst hr; simp
          · -- ExternReturn.nestedPfn: Except.ok { poison := true, pred := noPred }
            have hr := Except.ok.inj happly; subst hr; simp

-- Generalized variants: when joinPoison p1 p = true (covers both p1=true and p=true cases).
-- After the app-typing fix (AppPred (join p1 p) P3), normalizeAppResultByProvenance
-- is called with (joinPoison p1 p), so either outer or internal poison being dirty
-- forces poison=true, pred=noPred.
private lemma applyFnTClosure_ok_poison_pred_of_p1p_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : FnTClosure) (r : TypeResult)
  (h_p1p : joinPoison p1 p = true)
  (happly :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  unfold applyFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          cases htc :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison p1 ctx.pc)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } body fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance, h_p1p] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec effects capturedEnv =>
          -- normalizeAppResultByProvenance (joinPoison p1 p) = { poison := true, pred := noPred }
          -- since h_p1p : joinPoison p1 p = true
          simp only [normalizeAppResultByProvenance, h_p1p, ite_true,
            bind, Except.bind, pure, Except.pure] at happly
          -- after simp, happly: match retSpec with ... (after effects, each branch has poison := true)
          split at happly
          · -- collectAndAllocExternTags error case
            simp at happly
          · -- collectAndAllocExternTags ok; now forIn effects loop (can error or succeed)
            split at happly
            · simp at happly
            · -- forIn ok; now match retSpec
              split at happly
              · -- ExternReturn.simple: bind chain
                split at happly
                · simp at happly
                · split at happly
                  · simp at happly
                  · have hr := Except.ok.inj happly; subst hr; simp
              · -- ExternReturn.nestedFn
                have hr := Except.ok.inj happly; subst hr; simp
              · -- ExternReturn.nestedPfn
                have hr := Except.ok.inj happly; subst hr; simp

private lemma applyPFnTClosure_ok_poison_pred_of_p1p_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (h_p1p : joinPoison p1 p = true)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          cases htc :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc p1)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  pureCtx := true
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } (PExpr.toExpr body) fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance, h_p1p] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec capturedEnv =>
          -- normalizeAppResultByProvenance (joinPoison p1 p) = { poison := true, pred := noPred }
          -- since h_p1p : joinPoison p1 p = true
          simp only [normalizeAppResultByProvenance, h_p1p, ite_true,
            bind, Except.bind, pure, Except.pure] at happly
          -- happly: match retSpec with ... (each branch has poison := true, pred := noPred)
          split at happly
          · -- ExternReturn.simple: bind chain
            split at happly
            · simp at happly
            · split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · have hr := Except.ok.inj happly; subst hr; simp
          · -- ExternReturn.nestedFn
            have hr := Except.ok.inj happly; subst hr; simp
          · -- ExternReturn.nestedPfn
            have hr := Except.ok.inj happly; subst hr; simp





private lemma joinTypeResults_poison_pred_of_head_true_noPred
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hfirst_poison : first.qualType.poison = true)
  (hfirst_pred : first.qualType.pred = Predicate.noPred) :
  res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_poison :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.2.1 = true →
        acc'.2.2.1 = true := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hacc1 : acc1.2.2.1 = true := by
              simp [acc1, hacc, joinPoison]
            exact ih (acc := acc1) hfold_tail hacc1
  have h_fold_pred :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.2.2.1 = Predicate.noPred →
        acc'.2.2.2.1 = Predicate.noPred := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hacc1 : acc1.2.2.2.1 = Predicate.noPred := by
              simp [acc1, hacc, joinPredicates]
            exact ih (acc := acc1) hfold_tail hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at h_join
      have hpoison : poison = true := by simpa [hqt] using hfirst_poison
      have hpred : pred = Predicate.noPred := by simpa [hqt] using hfirst_pred
      subst hpoison hpred
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have hpoison_a : a.2.2.1 = true :=
                h_fold_poison
                  rest
                  (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a
                  hfold rfl
              have hpred_a : a.2.2.2.1 = Predicate.noPred :=
                h_fold_pred
                  rest
                  (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a
                  hfold rfl
              constructor
              · simp [joinPoison, hpoison_a]
              · cases a.1 <;> simp [hpred_a]
-- Synchronization helper for app/arrow clean branch.
-- Shape only for now: from clean output agreement on closure values, recover either
-- a shared regular-closure witness (with shared x/body) or explicit dirty-internal fallback.
private lemma stepFR_app_arrow_sync_from_clean
  (predSat : PredSat) (ctx : TypeContext) (res1 : TypeResult)
  (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap)
  (x₀ x₁ : Name) (body₀ body₁ : Expr) (env₀ env₁ : VarEnv)
  (hetyp : res1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hclean : qtypCleanUnder (ctxAfter ctx res1).regime res1.qualType)
  (hagree :
    resultAgreesIfClean predSat (ctxAfter ctx res1).regime
      μ₀ μ₁ θ₀ θ₁ res1.qualType
      (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)) :
  (∃ σcap,
      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
      x₀ = x₁ ∧
      body₀ = body₁ ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁)
  ∨ (¬ internalPoisonClean res1.qualType) := by
  -- Unfold resultAgreesIfClean and apply hclean to get agreeValueUnder
  have h := hagree hclean
  -- Case-split on the agreeValueUnder evidence
  cases h with
  | clean_internal_arrow hci hetyp' htcl hmatch hcap hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₁ hv₂ =>
    -- hetyp'  : res1.qualType.etyp = ETyp.arrow st1✝ st2✝ p✝ tcls✝  (fresh case vars)
    -- hetyp   : res1.qualType.etyp = ETyp.arrow st1  st2  p  tcls
    -- Combine to equate the two arrow types, then extract tcls✝ = tcls
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.arrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    -- hv₁ : Value.closure x₀ body₀ env₀ = Value.closure x✝ body✝ ρcap₁✝
    -- hv₂ : Value.closure x₁ body₁ env₁ = Value.closure x✝ body✝ ρcap₂✝
    cases hv₁
    cases hv₂
    -- hmatch : tcl✝ = FnTClosure.regular x₀ body₀ σcap✝
    subst hmatch
    -- htcl : FnTClosure.regular x₀ body₀ σcap✝ ∈ tcls
    left
    exact ⟨_, htcl, rfl, rfl, hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁⟩
  | dirty_internal_arrow hdirty _ _ _ =>
    -- Internal poison is dirty: the right disjunct holds
    right; exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    -- Impossible: arrow is a function type, contradicts hnotfun
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_parrow _ hetyp' _ _ _ _ _ _ _ =>
    -- Impossible: parrow ≠ arrow
    exfalso
    have : ETyp.parrow _ _ _ _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_parrow _ hisParrow _ _ =>
    -- Impossible: arrow type is not isParrow; hisParrow reduces to false = true
    exfalso; simp [ETyp.isParrow, hetyp] at hisParrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ arrow
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    -- Impossible: arrow is a function type
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ arrow
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this

-- Synchronization helper for app/parrow clean branch.
-- Same intent as the arrow helper, but for pe-closures.
private lemma stepFR_app_parrow_sync_from_clean
  (predSat : PredSat) (ctx : TypeContext) (res1 : TypeResult)
  (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap)
  (x₀ x₁ : Name) (body₀ body₁ : Expr) (env₀ env₁ : VarEnv)
  (hetyp : res1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hclean : qtypCleanUnder (ctxAfter ctx res1).regime res1.qualType)
  (hagree :
    resultAgreesIfClean predSat (ctxAfter ctx res1).regime
      μ₀ μ₁ θ₀ θ₁ res1.qualType
      (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)) :
  (∃ x pbody σcap,
      Expr.toPExpr? body₀ = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = body₁ ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁)
  ∨ (¬ internalPoisonClean res1.qualType) := by
  -- Unfold resultAgreesIfClean and apply hclean to get agreeValueUnder
  have h := hagree hclean
  -- Case-split on the agreeValueUnder evidence
  cases h with
  | clean_internal_parrow hci hetyp' htcl hmatch hcap hmv₁ hmc₁ hmv₂ hmc₂ hv₁ hv₂ =>
    -- hetyp'  : res1.qualType.etyp = ETyp.parrow st1✝ st2✝ p✝ tcls✝  (fresh case vars)
    -- hetyp   : res1.qualType.etyp = ETyp.parrow st1  st2  p  tcls
    -- Combine to equate the two parrow types, then extract tcls✝ = tcls
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.parrow.injEq] at hetyp_combined
    obtain ⟨-, -, -, rfl⟩ := hetyp_combined   -- tcls✝ := tcls
    -- hv₁ : Value.peClosure x₀ body₀ env₀ = Value.peClosure x✝ body✝ ρcap₁✝
    -- hv₂ : Value.peClosure x₁ body₁ env₁ = Value.peClosure x✝ body✝ ρcap₂✝
    cases hv₁
    cases hv₂
    -- hmatch : Expr.toPExpr? body₀ = some pbody✝ ∧ tcl✝ = PFnTClosure.regular x₀ pbody✝ σcap✝
    obtain ⟨htoPExpr, rfl⟩ := hmatch   -- tcl✝ := PFnTClosure.regular x₀ pbody✝ σcap✝
    -- htcl : PFnTClosure.regular x₀ pbody✝ σcap✝ ∈ tcls
    left
    exact ⟨x₀, _, _, htoPExpr, htcl, rfl, rfl, rfl, hcap, hmv₁, hmc₁, hmv₂, hmc₂⟩
  | dirty_internal_parrow hdirty _ _ _ =>
    -- Internal poison is dirty: the right disjunct holds
    right; exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    -- Impossible: parrow is a function type, contradicts hnotfun
    -- After simp, hnotfun reduces to true = false
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_arrow _ hetyp' _ _ _ _ _ _ _ =>
    -- Impossible: arrow ≠ parrow
    exfalso
    have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_arrow _ hisArrow _ _ =>
    -- Impossible: parrow type is not isArrow; hisArrow reduces to false = true
    exfalso; simp [ETyp.isArrow, hetyp] at hisArrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ parrow
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    -- Impossible: parrow is a function type
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ parrow
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this

private lemma stepFR_app_arrow_extract_shared_member
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (x₀ x₁ : Name) (body₀ body₁ : Expr)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results)
  (hsync :
    ∃ σcap,
      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
      x₀ = x₁ ∧
      body₀ = body₁) :
  ∃ σcap fuelBody first result3,
    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
    x₀ = x₁ ∧
    body₀ = body₁ ∧
    applyFnTClosure (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
      argEtyp argPoison argPred ctx result1 fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result1.tagEnv'
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' } body₀ fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases hsync with ⟨σcap, hmem, hx, hbody⟩
  rcases applyFnTClosure_regular_inv_of_mapM_mem
      ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuel tcls results x₀ body₀ σcap
      hmap hmem with
    ⟨fuelBody, first, result3, happly, hfuel, htc, hsub, hfirst⟩
  exact ⟨σcap, fuelBody, first, result3, hmem, hx, hbody, happly, hfuel, htc, hsub, hfirst⟩

-- Pure-arrow analog of shared-member extraction.
private lemma stepFR_app_parrow_extract_shared_member
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (x₀ x₁ : Name) (body₀ body₁ : Expr)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results)
  (hsync :
    ∃ x pbody σcap,
      Expr.toPExpr? body₀ = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = body₁) :
  ∃ x pbody σcap fuelBody first result3,
    Expr.toPExpr? body₀ = some pbody ∧
    PFnTClosure.regular x pbody σcap ∈ tcls ∧
    x₀ = x ∧
    x₁ = x ∧
    body₀ = body₁ ∧
    applyPFnTClosure (PFnTClosure.regular x pbody σcap) st1 st2 p p1
      argEtyp argPoison argPred ctx result1 fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result1.tagEnv'
        pureCtx := true
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases hsync with ⟨x, pbody, σcap, htoPExpr, hmem, hx₀, hx₁, hbody⟩
  rcases applyPFnTClosure_regular_inv_of_mapM_mem
      ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuel tcls results x pbody σcap
      hmap hmem with
    ⟨fuelBody, first, result3, happly, hfuel, htc, hsub, hfirst⟩
  exact ⟨x, pbody, σcap, fuelBody, first, result3, htoPExpr, hmem, hx₀, hx₁, hbody,
         happly, hfuel, htc, hsub, hfirst⟩

private lemma stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
      CtxCons ValCons predSat tm (Nat.succ (Nat.succ fuel')))
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmap : List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
      tcls = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res) :
  StepFRSingleRunFinalCleanPcTrueWithCtxValCons
    CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm result2 htc2'
  have hstruct := terminatesTo_app_inv' e1 e2 cinit cf o ht
  rcases hstruct with h_clo | h_peclo
  · rcases h_clo with
      ⟨c₂', v₂, c₁, x, body, env, evalCfg, ht_e2, ht_e1, _hpm1, ht_body, heq_cfg, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtx (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtx ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hcwr2 c₂'.nextAddr pm
        ((wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1) (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    have hTm1 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
    have hwf1 : wfTypeContext (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      wfTypeContext_of_wfTypeResult (ctxAfter ctxᵢ result2) result1
        (typecheckExpr_preserves_wfTypeResult (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1')
        hwf2 (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1')
    have htagR1 : regimeConsistentWithCtx (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_regimeConsistentWithCtx (ctxAfter ctxᵢ result2) e1 fuel' result1 htagR2 htc1'
    have hmono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
      regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
    have hv₁_arrow : valueHasETyp θ1 (Value.closure x body env) (ETyp.arrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_arrow with
    | closure _ _ _ =>
      obtain ⟨σcap, hσcap_mem, hσcap_typing, hcwr_body_raw⟩ :=
        ctxBodyStart
          ctxᵢ result2 result1 etyp2 p2 pred2
          st1 st2 p p1 tcls
          x body c₁.varEnv env
          c₂'.memory c₁.memory θ2 θ1 v₂
          hpredlaws hqt2 hetyp1 hmono1 hθext1
          hcwr1 hvalc2 hvalc1
      rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x body σcap hmap hσcap_mem with
        ⟨fuelBody, firstA, result3, happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
      have hfirstA_mem' : firstA ∈ first :: rest := by
        rcases list_mapM_ok_mem_input_exists_output
            (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
              ctxᵢ result1 fuel')
            hmap hσcap_mem with ⟨y, hy_mem, hy_eq⟩
        rw [← heq_results]
        have : y = firstA := Except.ok.inj (hy_eq.symm.trans happlyA)
        rwa [this] at hy_mem
      let bodyCtx : TypeContext :=
        { ctxᵢ with
          pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      have hcwr_body : CtxCons bodyCtx c₁.memory (env.update x v₂) θ1 := by
        simpa [bodyCtx] using hcwr_body_raw
      have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
        QTypRespectsTagMeaning_transport_etyp_pred
          (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
          (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
          (hqt2 ▸ typecheckExpr_preserves_QTypRespectsTagMeaning tm ctxᵢ e2 fuel' result2 hwfTm htc2') rfl rfl
      have hTmBody : wfTagMeaningCtx tm bodyCtx := by
        have hresTm1' : QTypRespectsTagMeaning tm result1.qualType :=
          typecheckExpr_preserves_QTypRespectsTagMeaning tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
        simpa [bodyCtx, ctxAfter] using
          wfTagMeaningCtx_closure_body
            (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
            (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
            (p := p) (tcls := tcls)
            (xFun := x) (body := body) (σcap := σcap)
            (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hTm1 hresTm1' hetyp1 hσcap_mem hargTm
      have htcBody' : typecheck bodyCtx body fuelBody = .ok result3 := by
        simpa [bodyCtx, typecheck] using htc_bodyA
      have hwfBody : wfTypeContext bodyCtx := by
        simp only [bodyCtx, wfTypeContext]
        have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
          (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
        have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
        exact ⟨hwf1.1,
          varEnvRefLocsBounded_update
            (varEnvRefLocsBounded_ofCaptured
              (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)))
            (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
          varEnvClosuresCapturedRefLocsBounded_update
            (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem))
            (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
      have harg_typed : valueHasETyp θ1 v₂ etyp2 := by
        simpa [hqt2] using valueHasETyp_extends hθext1.1 hv₂_typed
      have hric_body :
          runtimeInstantiatesCtx bodyCtx c₁.memory (env.update x v₂) θ1 := by
        let ctxCapBase : TypeContext :=
          { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
        have hric_cap_base :
            runtimeInstantiatesCtx (ctxAfter ctxCapBase result1)
              c₁.memory env θ1 := by
          constructor
          · intro l a hlookup
            exact hric1.1 l a hlookup
          · intro y qt hlookup
            have hlookup_list := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
            rcases hσcap_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
            exact ⟨v, hv, hσcap_typing.2.2 y qt v hlookup_list hv⟩
        have hric_body' :
            runtimeInstantiatesCtx
              { ctxCapBase with
                memEnv := result1.memEnv'
                tagEnv := result1.tagEnv'
                nextLoc := result1.nextLoc'
                nextTag := result1.nextTag'
                regime := result1.regime'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
              c₁.memory (env.update x v₂) θ1 :=
          runtimeInstantiatesCtx_closure_body
            (ctx := ctxCapBase) (result2 := result1) (x := x)
            (tenv := σcap)
            (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (argVal := v₂) (μ := c₁.memory) (ρ := env) (θ := θ1)
            hric_cap_base harg_typed
            (fun y qt hlookup => by
              have hl := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
              rcases hσcap_typing.2.1 y qt hl with ⟨v, hv⟩
              exact ⟨v, hv, hσcap_typing.2.2 y qt v hl hv⟩)
        simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body'
      have htagR_body : regimeConsistentWithCtx bodyCtx := by
        simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
      have hwfcfg_body_init :
          wfConfig
            { memory := c₁.memory
              varEnv := env.update x v₂
              nextAddr := c₁.nextAddr
              pureMode := false } := by
        have hwfcfg2 : wfConfig c₂' :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
        have hwfcfg1 : wfConfig c₁ :=
          (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).1
        have hv₂_wf_e2 : wfValue c₂'.nextAddr v₂ :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).2
        have hnext₂_to₁ : c₂'.nextAddr ≤ c₁.nextAddr :=
          terminatesTo_nextAddr_mono e1 c₂' c₁
            (Value.closure x body env) ht_e1
        have hv₂_wf : wfValue c₁.nextAddr v₂ :=
          wfValue_mono_of_le_nextAddr hnext₂_to₁ x v₂ hv₂_wf_e2
        have henv_wf : wfVarEnv c₁.nextAddr env := by
          cases (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).2 with
          | closure _ _ _ henv => exact henv
        constructor
        · intro a ha; exact hwfcfg1.1 a ha
        · simpa [VarEnv.update] using wfVarEnv.cons x v₂ env hv₂_wf henv_wf
      have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
        have : fuelBody < fuel' := by rw [hfuelA]; exact Nat.lt_succ_self _
        exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
      have hSingle_body := singleIH fuelBody hfuel_lt body bodyCtx hTmBody result3 htcBody'
      have hpc_body : bodyCtx.pc = true := by
        simp [bodyCtx, hpc, joinPoison]
      rcases
        hSingle_body hpredlaws hTmBody
          c₁.memory (env.update x v₂) θ1 evalCfg o
          hθ1wf hwfBody hric_body htagR_body hcwr_body
          c₁.nextAddr false hwfcfg_body_init ht_body hpc_body
        with ⟨θ_body, hθext_body, hv_body_typed, hric_body_final, hcwr_body_final, hvalc_body, hpres_body, _hfresh_body⟩
      have hθext : wfExtendsMap θ θ_body :=
        wfExtendsMap_trans hθext2 (wfExtendsMap_trans hθext1 hθext_body)
      have hfirstA_etyp : firstA.qualType.etyp = result3.qualType.etyp := by
        rw [hfirstA_eq]
        unfold normalizeAppResultByProvenance
        split <;> rfl
      have hmem_eq : cf.memory = evalCfg.memory := by
        simp [heq_cfg]
      have hvar_eq : cf.varEnv = c₁.varEnv := by
        simp [heq_cfg]
      have h_mono_body : Regime.monotoneStep bodyCtx.regime result3.regime' :=
        regime_monotone bodyCtx body fuelBody result3 htcBody'
      have hres1_to_firstA_mono :
          Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
            (ctxAfter ctxᵢ firstA).regime := by
        simpa [bodyCtx, ctxAfter, hfirstA_eq] using h_mono_body
      have hlookup_back_res1_to_A :
          ∀ k b,
            (ctxAfter ctxᵢ firstA).regime.lookup? k = some b →
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
        intro k b hk_src
        have hRdef_src : (ctxAfter ctxᵢ firstA).regime.lookup? k ≠ none := by
          intro hnone; rw [hk_src] at hnone; contradiction
        have hRdef_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
          hres1_to_firstA_mono.2 k hRdef_src
        cases hk_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
        | none => exact False.elim (hRdef_res1 hk_res1)
        | some b1 =>
            rcases hres1_to_firstA_mono.1 k b1 hk_res1 with hk_src' | hnone_src
            · have : some b1 = some b := hk_src'.symm.trans hk_src
              simpa using Option.some.inj this
            · rw [hnone_src] at hk_src
              cases hk_src
      have hric_final :
          runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        have hmem_to_res :
            ∀ l, firstA.memEnv'.contains l → res.memEnv'.contains l :=
          joinTypeResults_mem_contains_of_member
            (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest)
            (res := res) h_join hfirstA_mem'
        constructor
        · intro l a hθ
          have hloc := hric_body_final.1 l a hθ
          rcases hloc with ⟨hcontains_body, hmem_contains⟩
          have hcontains_src : firstA.memEnv'.contains l := by
            simpa [ctxAfter, hfirstA_eq] using hcontains_body
          exact ⟨hmem_to_res l hcontains_src, by simpa [hmem_eq] using hmem_contains⟩
        · intro y qt hlookup
          have hlookup_ctx :
              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup y = some qt := by
            simpa [ctxAfter] using hlookup
          rcases hric1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
          exact ⟨v, by simpa [hvar_eq] using hlookup_v, valueHasETyp_extends hθext_body.1 hv_typ⟩
      have hcwr_src :
          CtxCons (ctxAfter ctxᵢ firstA) cf.memory cf.varEnv θ_body := by
        have hpred_compat :
            ∀ (qt' : QTyp) (v' : Value),
              qtypPredHolds predSat qt' c₁.memory v' ↔ qtypPredHolds predSat qt' cf.memory v' :=
          qtypPredHolds_mem_compat_of_predSatLaws
            (hpredlaws := hpredlaws) (θ := θ1) (μ := c₁.memory) (μ' := cf.memory)
        exact
          ctxMember
            ctxᵢ bodyCtx result2 result1 firstA result3
            (normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
            c₁ evalCfg cf θ1 θ_body
            hpred_compat hfirstA_eq hmem_eq hvar_eq
            hlookup_back_res1_to_A hθext_body hcwr1 hcwr_body_final
      have hcwr_final :
          CtxCons (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        exact ctxJoinMember ctxᵢ first firstA rest res cf.memory cf.varEnv θ_body
          h_join hfirstA_mem' hcwr_src
      have hval_src :
          ValCons (ctxAfter ctxᵢ firstA).regime
            firstA.qualType cf.memory θ_body o := by
        exact
          valBodyResult ctxᵢ bodyCtx firstA result3 p p1 cf.memory evalCfg.memory θ_body o
            hfirstA_eq hmem_eq hvalc_body
      have hvalc_final :
          ValCons (ctxAfter ctxᵢ res).regime
            res.qualType cf.memory θ_body o := by
        exact valJoinMember ctxᵢ first firstA rest res cf.memory θ_body o
          h_join hfirstA_mem' hval_src
      have hpres_final :
          PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ_body := by
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hcontains_ctx : ctxᵢ.memEnv.contains l :=
          memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
        have hcontains2 : result2.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxᵢ) (e := e2) (fuel := fuel') (res := result2) htc2' l hcontains_ctx
        rcases memEnv_lookup_some_of_contains result2.memEnv' l hcontains2 with
          ⟨qt2, hlookup2⟩
        have hcontains1 : result1.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1) htc1' l
            (by simpa [ctxAfter] using hcontains2)
        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains1 with
          ⟨qt1, hlookup1⟩
        have hcontains3 : result3.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3) htcBody' l
            (by simpa [bodyCtx] using hcontains1)
        rcases memEnv_lookup_some_of_contains result3.memEnv' l hcontains3 with
          ⟨qt3, hlookup3⟩
        have hlookup_firstA : firstA.memEnv'.lookup l = some qt3 := by
          simpa [hfirstA_eq] using hlookup3
        have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_out := by
          simpa [ctxAfter] using hlookup_out
        have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_out := by
          simpa [ctxAfter] using hclean_out
        have hlookup_firstA_ctx : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
          simpa [ctxAfter] using hlookup_firstA
        have hclean3_firstA :
            qtypCleanUnder (ctxAfter ctxᵢ firstA).regime qt3 := by
          exact
            joinTypeResults_lookup_member_clean_compat
              (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
              h_join hfirstA_mem' l qt_out qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx
        have hclean3 : qtypCleanUnder result3.regime' qt3 := by
          simpa [ctxAfter, hfirstA_eq] using hclean3_firstA
        have hclean1 : qtypCleanUnder result1.regime' qt1 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
              htc_bodyA hwfBody hpc_body l qt1 qt3
              (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
        have hclean2 : qtypCleanUnder result2.regime' qt2 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
              (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
              (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
        have hpres_l2 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxᵢ) (res := result2) (μ_in := μ) (μ_out := c₂'.memory)
            (θ_in := θ) (θ_out := θ2)
            hpres2 hlookup_in hlookup2 hclean2
        have hpres_l1 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxAfter ctxᵢ result2) (res := result1)
            (μ_in := c₂'.memory) (μ_out := c₁.memory)
            (θ_in := θ2) (θ_out := θ1)
            hpres1
            (by simpa [ctxAfter] using hlookup2)
            hlookup1 hclean1
        have hpres_lbody :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := bodyCtx) (res := result3)
            (μ_in := c₁.memory) (μ_out := evalCfg.memory)
            (θ_in := θ1) (θ_out := θ_body)
            hpres_body
            (by simpa [bodyCtx] using hlookup1)
            hlookup3 hclean3
        have hpres_lbody' :
            PreservesInheritedCleanLocOneRun c₁.memory cf.memory θ1 θ_body l := by
          simpa [hmem_eq] using hpres_lbody
        exact
          PreservesInheritedCleanLocOneRun.trans hpres_l2
            (PreservesInheritedCleanLocOneRun.trans hpres_l1 hpres_lbody')
      have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ_body := by
        intro l qt_f hnotIn hlookup_f hclean_f
        by_cases hc3 : result3.memEnv'.contains l
        · by_cases hc1 : result1.memEnv'.contains l
          · by_cases hc2 : result2.memEnv'.contains l
            · -- Case 4: l ∈ result2.memEnv' but l ∉ ctxᵢ.memEnv
              rcases memEnv_lookup_some_of_contains result2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  htc_bodyA hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
                  (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
                  (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ2_none := _hfresh2 l qt2 hnotIn hlookup2 hclean2
              have hpres_l1' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxAfter ctxᵢ result2) (res := result1)
                  (μ_in := c₂'.memory) (μ_out := c₁.memory) (θ_in := θ2) (θ_out := θ1)
                  hpres1 (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ1_none : θ1.lookup l = none := by
                cases hpres_l1' with
                | both_unrealized _ h_out => exact h_out
                | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ2_none]; exact nofun)
              have hpres_lbody' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := c₁.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              cases hpres_lbody' with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
            · -- Case 3: l ∉ result2.memEnv' but l ∈ result1.memEnv'
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  htc_bodyA hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hθ1_none := _hfresh1 l qt1 (by simpa [ctxAfter] using hc2) hlookup1 hclean1
              have hpres_lbody' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := c₁.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              cases hpres_lbody' with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
          · -- Case 2: l ∉ result1.memEnv' but l ∈ result3.memEnv'
            rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
            have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
              simpa [ctxAfter, hfirstA_eq] using hlookup3
            have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
              simpa [ctxAfter] using hlookup_f
            have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
              simpa [ctxAfter] using hclean_f
            have hclean3 : qtypCleanUnder result3.regime' qt3 := by
              simpa [ctxAfter, hfirstA_eq] using
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                  h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
            exact _hfresh_body l qt3 (by simpa [bodyCtx] using hc1) hlookup3 hclean3
        · -- Case 1: l ∉ result3.memEnv'
          exact
            theta_not_contains_if_not_in_memEnv
              (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θ_body l
              hric_body_final (by simpa [ctxAfter] using hc3)
      refine ⟨θ_body, hθext, ?_, hric_final, hcwr_final, hvalc_final, hpres_final, hfresh_final⟩
      exact
        joinTypeResults_transport_valueHasETyp_from_member
          (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
          (θ := θ_body) (v := o)
          h_join hfirstA_mem' (hfirstA_etyp ▸ hv_body_typed)
  · rcases h_peclo with
      ⟨c₂', v₂, c₁, x, body, env, _evalCfg, ht_e2, ht_e1, _htoPExpr, _ht_body, _hcf, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtx (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtx ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_peClosure_etyp_parrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _ptcls, hparr⟩
    rw [hetyp1] at hparr
    cases hparr

private lemma stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxBodyStart :
    AppPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
      CtxCons ValCons predSat tm (Nat.succ (Nat.succ fuel')))
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmap : List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
      tcls = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res) :
  StepFRSingleRunFinalCleanPcTrueWithCtxValCons
    CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm result2 htc2'
  have hstruct := terminatesTo_app_inv' e1 e2 cinit cf o ht
  rcases hstruct with h_clo | h_peclo
  · rcases h_clo with
      ⟨c₂', v₂, c₁, x, body, env, _evalCfg, ht_e2, ht_e1, _hpm1, _ht_body, _hcf, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtx (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtx ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_closure_etyp_arrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _tcls, harrow⟩
    rw [hetyp1] at harrow
    cases harrow
  · rcases h_peclo with
      ⟨c₂', v₂, c₁, x, body, env, evalCfg, ht_e2, ht_e1, _htoPExpr_body, ht_body, hcf, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtx (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtx ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    have hTm1 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
    have hwf1 : wfTypeContext (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      wfTypeContext_of_wfTypeResult (ctxAfter ctxᵢ result2) result1
        (typecheckExpr_preserves_wfTypeResult (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1')
        hwf2 (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1')
    have htagR1 : regimeConsistentWithCtx (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_regimeConsistentWithCtx (ctxAfter ctxᵢ result2) e1 fuel' result1 htagR2 htc1'
    have hmono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
      regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
    have hv₁_parrow : valueHasETyp θ1 (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_parrow with
    | peClosure _ _ _ _ =>
      obtain ⟨σcap, pbody, htoPExpr, hσcap_mem, hσcap_typing, hcwr_body_raw⟩ :=
        ctxBodyStart
          ctxᵢ result2 result1 etyp2 p2 pred2
          st1 st2 p p1 tcls
          x body cf.varEnv env
          c₂'.memory cf.memory θ2 θ1 v₂
          hpredlaws hqt2 hetyp1 hmono1 hθext1
          (by simpa [hcf] using hcwr1) hvalc2 (by simpa [hcf] using hvalc1)
      have hbody_eq : PExpr.toExpr pbody = body :=
        PExpr_toExpr_of_toPExpr?_some body pbody htoPExpr
      rcases applyPFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x pbody σcap hmap hσcap_mem with
        ⟨fuelBody, firstA, result3, happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
      have hfirstA_mem' : firstA ∈ first :: rest := by
        rcases list_mapM_ok_mem_input_exists_output
            (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
              ctxᵢ result1 fuel')
            hmap hσcap_mem with ⟨y, hy_mem, hy_eq⟩
        rw [← heq_results]
        have : y = firstA := Except.ok.inj (hy_eq.symm.trans happlyA)
        rwa [this] at hy_mem
      let bodyCtx : TypeContext :=
        { ctxᵢ with
          pc := joinPoison p (joinPoison ctxᵢ.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      have hcwr_body : CtxCons bodyCtx cf.memory (env.update x v₂) θ1 := by
        simpa [bodyCtx] using hcwr_body_raw
      have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
        QTypRespectsTagMeaning_transport_etyp_pred
          (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
          (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
          (hqt2 ▸ typecheckExpr_preserves_QTypRespectsTagMeaning tm ctxᵢ e2 fuel' result2 hwfTm htc2') rfl rfl
      have hTmBody : wfTagMeaningCtx tm bodyCtx := by
        have hresTm1' : QTypRespectsTagMeaning tm result1.qualType :=
          typecheckExpr_preserves_QTypRespectsTagMeaning tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
        simpa [bodyCtx, ctxAfter] using
          wfTagMeaningCtx_pclosure_body
            (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
            (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
            (p := p) (tcls := tcls)
            (xFun := x) (pbody := pbody) (σcap := σcap)
            (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hTm1 hresTm1' hetyp1 hσcap_mem hargTm
      have htcBody' : typecheck bodyCtx (PExpr.toExpr pbody) fuelBody = .ok result3 := by
        simpa [bodyCtx, typecheck] using htc_bodyA
      have htcBody_body : typecheck bodyCtx body fuelBody = .ok result3 := by
        rw [← hbody_eq]
        exact htcBody'
      have hwfBody : wfTypeContext bodyCtx := by
        simp only [bodyCtx, wfTypeContext]
        have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
          (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
        have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
        exact ⟨hwf1.1,
          varEnvRefLocsBounded_update
            (varEnvRefLocsBounded_ofCaptured
              (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)))
            (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
          varEnvClosuresCapturedRefLocsBounded_update
            (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem))
            (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
      have harg_typed : valueHasETyp θ1 v₂ etyp2 := by
        simpa [hqt2] using valueHasETyp_extends hθext1.1 hv₂_typed
      have hric_body :
          runtimeInstantiatesCtx bodyCtx cf.memory (env.update x v₂) θ1 := by
        let ctxCapBase : TypeContext :=
          { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
        have hric_cap_base :
            runtimeInstantiatesCtx (ctxAfter ctxCapBase result1)
              cf.memory env θ1 := by
          constructor
          · intro l a hlookup
            have : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1) c₁.memory c₁.varEnv θ1 := hric1
            simpa [ctxAfter, hcf] using this.1 l a hlookup
          · intro y qt hlookup
            have hlookup_list := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
            rcases hσcap_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
            exact ⟨v, by simpa [hcf] using hv, hσcap_typing.2.2 y qt v hlookup_list (by simpa [hcf] using hv)⟩
        have hric_body' :
            runtimeInstantiatesCtx
              { ctxCapBase with
                memEnv := result1.memEnv'
                tagEnv := result1.tagEnv'
                nextLoc := result1.nextLoc'
                nextTag := result1.nextTag'
                regime := result1.regime'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
              cf.memory (env.update x v₂) θ1 :=
          runtimeInstantiatesCtx_closure_body
            (ctx := ctxCapBase) (result2 := result1) (x := x)
            (tenv := σcap)
            (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (argVal := v₂) (μ := cf.memory) (ρ := env) (θ := θ1)
            hric_cap_base harg_typed
            (fun y qt hlookup => by
              have hl := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
              rcases hσcap_typing.2.1 y qt hl with ⟨v, hv⟩
              exact ⟨v, by simpa [hcf] using hv, hσcap_typing.2.2 y qt v hl (by simpa [hcf] using hv)⟩)
        simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body'
      have htagR_body : regimeConsistentWithCtx bodyCtx := by
        simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
      have hwfcfg1 : wfConfig cf := by
        simpa [hcf] using (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).1
      have hwfcfg_body_init :
          wfConfig
            { memory := cf.memory
              varEnv := env.update x v₂
              nextAddr := cf.nextAddr
              pureMode := true } := by
        have hv₂_wf_e2 : wfValue c₂'.nextAddr v₂ :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).2
        have hnext₂_to₁ : c₂'.nextAddr ≤ cf.nextAddr := by
          simpa [hcf] using
            (terminatesTo_nextAddr_mono e1 c₂' c₁ (Value.peClosure x body env) ht_e1)
        have hv₂_wf : wfValue cf.nextAddr v₂ :=
          wfValue_mono_of_le_nextAddr hnext₂_to₁ x v₂ hv₂_wf_e2
        have henv_wf : wfVarEnv cf.nextAddr env := by
          have hwf_val := (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).2
          cases hwf_val with
          | peClosure _ _ _ henv =>
              simpa [hcf] using henv
        constructor
        · intro a ha
          exact hwfcfg1.1 a ha
        · simpa [VarEnv.update] using wfVarEnv.cons x v₂ env hv₂_wf henv_wf
      have ht_body' : terminatesTo body
          { memory := cf.memory, varEnv := env.update x v₂,
            nextAddr := cf.nextAddr, pureMode := true } evalCfg o := by
        simpa [hcf] using ht_body
      have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
        have : fuelBody < fuel' := by rw [hfuelA]; exact Nat.lt_succ_self _
        exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
      have hSingle_body := singleIH fuelBody hfuel_lt body bodyCtx hTmBody result3 htcBody_body
      have hpc_body : bodyCtx.pc = true := by
        simp [bodyCtx, hpc, joinPoison]
      rcases
        hSingle_body hpredlaws hTmBody
          cf.memory (env.update x v₂) θ1 evalCfg o
          hθ1wf hwfBody hric_body htagR_body hcwr_body
          cf.nextAddr true hwfcfg_body_init ht_body' hpc_body
        with ⟨θ_body, hθext_body, hv_body_typed, hric_body_final, hcwr_body_final, hvalc_body, hpres_body, _hfresh_body⟩
      have hθext : wfExtendsMap θ θ_body :=
        wfExtendsMap_trans hθext2 (wfExtendsMap_trans hθext1 hθext_body)
      have hfirstA_etyp : firstA.qualType.etyp = result3.qualType.etyp := by
        rw [hfirstA_eq]
        unfold normalizeAppResultByProvenance
        split <;> rfl
      have h_mono_body : Regime.monotoneStep bodyCtx.regime result3.regime' :=
        regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3 htcBody'
      have hres1_to_firstA_mono :
          Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
            (ctxAfter ctxᵢ firstA).regime := by
        simpa [bodyCtx, ctxAfter, hfirstA_eq] using h_mono_body
      have hlookup_back_res1_to_A :
          ∀ k b,
            (ctxAfter ctxᵢ firstA).regime.lookup? k = some b →
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
        intro k b hk_src
        have hRdef_src : (ctxAfter ctxᵢ firstA).regime.lookup? k ≠ none := by
          intro hnone; rw [hk_src] at hnone; contradiction
        have hRdef_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
          hres1_to_firstA_mono.2 k hRdef_src
        cases hk_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
        | none => exact False.elim (hRdef_res1 hk_res1)
        | some b1 =>
            rcases hres1_to_firstA_mono.1 k b1 hk_res1 with hk_src' | hnone_src
            · have : some b1 = some b := hk_src'.symm.trans hk_src
              simpa using Option.some.inj this
            · rw [hnone_src] at hk_src
              cases hk_src
      have hmem_eq : cf.memory = evalCfg.memory := by
        obtain ⟨fuel_b, verbose_b, hbeval_b⟩ := ht_body'
        exact (beval_pure_memory_eq body fuel_b _ evalCfg o verbose_b
          pbody
          htoPExpr rfl hbeval_b).symm
      have hric_final :
          runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        have hmem_to_res :
            ∀ l, firstA.memEnv'.contains l → res.memEnv'.contains l :=
          joinTypeResults_mem_contains_of_member
            (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest)
            (res := res) h_join hfirstA_mem'
        constructor
        · intro l a hθ
          have hloc := hric_body_final.1 l a hθ
          rcases hloc with ⟨hcontains_body, hmem_contains⟩
          have hcontains_src : firstA.memEnv'.contains l := by
            simpa [ctxAfter, hfirstA_eq] using hcontains_body
          exact ⟨hmem_to_res l hcontains_src, by simpa [hmem_eq] using hmem_contains⟩
        · intro y qt hlookup
          have hlookup_ctx :
              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup y = some qt := by
            simpa [ctxAfter] using hlookup
          have hric1_cf :
              runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1)
                cf.memory cf.varEnv θ1 := by
            simpa [hcf] using hric1
          rcases hric1_cf.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
          exact ⟨v, hlookup_v, valueHasETyp_extends hθext_body.1 hv_typ⟩
      have hcwr_src :
          CtxCons (ctxAfter ctxᵢ firstA) cf.memory cf.varEnv θ_body := by
        have hpred_compat :
            ∀ (qt' : QTyp) (v' : Value),
              qtypPredHolds predSat qt' cf.memory v' ↔ qtypPredHolds predSat qt' cf.memory v' :=
          fun _ _ => Iff.rfl
        exact
          ctxMember
            ctxᵢ bodyCtx result2 result1 firstA result3
            (normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
            cf evalCfg cf θ1 θ_body
            hpred_compat hfirstA_eq hmem_eq rfl
            hlookup_back_res1_to_A hθext_body
            (by simpa [hcf] using hcwr1) hcwr_body_final
      have hcwr_final :
          CtxCons (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        exact ctxJoinMember ctxᵢ first firstA rest res cf.memory cf.varEnv θ_body
          h_join hfirstA_mem' hcwr_src
      have hval_src :
          ValCons (ctxAfter ctxᵢ firstA).regime
            firstA.qualType cf.memory θ_body o := by
        exact
          valBodyResult ctxᵢ bodyCtx firstA result3 p p1 cf.memory evalCfg.memory θ_body o
            hfirstA_eq hmem_eq hvalc_body
      have hvalc_final :
          ValCons (ctxAfter ctxᵢ res).regime
            res.qualType cf.memory θ_body o := by
        exact valJoinMember ctxᵢ first firstA rest res cf.memory θ_body o
          h_join hfirstA_mem' hval_src
      have hpres_final :
          PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ_body := by
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hcontains_ctx : ctxᵢ.memEnv.contains l :=
          memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
        have hcontains2 : result2.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxᵢ) (e := e2) (fuel := fuel') (res := result2) htc2' l hcontains_ctx
        rcases memEnv_lookup_some_of_contains result2.memEnv' l hcontains2 with
          ⟨qt2, hlookup2⟩
        have hcontains1 : result1.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1) htc1' l
            (by simpa [ctxAfter] using hcontains2)
        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains1 with
          ⟨qt1, hlookup1⟩
        have hcontains3 : result3.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3) htcBody_body l
            (by simpa [bodyCtx] using hcontains1)
        rcases memEnv_lookup_some_of_contains result3.memEnv' l hcontains3 with
          ⟨qt3, hlookup3⟩
        have hlookup_firstA : firstA.memEnv'.lookup l = some qt3 := by
          simpa [hfirstA_eq] using hlookup3
        have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_out := by
          simpa [ctxAfter] using hlookup_out
        have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_out := by
          simpa [ctxAfter] using hclean_out
        have hlookup_firstA_ctx : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
          simpa [ctxAfter] using hlookup_firstA
        have hclean3_firstA :
            qtypCleanUnder (ctxAfter ctxᵢ firstA).regime qt3 := by
          exact
            joinTypeResults_lookup_member_clean_compat
              (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
              h_join hfirstA_mem' l qt_out qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx
        have hclean3 : qtypCleanUnder result3.regime' qt3 := by
          simpa [ctxAfter, hfirstA_eq] using hclean3_firstA
        have hclean1 : qtypCleanUnder result1.regime' qt1 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
              (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
              (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
        have hclean2 : qtypCleanUnder result2.regime' qt2 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
              (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
              (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
        have hpres_l2 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxᵢ) (res := result2) (μ_in := μ) (μ_out := c₂'.memory)
            (θ_in := θ) (θ_out := θ2)
            hpres2 hlookup_in hlookup2 hclean2
        have hpres_l1 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxAfter ctxᵢ result2) (res := result1)
            (μ_in := c₂'.memory) (μ_out := c₁.memory)
            (θ_in := θ2) (θ_out := θ1)
            hpres1
            (by simpa [ctxAfter] using hlookup2)
            hlookup1 hclean1
        have hpres_l1' :
            PreservesInheritedCleanLocOneRun c₂'.memory cf.memory θ2 θ1 l := by
          simpa [hcf] using hpres_l1
        have hpres_lbody :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := bodyCtx) (res := result3)
            (μ_in := cf.memory) (μ_out := evalCfg.memory)
            (θ_in := θ1) (θ_out := θ_body)
            hpres_body
            (by simpa [bodyCtx] using hlookup1)
            hlookup3 hclean3
        have hpres_lbody' :
            PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
          simpa [hmem_eq] using hpres_lbody
        exact
          PreservesInheritedCleanLocOneRun.trans hpres_l2
            (PreservesInheritedCleanLocOneRun.trans hpres_l1' hpres_lbody')
      have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ_body := by
        intro l qt_f hnotIn hlookup_f hclean_f
        by_cases hc3 : result3.memEnv'.contains l
        · by_cases hc1 : result1.memEnv'.contains l
          · by_cases hc2 : result2.memEnv'.contains l
            · -- Case 4: l ∈ result2.memEnv' but l ∉ ctxᵢ.memEnv
              rcases memEnv_lookup_some_of_contains result2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
                  (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
                  (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ2_none := _hfresh2 l qt2 hnotIn hlookup2 hclean2
              have hpres_l1_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxAfter ctxᵢ result2) (res := result1)
                  (μ_in := c₂'.memory) (μ_out := c₁.memory) (θ_in := θ2) (θ_out := θ1)
                  hpres1 (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ1_none : θ1.lookup l = none := by
                have hpres_cf : PreservesInheritedCleanLocOneRun c₂'.memory cf.memory θ2 θ1 l := by
                  simpa [hcf] using hpres_l1_loc
                cases hpres_cf with
                | both_unrealized _ h_out => exact h_out
                | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ2_none]; exact nofun)
              have hpres_lbody_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := cf.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hpres_lbody_cf : PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
                simpa [hmem_eq] using hpres_lbody_loc
              cases hpres_lbody_cf with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
            · -- Case 3: l ∉ result2.memEnv' but l ∈ result1.memEnv'
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hθ1_none := _hfresh1 l qt1 (by simpa [ctxAfter] using hc2) hlookup1 hclean1
              have hpres_lbody_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := cf.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hpres_lbody_cf : PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
                simpa [hmem_eq] using hpres_lbody_loc
              cases hpres_lbody_cf with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
          · -- Case 2: l ∉ result1.memEnv' but l ∈ result3.memEnv'
            rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
            have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
              simpa [ctxAfter, hfirstA_eq] using hlookup3
            have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
              simpa [ctxAfter] using hlookup_f
            have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
              simpa [ctxAfter] using hclean_f
            have hclean3 : qtypCleanUnder result3.regime' qt3 := by
              simpa [ctxAfter, hfirstA_eq] using
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                  h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
            exact _hfresh_body l qt3 (by simpa [bodyCtx] using hc1) hlookup3 hclean3
        · -- Case 1: l ∉ result3.memEnv'
          exact
            theta_not_contains_if_not_in_memEnv
              (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θ_body l
              hric_body_final (by simpa [ctxAfter] using hc3)
      refine ⟨θ_body, hθext, ?_, hric_final, hcwr_final, hvalc_final, hpres_final, hfresh_final⟩
      exact
        joinTypeResults_transport_valueHasETyp_from_member
          (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
          (θ := θ_body) (v := o)
          h_join hfirstA_mem' (hfirstA_etyp ▸ hv_body_typed)

private lemma stepFRSingleRunFinalCleanPcTrue_app_parametric
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxClosureBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (ctxPClosureBodyStart :
    AppPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueWithCtxValCons_IH
      CtxCons ValCons predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueWithCtxValCons
    CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  have htcApp : typecheckApp ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    rw [← typecheckExpr_app_succ ctxᵢ e1 e2 (Nat.succ fuel')]
    simpa [typecheck] using htc
  obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, h_arrow_or_parrow⟩ :=
    typecheckApp_arrow_structure_full ctxᵢ e1 e2 fuel' res htcApp
  have htc2' : typecheck ctxᵢ e2 fuel' = .ok result2 := by
    simpa [typecheck] using htc2
  have htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
    simp [ctxAfter] at htc1 ⊢
    exact htc1
  cases h_arrow_or_parrow with
  | inl h_arrow =>
      obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1, _hnpure,
        _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_arrow
      exact
        stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric
          CtxCons ValCons ctxᵢ predSat tm
          ctxClosureBodyStart ctxMember ctxJoinMember valBodyResult valJoinMember
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join
  | inr h_parrow =>
      obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1,
        _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_parrow
      exact
        stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric
          CtxCons ValCons ctxᵢ predSat tm
          ctxPClosureBodyStart ctxMember ctxJoinMember valBodyResult valJoinMember
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join

private def StepFRAppClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  AppClosureBodyStart CtxCons ValCons predSat tm

private def StepFRAppPClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  AppPClosureBodyStart CtxCons ValCons predSat tm

private def StepFRAppMemberCtxCons
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (predSat : PredSat) : Prop :=
  AppMemberCtxCons CtxCons predSat

private def StepFRAppJoinCtxConsFromMember
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop) : Prop :=
  AppJoinCtxConsFromMember CtxCons

private def StepFRAppBodyResultValCons
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  AppBodyResultValCons ValCons

private def StepFRAppJoinValConsFromMember
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop) : Prop :=
  AppJoinValConsFromMember ValCons

private theorem stepFRApp_closureBodyStart_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRAppClosureBodyStart
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    predSat tm := by
  intro ctx result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
    hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure
  simpa [StepFRAppClosureBodyStart] using
    consistentWithRegimeMasked_app_arrow_body_start masked ctx predSat tm result2 result1 etyp2 p2 pred2
      st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure

private theorem stepFRApp_pClosureBodyStart_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRAppPClosureBodyStart
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    predSat tm := by
  intro ctx result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
    hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure
  simpa [StepFRAppPClosureBodyStart] using
    consistentWithRegimeMasked_app_parrow_body_start masked ctx predSat tm result2 result1 etyp2 p2 pred2
      st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure

private theorem stepFRApp_memberCtxCons_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRAppMemberCtxCons
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    predSat := by
  intro ctx bodyCtx result2 result1 src result3 qtSrc cpre cbody cfinal θpre θfinal
    hpred_mem srcEq hmem hvar hreg hθext hctxCons_pre hctxCons_body
  simpa [StepFRAppMemberCtxCons] using
    consistentWithRegimeMasked_app_member_from_body masked predSat ctx bodyCtx result2 result1 src result3
      qtSrc cpre cbody cfinal θpre θfinal
      hpred_mem srcEq hmem hvar hreg hθext hctxCons_pre hctxCons_body

private theorem stepFRApp_joinCtxConsFromMember_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRAppJoinCtxConsFromMember
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ) := by
  intro ctx first src rest res μ ρ θ h_join h_src hctxCons
  simpa [StepFRAppJoinCtxConsFromMember] using
    joinTypeResults_transport_consistentWithRegimeMasked_from_member
      (masked := masked) (predSat := predSat) (ctx := ctx) (first := first) (src := src)
      (rest := rest) (res := res) (μ := μ) (ρ := ρ) (θ := θ)
      h_join h_src hctxCons

private theorem stepFRApp_bodyResultValCons_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRAppBodyResultValCons
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v) := by
  intro ctx bodyCtx src result3 p p1 μ_src μ_body θ v hsrc hμ hval
  simpa [StepFRAppBodyResultValCons] using
    valueConsistentWithRegimeMasked_app_body_result_member masked predSat ctx bodyCtx src result3
      p p1 μ_src μ_body θ v hsrc hμ hval

private theorem stepFRApp_joinValConsFromMember_masked
  (masked : Tag → Prop) (predSat : PredSat) :
  StepFRAppJoinValConsFromMember
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v) := by
  intro ctx first src rest res μ θ v h_join h_src hval
  simpa [StepFRAppJoinValConsFromMember] using
    joinTypeResults_transport_valueConsistentWithRegimeMasked_from_member
      (masked := masked) (predSat := predSat) (ctx := ctx) (first := first) (src := src)
      (rest := rest) (res := res) (μ := μ) (θ := θ) (v := v)
      h_join h_src hval

private lemma stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel')) masked CtxCons ValCons)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmap : List.mapM
      (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
      tcls = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm result2 htc2'
  have hstruct := terminatesTo_app_inv' e1 e2 cinit cf o ht
  rcases hstruct with h_clo | h_peclo
  · rcases h_clo with
      ⟨c₂', v₂, c₁, x, body, env, evalCfg, ht_e2, ht_e1, _hpm1, ht_body, heq_cfg, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hmasked_none2 : ∀ k, masked k → (ctxAfter ctxᵢ result2).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := ctxᵢ.regime) (R' := result2.regime')
          hmasked_none hmono2 k hk
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hcwr2 c₂'.nextAddr pm
        ((wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1) (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    have hTm1 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
    have hwf1 : wfTypeContext (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      wfTypeContext_of_wfTypeResult (ctxAfter ctxᵢ result2) result1
        (typecheckExpr_preserves_wfTypeResult (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1')
        hwf2 (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1')
    have htagR1 : regimeConsistentWithCtxMasked masked (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked
        masked (ctxAfter ctxᵢ result2) e1 fuel' result1 htagR2 htc1'
    have hmono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
      regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
    have hmasked_none1 :
        ∀ k, masked k → (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := (ctxAfter ctxᵢ result2).regime) (R' := result1.regime')
          hmasked_none2 hmono1 k hk
    have hv₁_arrow : valueHasETyp θ1 (Value.closure x body env) (ETyp.arrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_arrow with
    | closure _ _ _ =>
      obtain ⟨σcap, hσcap_mem, hσcap_typing, hcwr_body_raw⟩ :=
        ctxBodyStart
          ctxᵢ result2 result1 etyp2 p2 pred2
          st1 st2 p p1 tcls
          x body c₁.varEnv env
          c₂'.memory c₁.memory θ2 θ1 v₂
          hpredlaws hqt2 hetyp1 hmono1 hθext1
          hcwr1 hvalc2 hvalc1
      rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x body σcap hmap hσcap_mem with
        ⟨fuelBody, firstA, result3, happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
      have hfirstA_mem' : firstA ∈ first :: rest := by
        rcases list_mapM_ok_mem_input_exists_output
            (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
              ctxᵢ result1 fuel')
            hmap hσcap_mem with ⟨y, hy_mem, hy_eq⟩
        rw [← heq_results]
        have : y = firstA := Except.ok.inj (hy_eq.symm.trans happlyA)
        rwa [this] at hy_mem
      let bodyCtx : TypeContext :=
        { ctxᵢ with
          pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      have hcwr_body : CtxCons bodyCtx c₁.memory (env.update x v₂) θ1 := by
        simpa [bodyCtx] using hcwr_body_raw
      have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
        QTypRespectsTagMeaning_transport_etyp_pred
          (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
          (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
          (hqt2 ▸ typecheckExpr_preserves_QTypRespectsTagMeaning tm ctxᵢ e2 fuel' result2 hwfTm htc2') rfl rfl
      have hTmBody : wfTagMeaningCtx tm bodyCtx := by
        have hresTm1' : QTypRespectsTagMeaning tm result1.qualType :=
          typecheckExpr_preserves_QTypRespectsTagMeaning tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
        simpa [bodyCtx, ctxAfter] using
          wfTagMeaningCtx_closure_body
            (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
            (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
            (p := p) (tcls := tcls)
            (xFun := x) (body := body) (σcap := σcap)
            (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hTm1 hresTm1' hetyp1 hσcap_mem hargTm
      have htcBody' : typecheck bodyCtx body fuelBody = .ok result3 := by
        simpa [bodyCtx, typecheck] using htc_bodyA
      have hwfBody : wfTypeContext bodyCtx := by
        simp only [bodyCtx, wfTypeContext]
        have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
          (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
        have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
        exact ⟨hwf1.1,
          varEnvRefLocsBounded_update
            (varEnvRefLocsBounded_ofCaptured
              (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)))
            (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
          varEnvClosuresCapturedRefLocsBounded_update
            (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem))
            (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
      have harg_typed : valueHasETyp θ1 v₂ etyp2 := by
        simpa [hqt2] using valueHasETyp_extends hθext1.1 hv₂_typed
      have hric_body :
          runtimeInstantiatesCtx bodyCtx c₁.memory (env.update x v₂) θ1 := by
        let ctxCapBase : TypeContext :=
          { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
        have hric_cap_base :
            runtimeInstantiatesCtx (ctxAfter ctxCapBase result1)
              c₁.memory env θ1 := by
          constructor
          · intro l a hlookup
            exact hric1.1 l a hlookup
          · intro y qt hlookup
            have hlookup_list := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
            rcases hσcap_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
            exact ⟨v, hv, hσcap_typing.2.2 y qt v hlookup_list hv⟩
        have hric_body' :
            runtimeInstantiatesCtx
              { ctxCapBase with
                memEnv := result1.memEnv'
                tagEnv := result1.tagEnv'
                nextLoc := result1.nextLoc'
                nextTag := result1.nextTag'
                regime := result1.regime'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
              c₁.memory (env.update x v₂) θ1 :=
          runtimeInstantiatesCtx_closure_body
            (ctx := ctxCapBase) (result2 := result1) (x := x)
            (tenv := σcap)
            (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (argVal := v₂) (μ := c₁.memory) (ρ := env) (θ := θ1)
            hric_cap_base harg_typed
            (fun y qt hlookup => by
              have hl := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
              rcases hσcap_typing.2.1 y qt hl with ⟨v, hv⟩
              exact ⟨v, hv, hσcap_typing.2.2 y qt v hl hv⟩)
        simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body'
      have htagR_body : regimeConsistentWithCtxMasked masked bodyCtx := by
        simpa [bodyCtx, ctxAfter, regimeConsistentWithCtxMasked] using htagR1
      have hmasked_none_body : ∀ k, masked k → bodyCtx.regime.lookup? k = none := by
        intro k hk
        simpa [bodyCtx, ctxAfter] using hmasked_none1 k hk
      have hwfcfg_body_init :
          wfConfig
            { memory := c₁.memory
              varEnv := env.update x v₂
              nextAddr := c₁.nextAddr
              pureMode := false } := by
        have hwfcfg2 : wfConfig c₂' :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
        have hwfcfg1 : wfConfig c₁ :=
          (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).1
        have hv₂_wf_e2 : wfValue c₂'.nextAddr v₂ :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).2
        have hnext₂_to₁ : c₂'.nextAddr ≤ c₁.nextAddr :=
          terminatesTo_nextAddr_mono e1 c₂' c₁
            (Value.closure x body env) ht_e1
        have hv₂_wf : wfValue c₁.nextAddr v₂ :=
          wfValue_mono_of_le_nextAddr hnext₂_to₁ x v₂ hv₂_wf_e2
        have henv_wf : wfVarEnv c₁.nextAddr env := by
          cases (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).2 with
          | closure _ _ _ henv => exact henv
        constructor
        · intro a ha; exact hwfcfg1.1 a ha
        · simpa [VarEnv.update] using wfVarEnv.cons x v₂ env hv₂_wf henv_wf
      have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
        have : fuelBody < fuel' := by rw [hfuelA]; exact Nat.lt_succ_self _
        exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
      have hSingle_body := singleIH fuelBody hfuel_lt body bodyCtx hTmBody result3 htcBody'
      have hpc_body : bodyCtx.pc = true := by
        simp [bodyCtx, hpc, joinPoison]
      rcases
        hSingle_body hpredlaws hTmBody
          c₁.memory (env.update x v₂) θ1 evalCfg o
          hθ1wf hwfBody hric_body htagR_body hmasked_none_body hcwr_body
          c₁.nextAddr false hwfcfg_body_init ht_body hpc_body
        with ⟨θ_body, hθext_body, hv_body_typed, hric_body_final, hcwr_body_final, hvalc_body, hpres_body, _hfresh_body⟩
      have hθext : wfExtendsMap θ θ_body :=
        wfExtendsMap_trans hθext2 (wfExtendsMap_trans hθext1 hθext_body)
      have hfirstA_etyp : firstA.qualType.etyp = result3.qualType.etyp := by
        rw [hfirstA_eq]
        unfold normalizeAppResultByProvenance
        split <;> rfl
      have hmem_eq : cf.memory = evalCfg.memory := by
        simp [heq_cfg]
      have hvar_eq : cf.varEnv = c₁.varEnv := by
        simp [heq_cfg]
      have h_mono_body : Regime.monotoneStep bodyCtx.regime result3.regime' :=
        regime_monotone bodyCtx body fuelBody result3 htcBody'
      have hres1_to_firstA_mono :
          Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
            (ctxAfter ctxᵢ firstA).regime := by
        simpa [bodyCtx, ctxAfter, hfirstA_eq] using h_mono_body
      have hlookup_back_res1_to_A :
          ∀ k b,
            (ctxAfter ctxᵢ firstA).regime.lookup? k = some b →
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
        intro k b hk_src
        have hRdef_src : (ctxAfter ctxᵢ firstA).regime.lookup? k ≠ none := by
          intro hnone; rw [hk_src] at hnone; contradiction
        have hRdef_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
          hres1_to_firstA_mono.2 k hRdef_src
        cases hk_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
        | none => exact False.elim (hRdef_res1 hk_res1)
        | some b1 =>
            rcases hres1_to_firstA_mono.1 k b1 hk_res1 with hk_src' | hnone_src
            · have : some b1 = some b := hk_src'.symm.trans hk_src
              simpa using Option.some.inj this
            · rw [hnone_src] at hk_src
              cases hk_src
      have hric_final :
          runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        have hmem_to_res :
            ∀ l, firstA.memEnv'.contains l → res.memEnv'.contains l :=
          joinTypeResults_mem_contains_of_member
            (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest)
            (res := res) h_join hfirstA_mem'
        constructor
        · intro l a hθ
          have hloc := hric_body_final.1 l a hθ
          rcases hloc with ⟨hcontains_body, hmem_contains⟩
          have hcontains_src : firstA.memEnv'.contains l := by
            simpa [ctxAfter, hfirstA_eq] using hcontains_body
          exact ⟨hmem_to_res l hcontains_src, by simpa [hmem_eq] using hmem_contains⟩
        · intro y qt hlookup
          have hlookup_ctx :
              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup y = some qt := by
            simpa [ctxAfter] using hlookup
          rcases hric1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
          exact ⟨v, by simpa [hvar_eq] using hlookup_v, valueHasETyp_extends hθext_body.1 hv_typ⟩
      have hcwr_src :
          CtxCons (ctxAfter ctxᵢ firstA) cf.memory cf.varEnv θ_body := by
        have hpred_compat :
            ∀ (qt' : QTyp) (v' : Value),
              qtypPredHolds predSat qt' c₁.memory v' ↔ qtypPredHolds predSat qt' cf.memory v' :=
          qtypPredHolds_mem_compat_of_predSatLaws
            (hpredlaws := hpredlaws) (θ := θ1) (μ := c₁.memory) (μ' := cf.memory)
        exact
          ctxMember
            ctxᵢ bodyCtx result2 result1 firstA result3
            (normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
            c₁ evalCfg cf θ1 θ_body
            hpred_compat hfirstA_eq hmem_eq hvar_eq
            hlookup_back_res1_to_A hθext_body hcwr1 hcwr_body_final
      have hcwr_final :
          CtxCons (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        exact ctxJoinMember ctxᵢ first firstA rest res cf.memory cf.varEnv θ_body
          h_join hfirstA_mem' hcwr_src
      have hval_src :
          ValCons (ctxAfter ctxᵢ firstA).regime
            firstA.qualType cf.memory θ_body o := by
        exact
          valBodyResult ctxᵢ bodyCtx firstA result3 p p1 cf.memory evalCfg.memory θ_body o
            hfirstA_eq hmem_eq hvalc_body
      have hvalc_final :
          ValCons (ctxAfter ctxᵢ res).regime
            res.qualType cf.memory θ_body o := by
        exact valJoinMember ctxᵢ first firstA rest res cf.memory θ_body o
          h_join hfirstA_mem' hval_src
      have hpres_final :
          PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ_body := by
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hcontains_ctx : ctxᵢ.memEnv.contains l :=
          memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
        have hcontains2 : result2.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxᵢ) (e := e2) (fuel := fuel') (res := result2) htc2' l hcontains_ctx
        rcases memEnv_lookup_some_of_contains result2.memEnv' l hcontains2 with
          ⟨qt2, hlookup2⟩
        have hcontains1 : result1.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1) htc1' l
            (by simpa [ctxAfter] using hcontains2)
        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains1 with
          ⟨qt1, hlookup1⟩
        have hcontains3 : result3.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3) htcBody' l
            (by simpa [bodyCtx] using hcontains1)
        rcases memEnv_lookup_some_of_contains result3.memEnv' l hcontains3 with
          ⟨qt3, hlookup3⟩
        have hlookup_firstA : firstA.memEnv'.lookup l = some qt3 := by
          simpa [hfirstA_eq] using hlookup3
        have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_out := by
          simpa [ctxAfter] using hlookup_out
        have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_out := by
          simpa [ctxAfter] using hclean_out
        have hlookup_firstA_ctx : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
          simpa [ctxAfter] using hlookup_firstA
        have hclean3_firstA :
            qtypCleanUnder (ctxAfter ctxᵢ firstA).regime qt3 := by
          exact
            joinTypeResults_lookup_member_clean_compat
              (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
              h_join hfirstA_mem' l qt_out qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx
        have hclean3 : qtypCleanUnder result3.regime' qt3 := by
          simpa [ctxAfter, hfirstA_eq] using hclean3_firstA
        have hclean1 : qtypCleanUnder result1.regime' qt1 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
              htc_bodyA hwfBody hpc_body l qt1 qt3
              (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
        have hclean2 : qtypCleanUnder result2.regime' qt2 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
              (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
              (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
        have hpres_l2 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxᵢ) (res := result2) (μ_in := μ) (μ_out := c₂'.memory)
            (θ_in := θ) (θ_out := θ2)
            hpres2 hlookup_in hlookup2 hclean2
        have hpres_l1 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxAfter ctxᵢ result2) (res := result1)
            (μ_in := c₂'.memory) (μ_out := c₁.memory)
            (θ_in := θ2) (θ_out := θ1)
            hpres1
            (by simpa [ctxAfter] using hlookup2)
            hlookup1 hclean1
        have hpres_lbody :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := bodyCtx) (res := result3)
            (μ_in := c₁.memory) (μ_out := evalCfg.memory)
            (θ_in := θ1) (θ_out := θ_body)
            hpres_body
            (by simpa [bodyCtx] using hlookup1)
            hlookup3 hclean3
        have hpres_lbody' :
            PreservesInheritedCleanLocOneRun c₁.memory cf.memory θ1 θ_body l := by
          simpa [hmem_eq] using hpres_lbody
        exact
          PreservesInheritedCleanLocOneRun.trans hpres_l2
            (PreservesInheritedCleanLocOneRun.trans hpres_l1 hpres_lbody')
      have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ_body := by
        intro l qt_f hnotIn hlookup_f hclean_f
        by_cases hc3 : result3.memEnv'.contains l
        · by_cases hc1 : result1.memEnv'.contains l
          · by_cases hc2 : result2.memEnv'.contains l
            · -- Case 4: l ∈ result2.memEnv' but l ∉ ctxᵢ.memEnv
              rcases memEnv_lookup_some_of_contains result2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  htc_bodyA hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
                  (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
                  (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ2_none := _hfresh2 l qt2 hnotIn hlookup2 hclean2
              have hpres_l1' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxAfter ctxᵢ result2) (res := result1)
                  (μ_in := c₂'.memory) (μ_out := c₁.memory) (θ_in := θ2) (θ_out := θ1)
                  hpres1 (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ1_none : θ1.lookup l = none := by
                cases hpres_l1' with
                | both_unrealized _ h_out => exact h_out
                | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ2_none]; exact nofun)
              have hpres_lbody' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := c₁.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              cases hpres_lbody' with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
            · -- Case 3: l ∉ result2.memEnv' but l ∈ result1.memEnv'
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  htc_bodyA hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hθ1_none := _hfresh1 l qt1 (by simpa [ctxAfter] using hc2) hlookup1 hclean1
              have hpres_lbody' :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := c₁.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              cases hpres_lbody' with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
          · -- Case 2: l ∉ result1.memEnv' but l ∈ result3.memEnv'
            rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
            have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
              simpa [ctxAfter, hfirstA_eq] using hlookup3
            have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
              simpa [ctxAfter] using hlookup_f
            have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
              simpa [ctxAfter] using hclean_f
            have hclean3 : qtypCleanUnder result3.regime' qt3 := by
              simpa [ctxAfter, hfirstA_eq] using
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                  h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
            exact _hfresh_body l qt3 (by simpa [bodyCtx] using hc1) hlookup3 hclean3
        · -- Case 1: l ∉ result3.memEnv'
          exact
            theta_not_contains_if_not_in_memEnv
              (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θ_body l
              hric_body_final (by simpa [ctxAfter] using hc3)
      refine ⟨θ_body, hθext, ?_, hric_final, hcwr_final, hvalc_final, hpres_final, hfresh_final⟩
      exact
        joinTypeResults_transport_valueHasETyp_from_member
          (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
          (θ := θ_body) (v := o)
          h_join hfirstA_mem' (hfirstA_etyp ▸ hv_body_typed)
  · rcases h_peclo with
      ⟨c₂', v₂, c₁, x, body, env, _evalCfg, ht_e2, ht_e1, _htoPExpr, _ht_body, _hcf, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hmasked_none2 : ∀ k, masked k → (ctxAfter ctxᵢ result2).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := ctxᵢ.regime) (R' := result2.regime')
          hmasked_none hmono2 k hk
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_peClosure_etyp_parrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _ptcls, hparr⟩
    rw [hetyp1] at hparr
    cases hparr

private lemma stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric_maskedReg
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxBodyStart :
    AppPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel')) masked CtxCons ValCons)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmap : List.mapM
      (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
      tcls = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm result2 htc2'
  have hstruct := terminatesTo_app_inv' e1 e2 cinit cf o ht
  rcases hstruct with h_clo | h_peclo
  · rcases h_clo with
      ⟨c₂', v₂, c₁, x, body, env, _evalCfg, ht_e2, ht_e1, _hpm1, _ht_body, _heq_cfg, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hmasked_none2 : ∀ k, masked k → (ctxAfter ctxᵢ result2).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := ctxᵢ.regime) (R' := result2.regime')
          hmasked_none hmono2 k hk
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_closure_etyp_arrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _tcls, harrow⟩
    rw [hetyp1] at harrow
    cases harrow
  · rcases h_peclo with
      ⟨c₂', v₂, c₁, x, body, env, evalCfg, ht_e2, ht_e1, _htoPExpr_body, ht_body, hcf, hpm_e2, _⟩
    rcases
      hIH_e2 hpredlaws hwfTm μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
    have hTm2 : wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm ctxᵢ e2 fuel' result2 hwfTm htc2'
    have hwf2 : wfTypeContext (ctxAfter ctxᵢ result2) :=
      wfTypeContext_of_wfTypeResult ctxᵢ result2
        (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
        hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
    have htagR2 : regimeConsistentWithCtxMasked masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked masked ctxᵢ e2 fuel' result2 htagR htc2'
    have hmono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' :=
      regime_monotone ctxᵢ e2 fuel' result2 htc2'
    have hmasked_none2 : ∀ k, masked k → (ctxAfter ctxᵢ result2).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := ctxᵢ.regime) (R' := result2.regime')
          hmasked_none hmono2 k hk
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [show pm = c₂'.pureMode from hpm2.symm]
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
    rcases
      hIH_e1 hpredlaws hTm2 c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    have hTm1 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_wfTagMeaningCtx tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
    have hwf1 : wfTypeContext (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      wfTypeContext_of_wfTypeResult (ctxAfter ctxᵢ result2) result1
        (typecheckExpr_preserves_wfTypeResult (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1')
        hwf2 (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1')
    have htagR1 : regimeConsistentWithCtxMasked masked (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_regimeConsistentWithCtxMasked
        masked (ctxAfter ctxᵢ result2) e1 fuel' result1 htagR2 htc1'
    have hmono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
      regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
    have hmasked_none1 :
        ∀ k, masked k → (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = none := by
      intro k hk
      simpa [ctxAfter] using
        masked_lookup_none_of_monotoneStep
          (R := (ctxAfter ctxᵢ result2).regime) (R' := result1.regime')
          hmasked_none2 hmono1 k hk
    have hv₁_parrow : valueHasETyp θ1 (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_parrow with
    | peClosure _ _ _ _ =>
      obtain ⟨σcap, pbody, htoPExpr, hσcap_mem, hσcap_typing, hcwr_body_raw⟩ :=
        ctxBodyStart
          ctxᵢ result2 result1 etyp2 p2 pred2
          st1 st2 p p1 tcls
          x body cf.varEnv env
          c₂'.memory cf.memory θ2 θ1 v₂
          hpredlaws hqt2 hetyp1 hmono1 hθext1
          (by simpa [hcf] using hcwr1) hvalc2 (by simpa [hcf] using hvalc1)
      have hbody_eq : PExpr.toExpr pbody = body :=
        PExpr_toExpr_of_toPExpr?_some body pbody htoPExpr
      rcases applyPFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x pbody σcap hmap hσcap_mem with
        ⟨fuelBody, firstA, result3, happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
      have hfirstA_mem' : firstA ∈ first :: rest := by
        rcases list_mapM_ok_mem_input_exists_output
            (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
              ctxᵢ result1 fuel')
            hmap hσcap_mem with ⟨y, hy_mem, hy_eq⟩
        rw [← heq_results]
        have : y = firstA := Except.ok.inj (hy_eq.symm.trans happlyA)
        rwa [this] at hy_mem
      let bodyCtx : TypeContext :=
        { ctxᵢ with
          pc := joinPoison p (joinPoison ctxᵢ.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
      have hcwr_body : CtxCons bodyCtx cf.memory (env.update x v₂) θ1 := by
        simpa [bodyCtx] using hcwr_body_raw
      have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
        QTypRespectsTagMeaning_transport_etyp_pred
          (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
          (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
          (hqt2 ▸ typecheckExpr_preserves_QTypRespectsTagMeaning tm ctxᵢ e2 fuel' result2 hwfTm htc2') rfl rfl
      have hTmBody : wfTagMeaningCtx tm bodyCtx := by
        have hresTm1' : QTypRespectsTagMeaning tm result1.qualType :=
          typecheckExpr_preserves_QTypRespectsTagMeaning tm (ctxAfter ctxᵢ result2) e1 fuel' result1 hTm2 htc1'
        simpa [bodyCtx, ctxAfter] using
          wfTagMeaningCtx_pclosure_body
            (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
            (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
            (p := p) (tcls := tcls)
            (xFun := x) (pbody := pbody) (σcap := σcap)
            (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hTm1 hresTm1' hetyp1 hσcap_mem hargTm
      have htcBody' : typecheck bodyCtx (PExpr.toExpr pbody) fuelBody = .ok result3 := by
        simpa [bodyCtx, typecheck] using htc_bodyA
      have htcBody_body : typecheck bodyCtx body fuelBody = .ok result3 := by
        rw [← hbody_eq]
        exact htcBody'
      have hwfBody : wfTypeContext bodyCtx := by
        simp only [bodyCtx, wfTypeContext]
        have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
          (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
        have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
        exact ⟨hwf1.1,
          varEnvRefLocsBounded_update
            (varEnvRefLocsBounded_ofCaptured
              (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)))
            (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
          varEnvClosuresCapturedRefLocsBounded_update
            (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem))
            (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
      have harg_typed : valueHasETyp θ1 v₂ etyp2 := by
        simpa [hqt2] using valueHasETyp_extends hθext1.1 hv₂_typed
      have hric_body :
          runtimeInstantiatesCtx bodyCtx cf.memory (env.update x v₂) θ1 := by
        let ctxCapBase : TypeContext :=
          { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
        have hric_cap_base :
            runtimeInstantiatesCtx (ctxAfter ctxCapBase result1)
              cf.memory env θ1 := by
          constructor
          · intro l a hlookup
            have : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1) c₁.memory c₁.varEnv θ1 := hric1
            simpa [ctxAfter, hcf] using this.1 l a hlookup
          · intro y qt hlookup
            have hlookup_list := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
            rcases hσcap_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
            exact ⟨v, by simpa [hcf] using hv, hσcap_typing.2.2 y qt v hlookup_list (by simpa [hcf] using hv)⟩
        have hric_body' :
            runtimeInstantiatesCtx
              { ctxCapBase with
                memEnv := result1.memEnv'
                tagEnv := result1.tagEnv'
                nextLoc := result1.nextLoc'
                nextTag := result1.nextTag'
                regime := result1.regime'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
              cf.memory (env.update x v₂) θ1 :=
          runtimeInstantiatesCtx_closure_body
            (ctx := ctxCapBase) (result2 := result1) (x := x)
            (tenv := σcap)
            (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (argVal := v₂) (μ := cf.memory) (ρ := env) (θ := θ1)
            hric_cap_base harg_typed
            (fun y qt hlookup => by
              have hl := list_lookup_of_ofCaptured_lookup σcap y qt hlookup
              rcases hσcap_typing.2.1 y qt hl with ⟨v, hv⟩
              exact ⟨v, by simpa [hcf] using hv, hσcap_typing.2.2 y qt v hl (by simpa [hcf] using hv)⟩)
        simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body'
      have htagR_body : regimeConsistentWithCtxMasked masked bodyCtx := by
        simpa [bodyCtx, ctxAfter, regimeConsistentWithCtxMasked] using htagR1
      have hmasked_none_body : ∀ k, masked k → bodyCtx.regime.lookup? k = none := by
        intro k hk
        simpa [bodyCtx, ctxAfter] using hmasked_none1 k hk
      have hwfcfg1 : wfConfig cf := by
        simpa [hcf] using (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).1
      have hwfcfg_body_init :
          wfConfig
            { memory := cf.memory
              varEnv := env.update x v₂
              nextAddr := cf.nextAddr
              pureMode := true } := by
        have hv₂_wf_e2 : wfValue c₂'.nextAddr v₂ :=
          (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).2
        have hnext₂_to₁ : c₂'.nextAddr ≤ cf.nextAddr := by
          simpa [hcf] using
            (terminatesTo_nextAddr_mono e1 c₂' c₁ (Value.peClosure x body env) ht_e1)
        have hv₂_wf : wfValue cf.nextAddr v₂ :=
          wfValue_mono_of_le_nextAddr hnext₂_to₁ x v₂ hv₂_wf_e2
        have henv_wf : wfVarEnv cf.nextAddr env := by
          have hwf_val := (wfConfig_preserved e1 _ c₁ _ ht_e1 hwfcfg2).2
          cases hwf_val with
          | peClosure _ _ _ henv =>
              simpa [hcf] using henv
        constructor
        · intro a ha
          exact hwfcfg1.1 a ha
        · simpa [VarEnv.update] using wfVarEnv.cons x v₂ env hv₂_wf henv_wf
      have ht_body' : terminatesTo body
          { memory := cf.memory, varEnv := env.update x v₂,
            nextAddr := cf.nextAddr, pureMode := true } evalCfg o := by
        simpa [hcf] using ht_body
      have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
        have : fuelBody < fuel' := by rw [hfuelA]; exact Nat.lt_succ_self _
        exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
      have hSingle_body := singleIH fuelBody hfuel_lt body bodyCtx hTmBody result3 htcBody_body
      have hpc_body : bodyCtx.pc = true := by
        simp [bodyCtx, hpc, joinPoison]
      rcases
        hSingle_body hpredlaws hTmBody
          cf.memory (env.update x v₂) θ1 evalCfg o
          hθ1wf hwfBody hric_body htagR_body hmasked_none_body hcwr_body
          cf.nextAddr true hwfcfg_body_init ht_body' hpc_body
        with ⟨θ_body, hθext_body, hv_body_typed, hric_body_final, hcwr_body_final, hvalc_body, hpres_body, _hfresh_body⟩
      have hθext : wfExtendsMap θ θ_body :=
        wfExtendsMap_trans hθext2 (wfExtendsMap_trans hθext1 hθext_body)
      have hfirstA_etyp : firstA.qualType.etyp = result3.qualType.etyp := by
        rw [hfirstA_eq]
        unfold normalizeAppResultByProvenance
        split <;> rfl
      have h_mono_body : Regime.monotoneStep bodyCtx.regime result3.regime' :=
        regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3 htcBody'
      have hres1_to_firstA_mono :
          Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
            (ctxAfter ctxᵢ firstA).regime := by
        simpa [bodyCtx, ctxAfter, hfirstA_eq] using h_mono_body
      have hlookup_back_res1_to_A :
          ∀ k b,
            (ctxAfter ctxᵢ firstA).regime.lookup? k = some b →
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
        intro k b hk_src
        have hRdef_src : (ctxAfter ctxᵢ firstA).regime.lookup? k ≠ none := by
          intro hnone; rw [hk_src] at hnone; contradiction
        have hRdef_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
          hres1_to_firstA_mono.2 k hRdef_src
        cases hk_res1 :
            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
        | none => exact False.elim (hRdef_res1 hk_res1)
        | some b1 =>
            rcases hres1_to_firstA_mono.1 k b1 hk_res1 with hk_src' | hnone_src
            · have : some b1 = some b := hk_src'.symm.trans hk_src
              simpa using Option.some.inj this
            · rw [hnone_src] at hk_src
              cases hk_src
      have hmem_eq : cf.memory = evalCfg.memory := by
        obtain ⟨fuel_b, verbose_b, hbeval_b⟩ := ht_body'
        exact (beval_pure_memory_eq body fuel_b _ evalCfg o verbose_b
          pbody
          htoPExpr rfl hbeval_b).symm
      have hric_final :
          runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        have hmem_to_res :
            ∀ l, firstA.memEnv'.contains l → res.memEnv'.contains l :=
          joinTypeResults_mem_contains_of_member
            (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest)
            (res := res) h_join hfirstA_mem'
        constructor
        · intro l a hθ
          have hloc := hric_body_final.1 l a hθ
          rcases hloc with ⟨hcontains_body, hmem_contains⟩
          have hcontains_src : firstA.memEnv'.contains l := by
            simpa [ctxAfter, hfirstA_eq] using hcontains_body
          exact ⟨hmem_to_res l hcontains_src, by simpa [hmem_eq] using hmem_contains⟩
        · intro y qt hlookup
          have hlookup_ctx :
              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup y = some qt := by
            simpa [ctxAfter] using hlookup
          have hric1_cf :
              runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1)
                cf.memory cf.varEnv θ1 := by
            simpa [hcf] using hric1
          rcases hric1_cf.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
          exact ⟨v, hlookup_v, valueHasETyp_extends hθext_body.1 hv_typ⟩
      have hcwr_src :
          CtxCons (ctxAfter ctxᵢ firstA) cf.memory cf.varEnv θ_body := by
        have hpred_compat :
            ∀ (qt' : QTyp) (v' : Value),
              qtypPredHolds predSat qt' cf.memory v' ↔ qtypPredHolds predSat qt' cf.memory v' :=
          fun _ _ => Iff.rfl
        exact
          ctxMember
            ctxᵢ bodyCtx result2 result1 firstA result3
            (normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
            cf evalCfg cf θ1 θ_body
            hpred_compat hfirstA_eq hmem_eq rfl
            hlookup_back_res1_to_A hθext_body
            (by simpa [hcf] using hcwr1) hcwr_body_final
      have hcwr_final :
          CtxCons (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
        exact ctxJoinMember ctxᵢ first firstA rest res cf.memory cf.varEnv θ_body
          h_join hfirstA_mem' hcwr_src
      have hval_src :
          ValCons (ctxAfter ctxᵢ firstA).regime
            firstA.qualType cf.memory θ_body o := by
        exact
          valBodyResult ctxᵢ bodyCtx firstA result3 p p1 cf.memory evalCfg.memory θ_body o
            hfirstA_eq hmem_eq hvalc_body
      have hvalc_final :
          ValCons (ctxAfter ctxᵢ res).regime
            res.qualType cf.memory θ_body o := by
        exact valJoinMember ctxᵢ first firstA rest res cf.memory θ_body o
          h_join hfirstA_mem' hval_src
      have hpres_final :
          PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ_body := by
        refine ⟨?_⟩
        intro l qt_in qt_out hlookup_in hlookup_out hclean_out
        have hcontains_ctx : ctxᵢ.memEnv.contains l :=
          memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
        have hcontains2 : result2.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxᵢ) (e := e2) (fuel := fuel') (res := result2) htc2' l hcontains_ctx
        rcases memEnv_lookup_some_of_contains result2.memEnv' l hcontains2 with
          ⟨qt2, hlookup2⟩
        have hcontains1 : result1.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1) htc1' l
            (by simpa [ctxAfter] using hcontains2)
        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains1 with
          ⟨qt1, hlookup1⟩
        have hcontains3 : result3.memEnv'.contains l :=
          typecheckExpr_mem_contains_preserved
            (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3) htcBody_body l
            (by simpa [bodyCtx] using hcontains1)
        rcases memEnv_lookup_some_of_contains result3.memEnv' l hcontains3 with
          ⟨qt3, hlookup3⟩
        have hlookup_firstA : firstA.memEnv'.lookup l = some qt3 := by
          simpa [hfirstA_eq] using hlookup3
        have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_out := by
          simpa [ctxAfter] using hlookup_out
        have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_out := by
          simpa [ctxAfter] using hclean_out
        have hlookup_firstA_ctx : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
          simpa [ctxAfter] using hlookup_firstA
        have hclean3_firstA :
            qtypCleanUnder (ctxAfter ctxᵢ firstA).regime qt3 := by
          exact
            joinTypeResults_lookup_member_clean_compat
              (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
              h_join hfirstA_mem' l qt_out qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx
        have hclean3 : qtypCleanUnder result3.regime' qt3 := by
          simpa [ctxAfter, hfirstA_eq] using hclean3_firstA
        have hclean1 : qtypCleanUnder result1.regime' qt1 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
              (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
              (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
        have hclean2 : qtypCleanUnder result2.regime' qt2 := by
          exact
            typecheckExpr_lookup_clean_back_of_pc_true
              (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
              (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
              (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
        have hpres_l2 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxᵢ) (res := result2) (μ_in := μ) (μ_out := c₂'.memory)
            (θ_in := θ) (θ_out := θ2)
            hpres2 hlookup_in hlookup2 hclean2
        have hpres_l1 :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := ctxAfter ctxᵢ result2) (res := result1)
            (μ_in := c₂'.memory) (μ_out := c₁.memory)
            (θ_in := θ2) (θ_out := θ1)
            hpres1
            (by simpa [ctxAfter] using hlookup2)
            hlookup1 hclean1
        have hpres_l1' :
            PreservesInheritedCleanLocOneRun c₂'.memory cf.memory θ2 θ1 l := by
          simpa [hcf] using hpres_l1
        have hpres_lbody :=
          PreservesInheritedFinalCleanLocsOneRun.apply
            (ctx := bodyCtx) (res := result3)
            (μ_in := cf.memory) (μ_out := evalCfg.memory)
            (θ_in := θ1) (θ_out := θ_body)
            hpres_body
            (by simpa [bodyCtx] using hlookup1)
            hlookup3 hclean3
        have hpres_lbody' :
            PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
          simpa [hmem_eq] using hpres_lbody
        exact
          PreservesInheritedCleanLocOneRun.trans hpres_l2
            (PreservesInheritedCleanLocOneRun.trans hpres_l1' hpres_lbody')
      have hfresh_final : FreshCleanLocsUnrealizedOneRun ctxᵢ res θ_body := by
        intro l qt_f hnotIn hlookup_f hclean_f
        by_cases hc3 : result3.memEnv'.contains l
        · by_cases hc1 : result1.memEnv'.contains l
          · by_cases hc2 : result2.memEnv'.contains l
            · -- Case 4: l ∈ result2.memEnv' but l ∉ ctxᵢ.memEnv
              rcases memEnv_lookup_some_of_contains result2.memEnv' l hc2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := ctxAfter ctxᵢ result2) (e := e1) (fuel := fuel') (res := result1)
                  (by simpa [typecheck] using htc1') hwf2 hpc2 l qt2 qt1
                  (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ2_none := _hfresh2 l qt2 hnotIn hlookup2 hclean2
              have hpres_l1_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxAfter ctxᵢ result2) (res := result1)
                  (μ_in := c₂'.memory) (μ_out := c₁.memory) (θ_in := θ2) (θ_out := θ1)
                  hpres1 (by simpa [ctxAfter] using hlookup2) hlookup1 hclean1
              have hθ1_none : θ1.lookup l = none := by
                have hpres_cf : PreservesInheritedCleanLocOneRun c₂'.memory cf.memory θ2 θ1 l := by
                  simpa [hcf] using hpres_l1_loc
                cases hpres_cf with
                | both_unrealized _ h_out => exact h_out
                | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ2_none]; exact nofun)
              have hpres_lbody_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := cf.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hpres_lbody_cf : PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
                simpa [hmem_eq] using hpres_lbody_loc
              cases hpres_lbody_cf with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
            · -- Case 3: l ∉ result2.memEnv' but l ∈ result1.memEnv'
              rcases memEnv_lookup_some_of_contains result1.memEnv' l hc1 with ⟨qt1, hlookup1⟩
              rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
              have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
                simpa [ctxAfter, hfirstA_eq] using hlookup3
              have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
                simpa [ctxAfter] using hlookup_f
              have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
                simpa [ctxAfter] using hclean_f
              have hclean3 : qtypCleanUnder result3.regime' qt3 := by
                simpa [ctxAfter, hfirstA_eq] using
                  joinTypeResults_lookup_member_clean_compat
                    (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                    h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
              have hclean1 : qtypCleanUnder result1.regime' qt1 :=
                typecheckExpr_lookup_clean_back_of_pc_true
                  (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                  (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                  (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hθ1_none := _hfresh1 l qt1 (by simpa [ctxAfter] using hc2) hlookup1 hclean1
              have hpres_lbody_loc :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := bodyCtx) (res := result3)
                  (μ_in := cf.memory) (μ_out := evalCfg.memory) (θ_in := θ1) (θ_out := θ_body)
                  hpres_body (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
              have hpres_lbody_cf : PreservesInheritedCleanLocOneRun cf.memory cf.memory θ1 θ_body l := by
                simpa [hmem_eq] using hpres_lbody_loc
              cases hpres_lbody_cf with
              | both_unrealized _ h_out => exact h_out
              | preserve_value _ _ h_in => exact absurd h_in (by rw [hθ1_none]; exact nofun)
          · -- Case 2: l ∉ result1.memEnv' but l ∈ result3.memEnv'
            rcases memEnv_lookup_some_of_contains result3.memEnv' l hc3 with ⟨qt3, hlookup3⟩
            have hlookup_firstA_ctx' : (ctxAfter ctxᵢ firstA).memEnv.lookup l = some qt3 := by
              simpa [ctxAfter, hfirstA_eq] using hlookup3
            have hlookup_res_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_f := by
              simpa [ctxAfter] using hlookup_f
            have hclean_res_ctx : qtypCleanUnder (ctxAfter ctxᵢ res).regime qt_f := by
              simpa [ctxAfter] using hclean_f
            have hclean3 : qtypCleanUnder result3.regime' qt3 := by
              simpa [ctxAfter, hfirstA_eq] using
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
                  h_join hfirstA_mem' l qt_f qt3 hlookup_res_ctx hclean_res_ctx hlookup_firstA_ctx'
            exact _hfresh_body l qt3 (by simpa [bodyCtx] using hc1) hlookup3 hclean3
        · -- Case 1: l ∉ result3.memEnv'
          exact
            theta_not_contains_if_not_in_memEnv
              (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θ_body l
              hric_body_final (by simpa [ctxAfter] using hc3)
      refine ⟨θ_body, hθext, ?_, hric_final, hcwr_final, hvalc_final, hpres_final, hfresh_final⟩
      exact
        joinTypeResults_transport_valueHasETyp_from_member
          (ctx := ctxᵢ) (first := first) (src := firstA) (rest := rest) (res := res)
          (θ := θ_body) (v := o)
          h_join hfirstA_mem' (hfirstA_etyp ▸ hv_body_typed)

private lemma stepFRSingleRunFinalCleanPcTrue_app_parametric_maskedReg
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxClosureBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (ctxPClosureBodyStart :
    AppPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel')) masked CtxCons ValCons)
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  have htcApp : typecheckApp ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    rw [← typecheckExpr_app_succ ctxᵢ e1 e2 (Nat.succ fuel')]
    simpa [typecheck] using htc
  obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, h_arrow_or_parrow⟩ :=
    typecheckApp_arrow_structure_full ctxᵢ e1 e2 fuel' res htcApp
  have htc2' : typecheck ctxᵢ e2 fuel' = .ok result2 := by
    simpa [typecheck] using htc2
  have htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
    simp [ctxAfter] at htc1 ⊢
    exact htc1
  cases h_arrow_or_parrow with
  | inl h_arrow =>
      obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1, _hnpure,
        _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_arrow
      exact
        stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg
          masked CtxCons ValCons ctxᵢ predSat tm
          ctxClosureBodyStart ctxMember ctxJoinMember valBodyResult valJoinMember
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join
  | inr h_parrow =>
      obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1,
        _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_parrow
      exact
        stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric_maskedReg
          masked CtxCons ValCons ctxᵢ predSat tm
          ctxPClosureBodyStart ctxMember ctxJoinMember valBodyResult valJoinMember
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join

lemma stepFRSingleRunFinalCleanPcTrue_app_maskedReg
  (masked : Tag → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel'))
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v))
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    ctxᵢ (Expr.app e1 e2) res predSat tm := by
  exact
    stepFRSingleRunFinalCleanPcTrue_app_parametric_maskedReg
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctxᵢ predSat tm
      (stepFRApp_closureBodyStart_masked masked predSat tm)
      (stepFRApp_pClosureBodyStart_masked masked predSat tm)
      (stepFRApp_memberCtxCons_masked masked predSat)
      (stepFRApp_joinCtxConsFromMember_masked masked predSat)
      (stepFRApp_bodyResultValCons_masked masked predSat)
      (stepFRApp_joinValConsFromMember_masked masked predSat)
      e1 e2 fuel' res
      singleIH htc

-- Function application case: reduces to helper lemmas for closure/closure and peClosure branches
lemma stepFR_app
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (singleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR ctxᵢ (Expr.app e1 e2) res predSat tm := by
  -- Phase 1: Typecheck decomposition (typecheck = typecheckExpr; app case reduces to typecheckApp)
  have htcApp : typecheckApp ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    rw [← typecheckExpr_app_succ ctxᵢ e1 e2 (Nat.succ fuel')]
    simpa [typecheck] using htc
  obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, h_arrow_or_parrow⟩ :=
    typecheckApp_arrow_structure_full ctxᵢ e1 e2 fuel' res htcApp
  cases h_arrow_or_parrow with
  | inl h_arrow =>
    -- Arrow case (closure)
    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, hp1, _hnpure, _hnempty, _hsub,
            hmap, heq_results, h_join⟩ := h_arrow
    have htc2' : typecheck ctxᵢ e2 fuel' = .ok result2 := by
      simpa [typecheck] using htc2
    have htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
      simp [ctxAfter] at htc1 ⊢
      exact htc1
    intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2 (e1 IH defined after we have hTm2 from e2)
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm htagBounded result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    have hstruct₀ := terminatesTo_app_inv' e1 e2 cinit₀ cf₀ o₀ ht₀
    have hstruct₁ := terminatesTo_app_inv' e1 e2 cinit₁ cf₁ o₁ ht₁
    -- Handle runtime closure/peClosure splits for the arrow-typed branch.
    rcases hstruct₀ with h_clo₀ | h_peclo₀
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Both runs: closure
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        -- Phase A: Apply IH for e2
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        -- Phase B: Apply IH for e1
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        -- Phase C: Invert closure typing to extract FnTClosure structure
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        have hv₁1_arrow : valueHasETyp θ₁1 (Value.closure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        -- Invert closure typing for both runs
        cases hv₀1_arrow with
        | closure htcl₀ henv₀_typing hcover₀ =>
        cases hv₁1_arrow with
        | closure htcl₁ henv₁_typing hcover₁ =>
        -- Phase D: Extract body typing from applyFnTClosure via mapM membership
        rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₀ body₀ _ hmap htcl₀
          with ⟨fuelBody₀, first₀, result3₀, _happly₀, hfuel₀, htc_body₀, _hsub₀, hfirst₀_eq⟩
        rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₁ body₁ _ hmap htcl₁
          with ⟨fuelBody₁, first₁, result3₁, _happly₁, hfuel₁, htc_body₁, _hsub₁, hfirst₁_eq⟩
        have hfirst₀_mem : first₀ ∈ results := by
          rcases applyFnTClosure_ok_of_mem_mapM
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            (FnTClosure.regular x₀ body₀ _) hmap htcl₀ with ⟨r, hr_mem, happly_r⟩
          have heq : r = first₀ := @Except.ok.inj String TypeResult r first₀ (by simpa [happly_r] using _happly₀)
          subst heq
          exact hr_mem
        have hfirst₁_mem : first₁ ∈ results := by
          rcases applyFnTClosure_ok_of_mem_mapM
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            (FnTClosure.regular x₁ body₁ _) hmap htcl₁ with ⟨r, hr_mem, happly_r⟩
          have heq : r = first₁ := @Except.ok.inj String TypeResult r first₁ (by simpa [happly_r] using _happly₁)
          subst heq
          exact hr_mem
        -- Synchronization is used only under a clean-result assumption for `result1`.
        -- Keep it deferred to avoid requiring a global clean fact at this point.
        have _hsync1_of_clean :
              ∀ hclean1_e1 :
                  qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                (∃ σcap,
                    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                    x₀ = x₁ ∧
                    body₀ = body₁ ∧
                    agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory σcap env₀ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory θ₀1 σcap env₀ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory σcap env₁ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory θ₁1 σcap env₁)
                ∨ (¬ internalPoisonClean result1.qualType) :=
          fun hclean1_e1 =>
            stepFR_app_arrow_sync_from_clean
              (predSat := predSat)
              (ctx := (ctxAfter ctxᵢ result2))
              (res1 := result1)
              (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
              (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
              (θ₀ := θ₀1) (θ₁ := θ₁1)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              (env₀ := env₀) (env₁ := env₁)
              hetyp1 hclean1_e1 hres_agree1
        have _hextract_shared_of_sync :
            (∃ σcap,
                FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                x₀ = x₁ ∧
                body₀ = body₁) →
              ∃ σcap fuelBody first result3,
                FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                x₀ = x₁ ∧
                body₀ = body₁ ∧
                applyFnTClosure (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
                  etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok first ∧
                fuel' = Nat.succ fuelBody ∧
                typecheckExpr
                  { ctxᵢ with
                    pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                    memEnv := result1.memEnv'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                    tagEnv := result1.tagEnv'
                    nextTag := result1.nextTag'
                    nextLoc := result1.nextLoc'
                    regime := result1.regime' } body₀ fuelBody = .ok result3 ∧
                isSubtype st2 result3.qualType = true ∧
                first =
                  { result3 with
                    qualType :=
                      normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } :=
          fun hsync =>
            stepFR_app_arrow_extract_shared_member
              (ctx := ctxᵢ)
              (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              hmap hsync
        have _sync_extract_of_clean :
            ∀ hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                (∃ σcap fuelBody firstShared result3Shared,
                    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                    x₀ = x₁ ∧
                    body₀ = body₁ ∧
                    agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory σcap env₀ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory θ₀1 σcap env₀ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory σcap env₁ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory θ₁1 σcap env₁ ∧
                    applyFnTClosure (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
                      etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok firstShared ∧
                  fuel' = Nat.succ fuelBody ∧
                  typecheckExpr
                    { ctxᵢ with
                      pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                      memEnv := result1.memEnv'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                      tagEnv := result1.tagEnv'
                      nextTag := result1.nextTag'
                      nextLoc := result1.nextLoc'
                      regime := result1.regime' } body₀ fuelBody = .ok result3Shared ∧
                  isSubtype st2 result3Shared.qualType = true ∧
                  firstShared =
                    { result3Shared with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) } })
              ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          rcases _hsync1_of_clean hclean1_e1 with hsync | hdirty
          · left
            rcases hsync with
              ⟨σcap, hmem, hx, hbody, hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁⟩
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₀ body₀ σcap hmap hmem with
              ⟨fuelBody, firstShared, result3Shared, happly', hfuel', htc', hsub', hfirst'⟩
            exact ⟨σcap, fuelBody, firstShared, result3Shared, hmem, hx, hbody, hcap,
              hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
              happly', hfuel', htc', hsub', hfirst'⟩
          · right
            exact hdirty
        -- htc_body₀ : typecheckExpr bodyCtx body₀ fuelBody₀ = .ok result3₀
        -- hfuel₀ : fuel' = Nat.succ fuelBody₀
        -- Phase E-G: Body IH application and final assembly.
        -- Option 2 (in progress): choose output realization maps before assembling
        -- the existential package, then discharge remaining fields under that choice.
        have hOutMapChoice :
            ∃ (θ₀_out θ₁_out : RealizationMap),
              wfExtendsMap θ₀ θ₀_out ∧
              wfExtendsMap θ₁ θ₁_out ∧
              (valueHasETyp θ₀_out o₀ res.qualType.etyp ∧
               valueHasETyp θ₁_out o₁ res.qualType.etyp ∧
               runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_out ∧
               runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_out ∧
               consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₀.memory cf₀.varEnv θ₀_out ∧
               consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₁.memory cf₁.varEnv θ₁_out ∧
               agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₀.memory cf₀.varEnv θ₀_out cf₁.memory cf₁.varEnv θ₁_out ∧
               valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                 res.qualType cf₀.memory θ₀_out o₀ ∧
               valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                 res.qualType cf₁.memory θ₁_out o₁ ∧
               resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                 cf₀.memory cf₁.memory θ₀_out θ₁_out res.qualType o₀ o₁) := by
          have hOutMapChoice_p1p_true
              (h_p1p : joinPoison p1 p = true) :
              ∃ (θ₀_out θ₁_out : RealizationMap),
                wfExtendsMap θ₀ θ₀_out ∧
                wfExtendsMap θ₁ θ₁_out ∧
                (valueHasETyp θ₀_out o₀ res.qualType.etyp ∧
                 valueHasETyp θ₁_out o₁ res.qualType.etyp ∧
                 runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_out ∧
                 runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_out ∧
                 consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                   cf₀.memory cf₀.varEnv θ₀_out ∧
                 consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                   cf₁.memory cf₁.varEnv θ₁_out ∧
                 agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                   cf₀.memory cf₀.varEnv θ₀_out cf₁.memory cf₁.varEnv θ₁_out ∧
                 valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                   res.qualType cf₀.memory θ₀_out o₀ ∧
                 valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                   res.qualType cf₁.memory θ₁_out o₁ ∧
                 resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                   cf₀.memory cf₁.memory θ₀_out θ₁_out res.qualType o₀ o₁) := by
            rcases list_mapM_ok_mem_output_exists_input
                (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
                (xs := tcls) (ys := results) (y := first) hmap (by simp [heq_results])
              with ⟨tcl, _htcl_mem, happly_first⟩
            have hfirst_pack :
                first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
              applyFnTClosure_ok_poison_pred_of_p1p_true
                (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                (result2 := result1) (fuel := fuel') (tcl := tcl) (r := first)
                h_p1p happly_first
            have hres_pack :
                res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred :=
              joinTypeResults_poison_pred_of_head_true_noPred
                (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join hfirst_pack.1 hfirst_pack.2
            -- ===== Per-run body IH for ¬ qtypCleanUnder (p1=true) =====
            -- Extract σcap from closureCapturedVarsRegime for each run.
            -- This avoids the σcap matching problem between valueHasETyp.closure
            -- and closureCapturedVarsRegime.
            have ⟨σcapA₀, hσcapA₀_mem, hσcapA₀_regime, hσcapA₀_typing, hσcapA₀_rec⟩ :=
              closureCapturedVarsRegime_closure_extract hetyp1
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
            have ⟨σcapA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
              closureCapturedVarsRegime_closure_extract hetyp1
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
            -- Get body typing for σcapA₀ and σcapA₁ from applyFnTClosure
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₀ body₀ σcapA₀ hmap hσcapA₀_mem with
              ⟨fuelBodyA₀, firstA₀, result3A₀, happlyA₀, hfuelA₀,
                htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₁ body₁ σcapA₁ hmap hσcapA₁_mem with
              ⟨fuelBodyA₁, firstA₁, result3A₁, happlyA₁, hfuelA₁,
                htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
            -- Get membership in first :: rest (for join transport)
            have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
              rcases list_mapM_ok_mem_input_exists_output
                  (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  hmap hσcapA₀_mem with ⟨y, hy_mem, hy_eq⟩
              rw [← heq_results]
              have : y = firstA₀ := Except.ok.inj (hy_eq.symm.trans happlyA₀)
              rwa [this] at hy_mem
            have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
              rcases list_mapM_ok_mem_input_exists_output
                  (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  hmap hσcapA₁_mem with ⟨y, hy_mem, hy_eq⟩
              rw [← heq_results]
              have : y = firstA₁ := Except.ok.inj (hy_eq.symm.trans happlyA₁)
              rwa [this] at hy_mem
            -- Define body contexts
            let bodyCtxA₀ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            let bodyCtxA₁ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            -- Common setup
            have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
            have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
            have h_mono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
              regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            -- Fuel bounds
            have hfuel_ltA₀ : fuelBodyA₀ < Nat.succ (Nat.succ fuel') := by
              have : fuelBodyA₀ < fuel' := by rw [hfuelA₀]; exact Nat.lt_succ_self _
              exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            have hfuel_ltA₁ : fuelBodyA₁ < Nat.succ (Nat.succ fuel') := by
              have : fuelBodyA₁ < fuel' := by rw [hfuelA₁]; exact Nat.lt_succ_self _
              exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            -- ===== Run 0: unary body witness =====
            have hTmBodyA₀ : wfTagMeaningCtx tm bodyCtxA₀ := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (hqt2 ▸ hresTm2) rfl rfl
              simpa [bodyCtxA₀, ctxAfter] using
                wfTagMeaningCtx_closure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x₀) (body := body₀) (σcap := σcapA₀)
                  (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hTm1 hresTm1' hetyp1 hσcapA₀_mem hargTm
            have htcBodyA₀' : typecheck bodyCtxA₀ body₀ fuelBodyA₀ = .ok result3A₀ := by
              simpa [bodyCtxA₀, typecheck] using htc_bodyA₀
            have hwfBodyCtxA₀ : wfTypeContext bodyCtxA₀ := by
              simp only [bodyCtxA₀, wfTypeContext]
              have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
              have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
              exact ⟨hwf1.1,
                varEnvRefLocsBounded_update
                  (varEnvRefLocsBounded_ofCaptured
                    (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)))
                  (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
                varEnvClosuresCapturedRefLocsBounded_update
                  (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem))
                  (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
            have hric_bodyA₀ :
                runtimeInstantiatesCtx bodyCtxA₀ c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
              let ctxCapBaseA₀ : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₀ }
              have hric_cap_baseA₀ :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₀ result1)
                    c₁₀.memory env₀ θ₀1 := by
                constructor
                · intro l a hlookup
                  exact hric₀1.1 l a hlookup
                · intro y qt hlookup
                  have hlookup_list :=
                    list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                  rcases hσcapA₀_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hlookup_list hv⟩
              have hric_bodyA₀' :
                  runtimeInstantiatesCtx
                    { ctxCapBaseA₀ with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBaseA₀) (result2 := result1) (x := x₀)
                  (tenv := σcapA₀)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₀) (μ := c₁₀.memory) (ρ := env₀) (θ := θ₀1)
                  hric_cap_baseA₀ harg₀_typed
                  (fun y qt hlookup => by
                    have hl := list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                    rcases hσcapA₀_typing.2.1 y qt hl with ⟨v, hv⟩
                    exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hl hv⟩)
              simpa [runtimeInstantiatesCtx, bodyCtxA₀, ctxCapBaseA₀, ctxAfter]
                using hric_bodyA₀'
            have htagR_bodyA₀ : regimeConsistentWithCtx bodyCtxA₀ := by
              simpa [bodyCtxA₀, ctxAfter, regimeConsistentWithCtx] using htagR1
            have hcwr_bodyA₀ :
                consistentWithRegime predSat bodyCtxA₀.regime bodyCtxA₀
                  c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have hlocs_src₀ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' c₁₀.memory θ₀1 (l, qt) :=
                fun l qt k hlookup hguard hRdef =>
                  hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_capA₀ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₀.memory env₀ (x, qt) :=
                fun x qt k hlookup hguard hRdef =>
                  hσcapA₀_regime x qt k
                    (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hguard hRdef
              have hvars_argA₀ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                  valueConsistentWithRegime_transport_pred
                    (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                    (qt := result2.qualType)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                    (by simp [hqt2]) (hetyp := by simp [hqt2])
                    (by simpa [ctxAfter] using _hvalc₂₀)
                have hvalc_arg_e1 :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                exact
                  varsRegime_transport_predHolds
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                      c₂'₀.memory c₁₀.memory)
                    (varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₀) (k := k)
                      (by simp [VarEnv.update, VarEnv.lookup])
                      hguard hRdef hvalc_arg_e1)
              have h_cap_cvcrA₀ :
                  ∀ x qt v,
                    (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                    env₀.lookup x = some v →
                    closureCapturedVarsRegime predSat result1.regime' qt
                      c₁₀.memory θ₀1 v :=
                fun x qt v hlookup hv =>
                  hσcapA₀_rec x qt v
                    (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hv
              exact
                consistentWithRegime_closure_body_start
                  predSat ctxᵢ result1
                  σcapA₀ x₀ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  c₁₀.memory θ₀1 env₀ v₂₀
                  hlocs_src₀ hvars_capA₀ hvars_argA₀ h_cap_cvcrA₀
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                      c₂'₀.memory c₁₀.memory)
                    hθext₀1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime
                          _hvalc₂₀))))
            have hwfcfg_body_initA₀ :
                wfConfig
                  { memory := c₁₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := c₁₀.nextAddr
                    pureMode := false } := by
              have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                (wfConfig_preserved e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
              have hnext₂_to₁ : c₂'₀.nextAddr ≤ c₁₀.nextAddr :=
                terminatesTo_nextAddr_mono e1 c₂'₀ c₁₀
                  (Value.closure x₀ body₀ env₀) ht₀_e1
              have hv₂₀_wf : wfValue c₁₀.nextAddr v₂₀ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
              have henv₀_wf : wfVarEnv c₁₀.nextAddr env₀ := by
                cases (wfConfig_preserved e1 _ c₁₀ _ ht₀_e1 hwfcf₂₀).2 with
                | closure _ _ _ henv => exact henv
              constructor
              · intro a ha; exact hwfcf₁₀.1 a ha
              · simpa [VarEnv.update] using wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf
            have hSingle_bodyA₀ :=
              singleIH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀ result3A₀ htcBodyA₀'
            have hpc_bodyA₀_run : bodyCtxA₀.pc = true := by
              simp [bodyCtxA₀, joinPoison] at h_p1p ⊢
              cases p1 <;> cases p <;> simp at h_p1p ⊢
            have hsr₀ :=
              hSingle_bodyA₀ hpredlaws hTmBodyA₀
                c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
                hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀
                hcwr_bodyA₀ c₁₀.nextAddr false hwfcfg_body_initA₀ ht₀_body
                hpc_bodyA₀_run
            rcases hsr₀ with
              ⟨θ₀_body, hθext₀_body, hv₀_body_typed,
                hric_bodyA₀_final, hcwr_bodyA₀_final, hvalc_bodyA₀, _hpres₀, _hfresh₀_body⟩
            -- ===== Run 1: unary body witness =====
            have hTmBodyA₁ : wfTagMeaningCtx tm bodyCtxA₁ := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (hqt2 ▸ hresTm2) rfl rfl
              simpa [bodyCtxA₁, ctxAfter] using
                wfTagMeaningCtx_closure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x₁) (body := body₁) (σcap := σcapA₁)
                  (xArg := x₁) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hTm1 hresTm1' hetyp1 hσcapA₁_mem hargTm
            have htcBodyA₁' : typecheck bodyCtxA₁ body₁ fuelBodyA₁ = .ok result3A₁ := by
              simpa [bodyCtxA₁, typecheck] using htc_bodyA₁
            have hwfBodyCtxA₁ : wfTypeContext bodyCtxA₁ := by
              simp only [bodyCtxA₁, wfTypeContext]
              have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
              have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
              exact ⟨hwf1.1,
                varEnvRefLocsBounded_update
                  (varEnvRefLocsBounded_ofCaptured
                    (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))))
                  (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
                varEnvClosuresCapturedRefLocsBounded_update
                  (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption)))
                  (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
            have hric_bodyA₁ :
                runtimeInstantiatesCtx bodyCtxA₁ c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
              let ctxCapBaseA₁ : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₁ }
              have hric_cap_baseA₁ :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₁ result1)
                    c₁₁.memory env₁ θ₁1 := by
                constructor
                · intro l a hlookup
                  exact hric₁1.1 l a hlookup
                · intro y qt hlookup
                  have hlookup_list :=
                    list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                  rcases hσcapA₁_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hlookup_list hv⟩
              have hric_bodyA₁' :
                  runtimeInstantiatesCtx
                    { ctxCapBaseA₁ with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBaseA₁) (result2 := result1) (x := x₁)
                  (tenv := σcapA₁)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₁) (μ := c₁₁.memory) (ρ := env₁) (θ := θ₁1)
                  hric_cap_baseA₁ harg₁_typed
                  (fun y qt hlookup => by
                    have hl := list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                    rcases hσcapA₁_typing.2.1 y qt hl with ⟨v, hv⟩
                    exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hl hv⟩)
              simpa [runtimeInstantiatesCtx, bodyCtxA₁, ctxCapBaseA₁, ctxAfter]
                using hric_bodyA₁'
            have htagR_bodyA₁ : regimeConsistentWithCtx bodyCtxA₁ := by
              simpa [bodyCtxA₁, ctxAfter, regimeConsistentWithCtx] using htagR1
            have hcwr_bodyA₁ :
                consistentWithRegime predSat bodyCtxA₁.regime bodyCtxA₁
                  c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hlocs_src₁ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' c₁₁.memory θ₁1 (l, qt) :=
                fun l qt k hlookup hguard hRdef =>
                  hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_capA₁ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₁.memory env₁ (x, qt) :=
                fun x qt k hlookup hguard hRdef =>
                  hσcapA₁_regime x qt k
                    (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hguard hRdef
              have hvars_argA₁ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₁.memory
                      (env₁.update x₁ v₂₁) (x₁, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                  valueConsistentWithRegime_transport_pred
                    (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                    (qt := result2.qualType)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                    (by simp [hqt2]) (hetyp := by simp [hqt2])
                    (by simpa [ctxAfter] using _hvalc₂₁)
                have hvalc_arg_e1 :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                exact
                  varsRegime_transport_predHolds
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                      c₂'₁.memory c₁₁.memory)
                    (varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (ρ := env₁.update x₁ v₂₁)
                      (x := x₁) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₁) (k := k)
                      (by simp [VarEnv.update, VarEnv.lookup])
                      hguard hRdef hvalc_arg_e1)
              have h_cap_cvcrA₁ :
                  ∀ x qt v,
                    (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                    env₁.lookup x = some v →
                    closureCapturedVarsRegime predSat result1.regime' qt
                      c₁₁.memory θ₁1 v :=
                fun x qt v hlookup hv =>
                  hσcapA₁_rec x qt v
                    (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hv
              exact
                consistentWithRegime_closure_body_start
                  predSat ctxᵢ result1
                  σcapA₁ x₁ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  c₁₁.memory θ₁1 env₁ v₂₁
                  hlocs_src₁ hvars_capA₁ hvars_argA₁ h_cap_cvcrA₁
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                      c₂'₁.memory c₁₁.memory)
                    hθext₁1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime
                          _hvalc₂₁))))
            have hwfcfg_body_initA₁ :
                wfConfig
                  { memory := c₁₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := c₁₁.nextAddr
                    pureMode := false } := by
              have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                (wfConfig_preserved e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
              have hnext₂_to₁ : c₂'₁.nextAddr ≤ c₁₁.nextAddr :=
                terminatesTo_nextAddr_mono e1 c₂'₁ c₁₁
                  (Value.closure x₁ body₁ env₁) ht₁_e1
              have hv₂₁_wf : wfValue c₁₁.nextAddr v₂₁ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
              have henv₁_wf : wfVarEnv c₁₁.nextAddr env₁ := by
                cases (wfConfig_preserved e1 _ c₁₁ _ ht₁_e1 hwfcf₂₁).2 with
                | closure _ _ _ henv => exact henv
              constructor
              · intro a ha; exact hwfcf₁₁.1 a ha
              · simpa [VarEnv.update] using wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf
            have hSingle_bodyA₁ :=
              singleIH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁ result3A₁ htcBodyA₁'
            have hpc_bodyA₁_run : bodyCtxA₁.pc = true := by
              simp [bodyCtxA₁, joinPoison] at h_p1p ⊢
              cases p1 <;> cases p <;> simp at h_p1p ⊢
            have hsr₁ :=
              hSingle_bodyA₁ hpredlaws hTmBodyA₁
                c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 evalCfg₁ o₁
                hθ₁1wf hwfBodyCtxA₁ hric_bodyA₁ htagR_bodyA₁
                hcwr_bodyA₁ c₁₁.nextAddr false hwfcfg_body_initA₁ ht₁_body
                hpc_bodyA₁_run
            rcases hsr₁ with
              ⟨θ₁_body, hθext₁_body, hv₁_body_typed,
                hric_bodyA₁_final, hcwr_bodyA₁_final, hvalc_bodyA₁, _hpres₁, _hfresh₁_body⟩
            -- ===== Transport to joined result and pack =====
            -- etyp agreement: body result etyp = firstA etyp (normalizeAppResultByProvenance preserves etyp)
            have hfirstA₀_etyp : firstA₀.qualType.etyp = result3A₀.qualType.etyp := by
              rw [hfirstA₀_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
            have hfirstA₁_etyp : firstA₁.qualType.etyp = result3A₁.qualType.etyp := by
              rw [hfirstA₁_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
            -- regime monotonicity from result1 to body results
            have h_mono_bodyA₀ : Regime.monotoneStep bodyCtxA₀.regime result3A₀.regime' :=
              regime_monotone bodyCtxA₀ body₀ fuelBodyA₀ result3A₀ htcBodyA₀'
            have h_mono_bodyA₁ : Regime.monotoneStep bodyCtxA₁.regime result3A₁.regime' :=
              regime_monotone bodyCtxA₁ body₁ fuelBodyA₁ result3A₁ htcBodyA₁'
            have hres1_to_firstA₀_mono :
                Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                  (ctxAfter ctxᵢ firstA₀).regime := by
              simpa [bodyCtxA₀, ctxAfter, hfirstA₀_eq] using h_mono_bodyA₀
            have hres1_to_firstA₁_mono :
                Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                  (ctxAfter ctxᵢ firstA₁).regime := by
              simpa [bodyCtxA₁, ctxAfter, hfirstA₁_eq] using h_mono_bodyA₁
            -- lookup-back for regime: firstA₀.regime' → result1.regime'
            have hlookup_back_res1_to_A₀ :
                ∀ k b,
                  (ctxAfter ctxᵢ firstA₀).regime.lookup? k = some b →
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
              intro k b hk_src
              have hRdef_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k ≠ none := by
                intro hnone; rw [hk_src] at hnone; contradiction
              have hRdef_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                hres1_to_firstA₀_mono.2 k hRdef_src
              cases hk_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
              | none => exact False.elim (hRdef_res1 hk_res1)
              | some b1 =>
                  rcases hres1_to_firstA₀_mono.1 k b1 hk_res1 with hk_src' | hnone_src
                  · have : some b1 = some b := hk_src'.symm.trans hk_src
                    simp [Option.some.inj this]
                  · rw [hnone_src] at hk_src; cases hk_src
            have hlookup_back_res1_to_A₁ :
                ∀ k b,
                  (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
              intro k b hk_src
              have hRdef_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k ≠ none := by
                intro hnone; rw [hk_src] at hnone; contradiction
              have hRdef_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                hres1_to_firstA₁_mono.2 k hRdef_src
              cases hk_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
              | none => exact False.elim (hRdef_res1 hk_res1)
              | some b1 =>
                  rcases hres1_to_firstA₁_mono.1 k b1 hk_res1 with hk_src' | hnone_src
                  · have : some b1 = some b := hk_src'.symm.trans hk_src
                    simp [Option.some.inj this]
                  · rw [hnone_src] at hk_src; cases hk_src
            -- Memory/varEnv equalities
            have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by simp [heq_cfg₀]
            have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by simp [heq_cfg₁]
            have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by simp [heq_cfg₀]
            have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by simp [heq_cfg₁]
            -- predSat compat for memory transport
            have hpred_compat₀ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' c₁₀.memory v' ↔
                    qtypPredHolds predSat qt' cf₀.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₀1) (μ := c₁₀.memory) (μ' := cf₀.memory)
            have hpred_compat₁ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' c₁₁.memory v' ↔
                    qtypPredHolds predSat qt' cf₁.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₁1) (μ := c₁₁.memory) (μ' := cf₁.memory)
            exact ⟨θ₀_body, θ₁_body,
              wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 hθext₀_body),
              wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 hθext₁_body),
              -- valueHasETyp run 0
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                (θ := θ₀_body) (v := o₀)
                h_join hfirstA₀_mem' (hfirstA₀_etyp ▸ hv₀_body_typed),
              -- valueHasETyp run 1
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                (θ := θ₁_body) (v := o₁)
                h_join hfirstA₁_mem' (hfirstA₁_etyp ▸ hv₁_body_typed),
              -- runtimeInstantiatesCtx run 0
              by
                have hmem_to_res₀ :
                    ∀ l, firstA₀.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest)
                    (res := res) h_join hfirstA₀_mem'
                constructor
                · intro l a hθ
                  have hloc := hric_bodyA₀_final.1 l a hθ
                  rcases hloc with ⟨hcontains_body, hmem_contains⟩
                  have hcontains_src : firstA₀.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstA₀_eq] using hcontains_body
                  exact ⟨hmem_to_res₀ l hcontains_src, by simpa [hmem₀_eq] using hmem_contains⟩
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  exact ⟨v, by simpa [hvar₀_eq] using hlookup_v,
                    valueHasETyp_extends hθext₀_body.1 hv_typ⟩,
              -- runtimeInstantiatesCtx run 1
              by
                have hmem_to_res₁ :
                    ∀ l, firstA₁.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest)
                    (res := res) h_join hfirstA₁_mem'
                constructor
                · intro l a hθ
                  have hloc := hric_bodyA₁_final.1 l a hθ
                  rcases hloc with ⟨hcontains_body, hmem_contains⟩
                  have hcontains_src : firstA₁.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstA₁_eq] using hcontains_body
                  exact ⟨hmem_to_res₁ l hcontains_src, by simpa [hmem₁_eq] using hmem_contains⟩
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  exact ⟨v, by simpa [hvar₁_eq] using hlookup_v,
                    valueHasETyp_extends hθext₁_body.1 hv_typ⟩,
              -- consistentWithRegime run 0
              by
                have hcwr_src₀ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                      (ctxAfter ctxᵢ firstA₀) cf₀.memory cf₀.varEnv θ₀_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtxA₀ result3A₀).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstA₀_eq] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstA₀_eq] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtxA₀ result3A₀).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstA₀_eq] using hRdef
                    simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using
                      hcwr_bodyA₀_final.1 l qt k hlookup_body hguard_body hRdef_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k with
                    | none => exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_A₀ k b hk_src
                          rw [hk_back] at hnone; contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                              some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :=
                          hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :=
                          varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                        simpa [hvar₀_eq] using
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstA₀).regime)
                            (μ := cf₀.memory) (ρ := c₁₀.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_A₀ hguard hk_src hvar_res1_mem
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ hθext₀_body.1
                      (closureCapturedVarsRegime_transport_lookup_back
                        hlookup_back_res1_to_A₀ hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                    h_join hfirstA₀_mem' hcwr_src₀,
              -- consistentWithRegime run 1
              by
                have hcwr_src₁ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                      (ctxAfter ctxᵢ firstA₁) cf₁.memory cf₁.varEnv θ₁_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtxA₁ result3A₁).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstA₁_eq] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstA₁_eq] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtxA₁ result3A₁).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstA₁_eq] using hRdef
                    simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using
                      hcwr_bodyA₁_final.1 l qt k hlookup_body hguard_body hRdef_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k with
                    | none => exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_A₁ k b hk_src
                          rw [hk_back] at hnone; contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                              some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :=
                          hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :=
                          varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                        simpa [hvar₁_eq] using
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstA₁).regime)
                            (μ := cf₁.memory) (ρ := c₁₁.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_A₁ hguard hk_src hvar_res1_mem
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ hθext₁_body.1
                      (closureCapturedVarsRegime_transport_lookup_back
                        hlookup_back_res1_to_A₁ hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                    h_join hfirstA₁_mem' hcwr_src₁,
              -- agreeOnClean for ¬qtypCleanUnder (p1=true, different closure bodies)
              by
                -- Regime monotonicity: result1.regime' → res.regime' (through the join)
                have h_all_members_mono :
                    ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                  apply List.mapM_Except_preserves_property
                    (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                      ctxᵢ result1 fuel')
                    (P := fun x => Regime.monotoneStep result1.regime' x.regime')
                  · intro tcl result _htcl
                    exact applyFnTClosure_regime_mono tcl ctxᵢ st1 st2 p p1 etyp2 p2 pred2
                      result1 result fuel'
                      (fun m _hlt e ctx' res' htc =>
                        by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                      _htcl
                  · rw [← heq_results]; exact hmap
                have h_mono_res : Regime.monotoneStep result1.regime' res.regime' :=
                  joinTypeResults_regime_monotone ctxᵢ first rest res result1.regime'
                    (h_all_members_mono first (by simp))
                    (fun x hx => h_all_members_mono x (List.mem_cons_of_mem _ hx))
                    h_join
                -- Clean transfer: qtypCleanUnder res → qtypCleanUnder result1
                have h_clean_res_to_pre :
                    ∀ qt, qtypCleanUnder res.regime' qt →
                      qtypCleanUnder result1.regime' qt :=
                  fun qt hc => cleanUnder_of_monotone h_mono_res hc
                constructor
                · -- Locations conjunct
                  intro l qt hlookup hclean
                  have hclean_res : qtypCleanUnder res.regime' qt := by
                    simpa [ctxAfter] using hclean
                  have hlookup_res : res.memEnv'.lookup l = some qt := by
                    simpa [ctxAfter] using hlookup
                  -- Case split: is l inherited from result1.memEnv'?
                  cases hlookup_body : (result1.memEnv'.lookup l) with
                  | none =>
                    -- Fresh location: l is NOT in result1.memEnv' (= bodyCtxAᵢ.memEnv)
                    -- Derive ¬ bodyCtxAᵢ.memEnv.contains l from hlookup_body
                    have hnotContains_body : ¬ result1.memEnv'.contains l := by
                      intro habs
                      rcases memEnv_lookup_some_of_contains result1.memEnv' l habs with
                        ⟨_qt', hlookup'⟩
                      rw [hlookup_body] at hlookup'; exact Option.noConfusion hlookup'
                    -- Run 0: prove θ₀_body.lookup l = none
                    have hθ₀_none : θ₀_body.lookup l = none := by
                      by_cases hc₀ : result3A₀.memEnv'.contains l
                      · -- l is fresh in result3A₀ (not in bodyCtxA₀, but in result3A₀)
                        -- Need: result3A₀.memEnv'.lookup l = some qt₀ and clean
                        rcases memEnv_lookup_some_of_contains result3A₀.memEnv' l hc₀ with
                          ⟨qt₀, hlookup₀⟩
                        -- firstA₀.memEnv' = result3A₀.memEnv' (from hfirstA₀_eq)
                        have hlookup₀_first : firstA₀.memEnv'.lookup l = some qt₀ := by
                          simpa [hfirstA₀_eq] using hlookup₀
                        have hlookup₀_ctx :
                            (ctxAfter ctxᵢ firstA₀).memEnv.lookup l = some qt₀ := by
                          simpa [ctxAfter] using hlookup₀_first
                        have hclean₀ :
                            qtypCleanUnder (ctxAfter ctxᵢ firstA₀).regime qt₀ := by
                          exact
                            joinTypeResults_lookup_member_clean_compat
                              (ctx := ctxᵢ) (first := first) (src := firstA₀)
                              (rest := rest) (res := res)
                              h_join hfirstA₀_mem' l qt qt₀ hlookup hclean hlookup₀_ctx
                        -- Transport cleanness from firstA₀ regime to result3A₀ regime
                        have hclean₀_body : qtypCleanUnder result3A₀.regime' qt₀ := by
                          simpa [ctxAfter, hfirstA₀_eq] using hclean₀
                        exact _hfresh₀_body l qt₀
                          (by simpa [bodyCtxA₀] using hnotContains_body) hlookup₀ hclean₀_body
                      · -- l is not in result3A₀.memEnv' either → not in ctxAfter
                        exact theta_not_contains_if_not_in_memEnv
                          (ctxAfter bodyCtxA₀ result3A₀) evalCfg₀.memory
                          evalCfg₀.varEnv θ₀_body l
                          hric_bodyA₀_final
                          (by simp [ctxAfter]; exact hc₀)
                    -- Run 1: prove θ₁_body.lookup l = none
                    have hθ₁_none : θ₁_body.lookup l = none := by
                      by_cases hc₁ : result3A₁.memEnv'.contains l
                      · rcases memEnv_lookup_some_of_contains result3A₁.memEnv' l hc₁ with
                          ⟨qt₁, hlookup₁⟩
                        have hlookup₁_first : firstA₁.memEnv'.lookup l = some qt₁ := by
                          simpa [hfirstA₁_eq] using hlookup₁
                        have hlookup₁_ctx :
                            (ctxAfter ctxᵢ firstA₁).memEnv.lookup l = some qt₁ := by
                          simpa [ctxAfter] using hlookup₁_first
                        have hclean₁ :
                            qtypCleanUnder (ctxAfter ctxᵢ firstA₁).regime qt₁ := by
                          exact
                            joinTypeResults_lookup_member_clean_compat
                              (ctx := ctxᵢ) (first := first) (src := firstA₁)
                              (rest := rest) (res := res)
                              h_join hfirstA₁_mem' l qt qt₁ hlookup hclean hlookup₁_ctx
                        have hclean₁_body : qtypCleanUnder result3A₁.regime' qt₁ := by
                          simpa [ctxAfter, hfirstA₁_eq] using hclean₁
                        exact _hfresh₁_body l qt₁
                          (by simpa [bodyCtxA₁] using hnotContains_body) hlookup₁ hclean₁_body
                      · exact theta_not_contains_if_not_in_memEnv
                          (ctxAfter bodyCtxA₁ result3A₁) evalCfg₁.memory
                          evalCfg₁.varEnv θ₁_body l
                          hric_bodyA₁_final
                          (by simp [ctxAfter]; exact hc₁)
                    exact agreeLocUnder.both_unrealized l qt hθ₀_none hθ₁_none
                  | some qt' =>
                    -- Inherited location: l is in result1.memEnv' with type qt'
                    have hetyp_qt : qt.etyp = ETyp.int :=
                      memEnv_lookup_etyp_int res.memEnv' l qt hlookup_res
                    have hetyp_qt' : qt'.etyp = ETyp.int :=
                      memEnv_lookup_etyp_int result1.memEnv' l qt' hlookup_body
                    have hcontains_body : result1.memEnv'.contains l := by
                      exact
                        memEnv_contains_of_lookup_some
                          (env := result1.memEnv') (l := l) (qt := qt') hlookup_body
                    have hcontains_A₀ : firstA₀.memEnv'.contains l := by
                      have hcontains_result3A₀ : result3A₀.memEnv'.contains l := by
                        exact
                          typecheckExpr_mem_contains_preserved
                            (ctx := bodyCtxA₀) (e := body₀) (fuel := fuelBodyA₀) (res := result3A₀)
                            htc_bodyA₀ l (by simpa [bodyCtxA₀] using hcontains_body)
                      simpa [hfirstA₀_eq] using hcontains_result3A₀
                    have hcontains_A₁ : firstA₁.memEnv'.contains l := by
                      have hcontains_result3A₁ : result3A₁.memEnv'.contains l := by
                        exact
                          typecheckExpr_mem_contains_preserved
                            (ctx := bodyCtxA₁) (e := body₁) (fuel := fuelBodyA₁) (res := result3A₁)
                            htc_bodyA₁ l (by simpa [bodyCtxA₁] using hcontains_body)
                      simpa [hfirstA₁_eq] using hcontains_result3A₁
                    rcases memEnv_lookup_some_of_contains firstA₀.memEnv' l hcontains_A₀ with
                      ⟨qt_A₀, hlookup_A₀⟩
                    rcases memEnv_lookup_some_of_contains firstA₁.memEnv' l hcontains_A₁ with
                      ⟨qt_A₁, hlookup_A₁⟩
                    have hlookup_A₀_ctx :
                        (ctxAfter ctxᵢ firstA₀).memEnv.lookup l = some qt_A₀ := by
                      simpa [ctxAfter] using hlookup_A₀
                    have hlookup_A₁_ctx :
                        (ctxAfter ctxᵢ firstA₁).memEnv.lookup l = some qt_A₁ := by
                      simpa [ctxAfter] using hlookup_A₁
                    have hclean_A₀ :
                        qtypCleanUnder (ctxAfter ctxᵢ firstA₀).regime qt_A₀ := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                          h_join hfirstA₀_mem' l qt qt_A₀ hlookup hclean hlookup_A₀_ctx
                    have hclean_A₁ :
                        qtypCleanUnder (ctxAfter ctxᵢ firstA₁).regime qt_A₁ := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                          h_join hfirstA₁_mem' l qt qt_A₁ hlookup hclean hlookup_A₁_ctx
                    have hlookup_result3A₀ : result3A₀.memEnv'.lookup l = some qt_A₀ := by
                      simpa [hfirstA₀_eq] using hlookup_A₀
                    have hclean_result3A₀ : qtypCleanUnder result3A₀.regime' qt_A₀ := by
                      simpa [ctxAfter, hfirstA₀_eq] using hclean_A₀
                    -- Establish qt' cleanness under result1.regime'
                    -- (bodies may change the type at l; qt' ≠ qt is possible)
                    have hclean_pre' : qtypCleanUnder result1.regime' qt' := by
                      have hpc_bodyA₀ : bodyCtxA₀.pc = true := by
                        simp [bodyCtxA₀, joinPoison] at h_p1p ⊢
                        cases p1 <;> cases p <;> simp at h_p1p ⊢
                      exact
                        typecheckExpr_lookup_clean_back_of_pc_true
                          (ctx := bodyCtxA₀) (e := body₀) (fuel := fuelBodyA₀) (res := result3A₀)
                          htc_bodyA₀ hwfBodyCtxA₀ hpc_bodyA₀ l qt' qt_A₀
                          (by simpa [bodyCtxA₀] using hlookup_body)
                          hlookup_result3A₀ hclean_result3A₀
                    -- Use qt' cleanness to prove agreeLocUnder
                    have hlookup_pre :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).memEnv.lookup l =
                          some qt' := by
                      simpa [ctxAfter] using hlookup_body
                    have hloc_pre := hagree1.1 l qt' hlookup_pre hclean_pre'
                    -- Per-run preservation
                    rcases _hpres₀ with ⟨hpres₀_fn⟩
                    have hpres_l₀ := hpres₀_fn l qt' qt_A₀
                      (by simp only [bodyCtxA₀]; exact hlookup_body)
                      hlookup_result3A₀ hclean_result3A₀
                    have hlookup_result3A₁ : result3A₁.memEnv'.lookup l = some qt_A₁ := by
                      simpa [hfirstA₁_eq] using hlookup_A₁
                    have hclean_result3A₁ : qtypCleanUnder result3A₁.regime' qt_A₁ := by
                      simpa [ctxAfter, hfirstA₁_eq] using hclean_A₁
                    rcases _hpres₁ with ⟨hpres₁_fn⟩
                    have hpres_l₁ := hpres₁_fn l qt' qt_A₁
                      (by simp only [bodyCtxA₁]; exact hlookup_body)
                      hlookup_result3A₁ hclean_result3A₁
                    -- Case split on pre-body loc agreement × run preservation
                    cases hloc_pre with
                    | both_unrealized _ _ hθ₀_none hθ₁_none =>
                      cases hpres_l₀ with
                      | both_unrealized _ hout₀ =>
                        cases hpres_l₁ with
                        | both_unrealized _ hout₁ =>
                          exact agreeLocUnder.both_unrealized l qt hout₀ hout₁
                        | preserve_value a n hin _ _ _ =>
                          exact absurd (hθ₁_none ▸ hin) (by exact Option.noConfusion)
                      | preserve_value a n hin _ _ _ =>
                        exact absurd (hθ₀_none ▸ hin) (by exact Option.noConfusion)
                    | agree_values _ _ a₀ a₁ n₀ n₁ hθ₀_in hθ₁_in hm₀_in hm₁_in
                        hagree_val =>
                      cases hpres_l₀ with
                      | both_unrealized hin₀ _ =>
                        exact absurd (hin₀ ▸ hθ₀_in) (by exact Option.noConfusion)
                      | preserve_value a₀' n₀' hθ₀_in' hm₀_in' hθ₀_out hm₀_out =>
                        cases hpres_l₁ with
                        | both_unrealized hin₁ _ =>
                          exact absurd (hin₁ ▸ hθ₁_in) (by exact Option.noConfusion)
                        | preserve_value a₁' n₁' hθ₁_in' hm₁_in' hθ₁_out hm₁_out =>
                          -- Equate addresses via unique θ lookups
                          have ha₀ : a₀' = a₀ :=
                            Option.some.inj (hθ₀_in'.symm.trans hθ₀_in)
                          have ha₁ : a₁' = a₁ :=
                            Option.some.inj (hθ₁_in'.symm.trans hθ₁_in)
                          -- Equate values via unique memory lookups
                          have hn₀ : n₀' = n₀ := by
                            rw [ha₀] at hm₀_in'
                            exact Option.some.inj (hm₀_in'.symm.trans hm₀_in)
                          have hn₁ : n₁' = n₁ := by
                            rw [ha₁] at hm₁_in'
                            exact Option.some.inj (hm₁_in'.symm.trans hm₁_in)
                          -- Pre-body value equality (clean ints must agree)
                          have heq_pre : n₀ = n₁ := by
                            cases hagree_val with
                            | clean_eq_nonref_nonarrow _ _ _ hEq =>
                              exact Value.num.inj hEq
                            | withPred_true_eq _ _ _ _ _ hEq =>
                              exact Value.num.inj hEq
                            | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | dirty_internal_arrow _ hisA htyp₀ _ =>
                              simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                            | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | dirty_internal_parrow _ hisP htyp₀ _ =>
                              simp [valueHasETyp_num_etyp htyp₀, ETyp.isParrow] at hisP
                            | clean_ref _ _ _ _ hv₀ _ _ => cases hv₀
                            | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ => cases hv₀
                          have heq_post : n₀' = n₁' := by
                            rw [hn₀, hn₁, heq_pre]
                          -- Construct post-body agreeLocUnder
                          refine agreeLocUnder.agree_values l qt a₀' a₁'
                            n₀' n₁' hθ₀_out hθ₁_out
                            (by rw [hmem₀_eq]; exact hm₀_out)
                            (by rw [hmem₁_eq]; exact hm₁_out) ?_
                          rw [heq_post]
                          cases hclean_res with
                          | clean hpoison =>
                            exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison
                              (by simp [hetyp_qt, ETyp.isFunctionType, ETyp.isArrow,
                                        ETyp.isParrow])
                              (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                          | guard k htag hregime hnotfun =>
                            exact agreeValueUnder.withPred_true_eq k htag
                              (by simpa [ctxAfter] using hregime) hnotfun
                              (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                · -- Variables conjunct
                  intro x qt hlookup hclean
                  have hlookup_pre :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  have hclean_pre : qtypCleanUnder result1.regime' qt :=
                    h_clean_res_to_pre qt (by simpa [ctxAfter] using hclean)
                  cases hagree1.2 x qt hlookup_pre hclean_pre with
                  | agree_values x qt v₀ v₁ hv₀_pre hv₁_pre hagree_val =>
                    refine agreeVarUnder.agree_values x qt v₀ v₁
                      (by rwa [hvar₀_eq]) (by rwa [hvar₁_eq]) ?_
                    -- Transport agreeValueUnder:
                    -- 1. Extend memory/θ (result1 context → body output context)
                    have hagree_ext :=
                      agreeValueUnder_clean_extends
                        hpred_compat₀ hpred_compat₁ hclean_pre hθext₀_body.1 hθext₁_body.1
                        hagree_val
                    -- 2. Change regime (result1 → res)
                    exact agreeValueUnder_clean_monotoneRegime h_mono_res
                      (by simpa [ctxAfter] using hclean) hagree_ext
                  | both_none x qt hv₀_pre hv₁_pre =>
                    exact agreeVarUnder.both_none x qt
                      (by rwa [hvar₀_eq]) (by rwa [hvar₁_eq]),
              -- valueConsistentWithRegime run 0
              by
                have hfirstA₀_eq_regime : firstA₀.regime' = result3A₀.regime' := by
                  simp [hfirstA₀_eq]
                have hval_src₀ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                      firstA₀.qualType cf₀.memory θ₀_body o₀ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtxA₀ result3A₀).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3A₀.qualType with
                            poison := joinPoison p1 (joinPoison p result3A₀.qualType.poison) })
                        evalCfg₀.memory θ₀_body o₀ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtxA₀ result3A₀).regime)
                      (p := p) (p1 := p1) (qt := result3A₀.qualType)
                      (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) hvalc_bodyA₀
                  simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                    h_join hfirstA₀_mem' hval_src₀,
              -- valueConsistentWithRegime run 1
              by
                have hval_src₁ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                      firstA₁.qualType cf₁.memory θ₁_body o₁ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtxA₁ result3A₁).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3A₁.qualType with
                            poison := joinPoison p1 (joinPoison p result3A₁.qualType.poison) })
                        evalCfg₁.memory θ₁_body o₁ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtxA₁ result3A₁).regime)
                      (p := p) (p1 := p1) (qt := result3A₁.qualType)
                      (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) hvalc_bodyA₁
                  simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                    h_join hfirstA₁_mem' hval_src₁,
              -- resultAgreesIfClean (vacuously true since poison=true ∧ pred=noPred)
              resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
          by_cases hclean1_e1 :
              qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
          · rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
            · rcases hshared with
                ⟨σcap, fuelBody, firstShared, result3Shared,
                  hmem, hx, hbody, hcap,
                  hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                  happly, hfuel, htcBody, hsubBody, hfirstShared⟩
              let bodyCtx : TypeContext :=
                { ctxᵢ with
                  pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                  memEnv := result1.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  tagEnv := result1.tagEnv'
                  nextTag := result1.nextTag'
                  nextLoc := result1.nextLoc'
                  regime := result1.regime' }
              have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
              have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
              have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
                have hfuel_lt' : fuelBody < fuel' := by
                  rw [hfuel]
                  exact Nat.lt_succ_self fuelBody
                exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
                have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                  simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
                have hargTm' :
                    ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                      QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                      qtypGuardDesc? qt' = some (k, d) →
                      tm.lookup k = some d :=
                  QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm)
                    (qt := ⟨etyp2, p2, pred2⟩)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    hresTm2_arg rfl rfl
                exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
              have hTmBody : wfTagMeaningCtx tm bodyCtx := by
                have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
                have hTmBody' :
                    wfTagMeaningCtx tm
                      { (ctxAfter ctxᵢ result2) with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ } :=
                  wfTagMeaningCtx_closure_body
                    (tm := tm)
                    (ctx := (ctxAfter ctxᵢ result2))
                    (result1 := result1)
                    (qtRes := result1.qualType)
                    (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
                    (xFun := x₀) (body := body₀) (σcap := σcap)
                    (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    hTm1 hresTm1' hetyp1 hmem hargTm
                simpa [bodyCtx, ctxAfter] using hTmBody'
              have htcBody' : typecheck bodyCtx body₀ fuelBody = .ok result3Shared := by
                simpa [bodyCtx, typecheck] using htcBody
              have htagBoundedBody : TagBoundedCtx bodyCtx := by
                obtain ⟨hb_tag1, ⟨hb_predV1, hb_predM1⟩, hb_clos1⟩ := _htagBounded1
                have hb_predCtx2 := (_htagBounded2 : TagBoundedCtx (ctxAfter ctxᵢ result2)).2.1
                have hb_closCtx2 := (_htagBounded2 : TagBoundedCtx (ctxAfter ctxᵢ result2)).2.2
                -- Closure captured env bounds from result1's etyp
                have hClosFull := typecheckExpr_preserves_closureCapturedBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1
                  (by simpa [typecheck] using htc1') hb_predCtx2 hb_closCtx2
                rw [hetyp1] at hClosFull
                have hCapBound : CapturedEnvFullBounded σcap result1.nextTag' := hClosFull _ hmem
                have hCapPred := capturedPredTagsBounded_of_fullBounded hCapBound
                -- Arg pred bounded (pred2 from result2, monotone to result1.nextTag')
                have hmono_r2_r1 : result2.nextTag' ≤ result1.nextTag' :=
                  typecheck_normal_nextTag_mono (ctxAfter ctxᵢ result2) e1 fuel' result1
                    (by simpa [typecheck] using htc1')
                have hArgPred : qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ result1.nextTag' := by
                  have := (typecheckExpr_preserves_predTagsBounded ctxᵢ e2 fuel' result2
                    (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2).2
                  rw [hqt2] at this
                  exact qtypPredTagBounded_mono this hmono_r2_r1
                have hArgClos : etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp result1.nextTag' := by
                  have := typecheckExpr_preserves_closureCapturedBounded ctxᵢ e2 fuel' result2
                    (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2
                  rw [hqt2] at this; exact etypClosuresFullBounded_mono this hmono_r2_r1
                refine ⟨by simpa [bodyCtx] using hb_tag1,
                  ⟨predTagsBoundedInVarEnv_update
                    (predTagsBoundedInVarEnv_ofCaptured hCapPred) hArgPred,
                   by simpa [bodyCtx] using hb_predM1⟩,
                  varEnvClosuresCapturedBounded_update
                    (varEnvClosuresCapturedBounded_ofCaptured hCapBound) hArgClos⟩
              have hIH_body :=
                IH fuelBody hfuel_lt body₀ bodyCtx hTmBody htagBoundedBody result3Shared htcBody'
              have hwfBodyCtx : wfTypeContext bodyCtx := by
                simp only [bodyCtx, wfTypeContext]
                have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
                have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
                exact ⟨hwf1.1,
                  varEnvRefLocsBounded_update
                    (varEnvRefLocsBounded_ofCaptured
                      (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))))
                    (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
                  varEnvClosuresCapturedRefLocsBounded_update
                    (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption)))
                    (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
              have hric_body₀ :
                  runtimeInstantiatesCtx bodyCtx c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
                let ctxCapBase : TypeContext :=
                  { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
                have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                  simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
                have hric_cap_base :
                    runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) c₁₀.memory env₀ θ₀1 := by
                  constructor
                  · intro l a hlookup
                    exact hric₀1.1 l a hlookup
                  · intro y qt hlookup
                    exact
                      agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y qt hlookup
                have hric_body₀' :
                    runtimeInstantiatesCtx
                      { ctxCapBase with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                      c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                  runtimeInstantiatesCtx_closure_body
                    (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (argVal := v₂₀) (μ := c₁₀.memory) (ρ := env₀) (θ := θ₀1)
                    hric_cap_base harg₀_typed
                    (agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap))
                simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body₀'
              have hric_body₁ :
                  runtimeInstantiatesCtx bodyCtx c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                let ctxCapBase : TypeContext :=
                  { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
                have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                  simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
                have hric_cap_base :
                    runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) c₁₁.memory env₁ θ₁1 := by
                  constructor
                  · intro l a hlookup
                    exact hric₁1.1 l a hlookup
                  · intro y qt hlookup
                    exact
                      agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y qt hlookup
                have hric_body₁' :
                    runtimeInstantiatesCtx
                      { ctxCapBase with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 :=
                  runtimeInstantiatesCtx_closure_body
                    (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (argVal := v₂₁) (μ := c₁₁.memory) (ρ := env₁) (θ := θ₁1)
                    hric_cap_base harg₁_typed
                    (agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap))
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter, henv_update]
                  using hric_body₁'
              have h_mono1 :
                  Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
                regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
              have htagR_body : regimeConsistentWithCtx bodyCtx := by
                simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
              have hcwr_body₀ :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
                have hlocs_src₀ :
                    ∀ l qt k,
                      result1.memEnv'.lookup l = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      locsRegime predSat result1.regime' c₁₀.memory θ₀1 (l, qt) := by
                  intro l qt k hlookup hguard hRdef
                  exact hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
                have hvars_cap₀ :
                    ∀ x qt k,
                      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₀.memory env₀ (x, qt) := by
                  intro x qt k hlookup hguard hRdef
                  rcases
                      agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap) x qt hlookup
                    with ⟨v, hlookup_v, _htyp_v⟩
                  exact hmemberVars₀ x qt k v hlookup hlookup_v hguard hRdef
                have hvars_arg₀ :
                    ∀ k,
                      qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₀.memory
                        (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  intro k hguard hRdef
                  have hvalc_arg_e2 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ := by
                    have hvalc₂ :
                        valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                          result2.qualType c₂'₀.memory θ₀2 v₂₀ := by
                      simpa [ctxAfter] using _hvalc₂₀
                    exact
                      valueConsistentWithRegime_transport_pred
                        (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                        (qt := result2.qualType)
                        (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                        (by simp [hqt2]) (hetyp := by simp [hqt2])
                        hvalc₂
                  have hvalc_arg_e1 :
                      valueConsistentWithRegime predSat result1.regime'
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                    valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                  have hlookup_v_body :
                      (env₀.update x₀ v₂₀).lookup x₀ = some v₂₀ := by
                    simp [VarEnv.update, VarEnv.lookup]
                  have hvars_arg_e1R_mem₂ :
                      varsRegime predSat result1.regime' c₂'₀.memory
                        (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                    exact
                      varsRegime_of_valueConsistentWithRegime_active
                        (predSat := predSat) (R := result1.regime')
                        (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                        (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (v := v₂₀) (k := k)
                        hlookup_v_body hguard hRdef hvalc_arg_e1
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                    predSat_mem_noPred_compat hpredlaws θ₀1
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value),
                        qtypPredHolds predSat qt c₂'₀.memory v ↔ qtypPredHolds predSat qt c₁₀.memory v := by
                    intro qt v
                    constructor <;> intro h
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).1 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).1 hs)
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).2 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).2 hs)
                  exact
                    varsRegime_transport_predHolds
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (μ' := c₁₀.memory)
                      (ρ := env₀.update x₀ v₂₀)
                      (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                      hqtypPredHolds_mem hvars_arg_e1R_mem₂
                exact
                  consistentWithRegime_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₁₀.memory) (θ := θ₀1) (ρcap := env₀) (vArg := v₂₀)
                    hlocs_src₀ hvars_cap₀ hvars_arg₀
                      hmemberCvcr₀
                    (closureCapturedVarsRegime_transport_μ_θ
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory c₁₀.memory)
                      hθext₀1.1
                      (closureCapturedVarsRegime_monotone h_mono1
                        (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                          (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₀))))
              have hcwr_body₁ :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                have hlocs_src₁ :
                    ∀ l qt k,
                      result1.memEnv'.lookup l = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      locsRegime predSat result1.regime' c₁₁.memory θ₁1 (l, qt) := by
                  intro l qt k hlookup hguard hRdef
                  exact hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
                have hvars_cap₁ :
                    ∀ x qt k,
                      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₁.memory env₁ (x, qt) := by
                  intro x qt k hlookup hguard hRdef
                  rcases
                      agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap) x qt hlookup
                    with ⟨v, hlookup_v, _htyp_v⟩
                  exact hmemberVars₁ x qt k v hlookup hlookup_v hguard hRdef
                have hvars_arg₁ :
                    ∀ k,
                      qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₁.memory
                        (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  intro k hguard hRdef
                  have hvalc_arg_e2 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ := by
                    have hvalc₂ :
                        valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                          result2.qualType c₂'₁.memory θ₁2 v₂₁ := by
                      simpa [ctxAfter] using _hvalc₂₁
                    exact
                      valueConsistentWithRegime_transport_pred
                        (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                        (qt := result2.qualType)
                        (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                        (by simp [hqt2]) (hetyp := by simp [hqt2])
                        hvalc₂
                  have hvalc_arg_e1 :
                      valueConsistentWithRegime predSat result1.regime'
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                    valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                  have hlookup_v_body :
                      (env₁.update x₀ v₂₁).lookup x₀ = some v₂₁ := by
                    simp [VarEnv.update, VarEnv.lookup]
                  have hvars_arg_e1R_mem₂ :
                      varsRegime predSat result1.regime' c₂'₁.memory
                        (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                    exact
                      varsRegime_of_valueConsistentWithRegime_active
                        (predSat := predSat) (R := result1.regime')
                        (μ := c₂'₁.memory) (ρ := env₁.update x₀ v₂₁)
                        (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (v := v₂₁) (k := k)
                        hlookup_v_body hguard hRdef hvalc_arg_e1
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                    predSat_mem_noPred_compat hpredlaws θ₁1
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value),
                        qtypPredHolds predSat qt c₂'₁.memory v ↔ qtypPredHolds predSat qt c₁₁.memory v := by
                    intro qt v
                    constructor <;> intro h
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).1 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).1 hs)
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).2 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).2 hs)
                  exact
                    varsRegime_transport_predHolds
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (μ' := c₁₁.memory)
                      (ρ := env₁.update x₀ v₂₁)
                      (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                      hqtypPredHolds_mem hvars_arg_e1R_mem₂
                have hcwr_body₁' :
                    consistentWithRegime predSat bodyCtx.regime bodyCtx
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                  exact
                    consistentWithRegime_closure_body_start
                      (predSat := predSat)
                      (ctx := ctxᵢ) (result1 := result1)
                      (σcap := σcap) (xArg := x₀)
                      (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₁₁.memory) (θ := θ₁1) (ρcap := env₁) (vArg := v₂₁)
                      hlocs_src₁ hvars_cap₁ hvars_arg₁
                      hmemberCvcr₁
                      (closureCapturedVarsRegime_transport_μ_θ
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory c₁₁.memory)
                        hθext₁1.1
                        (closureCapturedVarsRegime_monotone h_mono1
                          (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                            (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₁))))
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [henv_update] using hcwr_body₁'
              have hagree_body_start :
                  agreeOnClean predSat bodyCtx.regime bodyCtx
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                have hmem_agree :
                    ∀ l qt,
                      result1.memEnv'.lookup l = some qt →
                      qtypCleanUnder result1.regime' qt →
                      agreeLocUnder predSat result1.regime' c₁₀.memory c₁₁.memory θ₀1 θ₁1 (l, qt) := by
                  intro l qt hlookup hclean
                  exact hagree1.1 l qt (by simpa [ctxAfter] using hlookup) hclean
                have hagree_body_start' :
                    agreeOnClean predSat bodyCtx.regime bodyCtx
                      c₁₀.memory (env₀.update x₀ v₂₀) θ₀1
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                  have harg_agree :
                      qtypCleanUnder result1.regime' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                        agreeValueUnder predSat result1.regime'
                          c₁₀.memory c₁₁.memory θ₀1 θ₁1
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                    intro hclean_arg
                    have hclean_arg_e2 :
                        qtypCleanUnder (ctxAfter ctxᵢ result2).regime
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                      cleanUnder_of_monotone h_mono1 hclean_arg
                    have hclean_res2 :
                        qtypCleanUnder (ctxAfter ctxᵢ result2).regime result2.qualType := by
                      cases hclean_arg_e2 with
                      | clean hpoison =>
                          have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                            simpa using hpoison
                          exact qtypCleanUnder.clean (by simpa [hqt2] using (joinPoison_eq_false hjoin).2)
                      | guard k htag hk hnotfun =>
                          have htag' : qtypGuardTag result2.qualType = some k := by
                            simpa [hqt2, qtypGuardTag] using htag
                          have hnotfun' : result2.qualType.etyp.isFunctionType = false := by
                            simpa [hqt2] using hnotfun
                          exact qtypCleanUnder.guard k htag' hk hnotfun'
                    have hagree_res2 :
                        agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2 result2.qualType v₂₀ v₂₁ :=
                      hres_agree2 hclean_res2
                    have hagree_arg_e2 :
                        agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                      refine agreeValueUnder_transport_clean hclean_arg_e2 ?_ ?_ hagree_res2
                      · simp [hqt2]
                      · intro hpoison
                        have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                          simpa using hpoison
                        exact by simpa [hqt2] using (joinPoison_eq_false hjoin).2
                    have hagree_arg_e2_to_e1 :
                        agreeValueUnder predSat result1.regime'
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ :=
                      agreeValueUnder_clean_monotoneRegime h_mono1 hclean_arg hagree_arg_e2
                    have hqtypPredHolds_mem_app_arg₀ :
                        ∀ (qt' : QTyp) (v' : Value),
                          qtypPredHolds predSat qt' c₂'₀.memory v' ↔
                            qtypPredHolds predSat qt' c₁₀.memory v' :=
                      qtypPredHolds_mem_compat_of_predSatLaws
                        (hpredlaws := hpredlaws) (θ := θ₀2) (μ := c₂'₀.memory) (μ' := c₁₀.memory)
                    have hqtypPredHolds_mem_app_arg₁ :
                        ∀ (qt' : QTyp) (v' : Value),
                          qtypPredHolds predSat qt' c₂'₁.memory v' ↔
                            qtypPredHolds predSat qt' c₁₁.memory v' :=
                      qtypPredHolds_mem_compat_of_predSatLaws
                        (hpredlaws := hpredlaws) (θ := θ₁2) (μ := c₂'₁.memory) (μ' := c₁₁.memory)
                    exact
                      agreeValueUnder_clean_extends_transport_mem
                        hqtypPredHolds_mem_app_arg₀ hqtypPredHolds_mem_app_arg₁
                        hclean_arg hθext₀1.1 hθext₁1.1 hagree_arg_e2_to_e1
                  exact
                    agreeOnClean_closure_body_start
                      (predSat := predSat)
                      (ctx := ctxᵢ) (result1 := result1)
                      (σcap := σcap) (xArg := x₀)
                      (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
                      (θ₀ := θ₀1) (θ₁ := θ₁1)
                      (ρcap₀ := env₀) (ρcap₁ := env₁)
                      (vArg₀ := v₂₀) (vArg₁ := v₂₁)
                      hmem_agree hcap harg_agree
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [henv_update] using hagree_body_start'
              have hwfcfg_body_init₀ :
                  wfConfig
                    { memory := c₁₀.memory
                      varEnv := env₀.update x₀ v₂₀
                      nextAddr := c₁₀.nextAddr
                      pureMode := false } := by
                have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                  (wfConfig_preserved e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
                have hnext₂_to₁ : c₂'₀.nextAddr ≤ c₁₀.nextAddr :=
                  terminatesTo_nextAddr_mono e1 c₂'₀ c₁₀ (Value.closure x₀ body₀ env₀) ht₀_e1
                have hv₂₀_wf : wfValue c₁₀.nextAddr v₂₀ :=
                  wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
                have hv₀_closure_wf : wfValue c₁₀.nextAddr (Value.closure x₀ body₀ env₀) :=
                  (wfConfig_preserved e1 _ c₁₀ _ ht₀_e1 hwfcf₂₀).2
                have henv₀_wf : wfVarEnv c₁₀.nextAddr env₀ := by
                  cases hv₀_closure_wf with
                  | closure _ _ _ henv => exact henv
                constructor
                · intro a ha
                  exact hwfcf₁₀.1 a ha
                · simpa [VarEnv.update] using (wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf)
              have hwfcfg_body_init₁ :
                  wfConfig
                    { memory := c₁₁.memory
                      varEnv := env₁.update x₁ v₂₁
                      nextAddr := c₁₁.nextAddr
                      pureMode := false } := by
                have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                  (wfConfig_preserved e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
                have hnext₂_to₁ : c₂'₁.nextAddr ≤ c₁₁.nextAddr :=
                  terminatesTo_nextAddr_mono e1 c₂'₁ c₁₁ (Value.closure x₁ body₁ env₁) ht₁_e1
                have hv₂₁_wf : wfValue c₁₁.nextAddr v₂₁ :=
                  wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
                have hv₁_closure_wf : wfValue c₁₁.nextAddr (Value.closure x₁ body₁ env₁) :=
                  (wfConfig_preserved e1 _ c₁₁ _ ht₁_e1 hwfcf₂₁).2
                have henv₁_wf : wfVarEnv c₁₁.nextAddr env₁ := by
                  cases hv₁_closure_wf with
                  | closure _ _ _ henv => exact henv
                constructor
                · intro a ha
                  exact hwfcf₁₁.1 a ha
                · simpa [VarEnv.update] using (wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf)
              have hwfcfg_body_final₀ : wfConfig evalCfg₀ := by
                exact (wfConfig_preserved body₀ _ evalCfg₀ o₀ ht₀_body hwfcfg_body_init₀).1
              have hwfcfg_body_final₁ : wfConfig evalCfg₁ := by
                exact (wfConfig_preserved body₁ _ evalCfg₁ o₁ ht₁_body hwfcfg_body_init₁).1
              have ht₀_body' :
                  terminatesTo body₀
                    { memory := c₁₀.memory
                      varEnv := env₀.update x₀ v₂₀
                      nextAddr := c₁₀.nextAddr
                      pureMode := false } evalCfg₀ o₀ := by
                simpa using ht₀_body
              have ht₁_body' :
                  terminatesTo body₀
                    { memory := c₁₁.memory
                      varEnv := env₁.update x₁ v₂₁
                      nextAddr := c₁₁.nextAddr
                      pureMode := false } evalCfg₁ o₁ := by
                simpa [hbody] using ht₁_body
              have hstep_body := hIH_body hpredlaws hTmBody
                c₁₀.memory c₁₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
                evalCfg₀ evalCfg₁ o₀ o₁
                hθ₀1wf hθ₁1wf hwfBodyCtx htagBoundedBody hric_body₀ hric_body₁ htagR_body
                hcwr_body₀ hcwr_body₁ hagree_body_start
                c₁₀.nextAddr c₁₁.nextAddr false
                hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
              rcases hstep_body with
                ⟨_hresTm_body,
                  ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                    _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after, _htagBounded_body_after,
                    _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                    _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                    _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                    _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩⟩
              have hAgree_out_body :
                  agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                have hsrc_mem : firstShared ∈ first :: rest := by
                  rcases applyFnTClosure_ok_of_mem_mapM
                      (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result2 := result1) (fuel := fuel')
                      (tcls := tcls) (results := results)
                      (tcl := FnTClosure.regular x₀ body₀ σcap)
                      hmap hmem with
                    ⟨r, hr_mem, happly_r⟩
                  have hr_eq : r = firstShared := by
                    have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                      simpa [happly_r] using happly
                    exact Except.ok.inj hEq
                  subst hr_eq
                  simpa [heq_results] using hr_mem
                have hagree_src :
                    agreeOnClean predSat (ctxAfter ctxᵢ firstShared).regime (ctxAfter ctxᵢ firstShared)
                      cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                  have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                    regime_monotone bodyCtx body₀ fuelBody result3Shared htcBody'
                  have hres1_to_src_mono :
                      Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                        (ctxAfter ctxᵢ firstShared).regime := by
                    simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  constructor
                  · intro l qt hlookup hclean
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hclean_body :
                        qtypCleanUnder (ctxAfter bodyCtx result3Shared).regime qt := by
                      simpa [ctxAfter, hfirstShared] using hclean
                    have hloc_agree_body := hagree_body_after.1 l qt hlookup_body hclean_body
                    cases hloc_agree_body with
                    | both_unrealized _ _ hnone₀ hnone₁ =>
                        exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                    | agree_values _ _ a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                        have hlookup₀' : cf₀.memory.lookup a₀' = some n₀ := by
                          simpa [hmem₀_eq] using hlookup₀
                        have hlookup₁' : cf₁.memory.lookup a₁' = some n₁ := by
                          simpa [hmem₁_eq] using hlookup₁
                        have hagree_val' :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₁.memory θ₀_body θ₁_body qt
                              (Value.num n₀) (Value.num n₁) := by
                          simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hagree_val
                        exact
                          agreeLocUnder.agree_values l qt a₀' a₁' n₀ n₁
                            hreal₀ hreal₁ hlookup₀' hlookup₁' hagree_val'
                  · intro x qt hlookup hclean
                    have hclean_res1 :
                        qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime qt :=
                      cleanUnder_of_monotone hres1_to_src_mono hclean
                    have hvar_agree1 := hagree1.2 x qt hlookup hclean_res1
                    cases hvar_agree1 with
                    | both_none _ _ hnone₀ hnone₁ =>
                        have hnone₀' : cf₀.varEnv.lookup x = none := by
                          simpa [hvar₀_eq] using hnone₀
                        have hnone₁' : cf₁.varEnv.lookup x = none := by
                          simpa [hvar₁_eq] using hnone₁
                        exact agreeVarUnder.both_none x qt hnone₀' hnone₁'
                    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree_val1 =>
                        have hlookup₀' : cf₀.varEnv.lookup x = some v₀ := by
                          simpa [hvar₀_eq] using hlookup₀
                        have hlookup₁' : cf₁.varEnv.lookup x = some v₁ := by
                          simpa [hvar₁_eq] using hlookup₁
                        have hagree_src_regime :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              c₁₀.memory c₁₁.memory θ₀1 θ₁1 qt v₀ v₁ :=
                          agreeValueUnder_clean_monotoneRegime hres1_to_src_mono hclean hagree_val1
                        have hagree_src_final :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₁.memory θ₀_body θ₁_body qt v₀ v₁ :=
                          by
                            have hqtypPredHolds_mem_app_out₀ :
                                ∀ (qt' : QTyp) (v' : Value),
                                  qtypPredHolds predSat qt' c₁₀.memory v' ↔
                                    qtypPredHolds predSat qt' cf₀.memory v' :=
                              qtypPredHolds_mem_compat_of_predSatLaws
                                (hpredlaws := hpredlaws) (θ := θ₀1)
                                (μ := c₁₀.memory) (μ' := cf₀.memory)
                            have hqtypPredHolds_mem_app_out₁ :
                                ∀ (qt' : QTyp) (v' : Value),
                                  qtypPredHolds predSat qt' c₁₁.memory v' ↔
                                    qtypPredHolds predSat qt' cf₁.memory v' :=
                              qtypPredHolds_mem_compat_of_predSatLaws
                                (hpredlaws := hpredlaws) (θ := θ₁1)
                                (μ := c₁₁.memory) (μ' := cf₁.memory)
                            exact
                              agreeValueUnder_clean_extends_transport_mem
                                hqtypPredHolds_mem_app_out₀ hqtypPredHolds_mem_app_out₁
                                hclean _hθext₀_body.1 _hθext₁_body.1 hagree_src_regime
                        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀' hlookup₁' hagree_src_final
                have h_clean_res_to_src :
                    ∀ qt,
                      qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                      qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt := by
                  intro qt hclean
                  cases hclean with
                  | clean hpoison =>
                      exact qtypCleanUnder.clean hpoison
                  | guard k htag hk hnotfun =>
                      have hk_src :
                          (ctxAfter ctxᵢ firstShared).regime.lookup? k = some true :=
                        joinTypeResults_lookup_member_regime_compat
                          (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                          h_join hsrc_mem k true hk
                      exact qtypCleanUnder.guard k htag hk_src hnotfun
                have h_mem_from_src_or_unrealized :
                    ∀ l qt,
                      (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
                      qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                      ((∃ qt_src,
                          (ctxAfter ctxᵢ firstShared).memEnv.lookup l = some qt_src ∧
                          qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src ∧
                          qt.etyp = qt_src.etyp ∧
                          (qt.poison = false → qt_src.poison = false)) ∨
                        (θ₀_body.lookup l = none ∧ θ₁_body.lookup l = none)) := by
                  intro l qt hlookup hclean
                  by_cases hlookup_src_none : (ctxAfter ctxᵢ firstShared).memEnv.lookup l = none
                  · right
                    have hlookup_body_none :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = none := by
                      simpa [ctxAfter, hfirstShared] using hlookup_src_none
                    have hnot_contains_body :
                        ¬ (ctxAfter bodyCtx result3Shared).memEnv.contains l := by
                      intro hcontains
                      have hmem : l ∈ (ctxAfter bodyCtx result3Shared).memEnv :=
                        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                      have hlookup_isSome :
                          ((ctxAfter bodyCtx result3Shared).memEnv[l]?).isSome = true :=
                        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                      have hlookup_get_none :
                          (ctxAfter bodyCtx result3Shared).memEnv[l]? = none := by
                        simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup_body_none
                      simp [hlookup_get_none] at hlookup_isSome
                    have htheta₀_none :
                        θ₀_body.lookup l = none :=
                      theta_not_contains_if_not_in_memEnv
                        (ctx := (ctxAfter bodyCtx result3Shared))
                        (μ := evalCfg₀.memory) (ρ := evalCfg₀.varEnv) (θ := θ₀_body)
                        (l := l) _hric_body_final₀ hnot_contains_body
                    have htheta₁_none :
                        θ₁_body.lookup l = none :=
                      theta_not_contains_if_not_in_memEnv
                        (ctx := (ctxAfter bodyCtx result3Shared))
                        (μ := evalCfg₁.memory) (ρ := evalCfg₁.varEnv) (θ := θ₁_body)
                        (l := l) _hric_body_final₁ hnot_contains_body
                    exact ⟨htheta₀_none, htheta₁_none⟩
                  · left
                    rcases Option.ne_none_iff_exists'.1 hlookup_src_none with ⟨qt_src, hlookup_src⟩
                    have hclean_src : qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src :=
                      joinTypeResults_lookup_member_clean_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hclean hlookup_src
                    have hetyp_eq : qt.etyp = qt_src.etyp :=
                      joinTypeResults_lookup_member_etyp_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hlookup_src
                    have hpoison_imp : qt.poison = false → qt_src.poison = false :=
                      joinTypeResults_lookup_member_poison_imp
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hlookup_src
                    exact ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
                have hlookup_back_res_to_src :
                    ∀ k b,
                      (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                      (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b := by
                  intro k b hk
                  exact
                    joinTypeResults_lookup_member_regime_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem k b hk
                exact
                  join_transport_agreeOnClean_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ)
                    (first := first)
                    (src := firstShared)
                    (rest := rest)
                    (res := res)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                    (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                    (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                    h_join hsrc_mem hagree_src h_clean_res_to_src h_mem_from_src_or_unrealized
                    (fun {σcap} {ρcap} h =>
                      memberVarsRegimeEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₀.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberCvcrEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₀.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberVarsRegimeEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₁.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberCvcrEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₁.memory)
                        hlookup_back_res_to_src h)
              have hOutPack_body :
                  valueHasETyp θ₀_body o₀ res.qualType.etyp ∧
                  valueHasETyp θ₁_body o₁ res.qualType.etyp ∧
                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_body ∧
                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_body ∧
                  consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body ∧
                  consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₁.memory cf₁.varEnv θ₁_body ∧
                  agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body ∧
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                    res.qualType cf₀.memory θ₀_body o₀ ∧
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                    res.qualType cf₁.memory θ₁_body o₁ ∧
                  resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                    cf₀.memory cf₁.memory θ₀_body θ₁_body res.qualType o₀ o₁ := by
                have hsrc_mem' : firstShared ∈ first :: rest := by
                  rcases applyFnTClosure_ok_of_mem_mapM
                      (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result2 := result1) (fuel := fuel')
                      (tcls := tcls) (results := results)
                      (tcl := FnTClosure.regular x₀ body₀ σcap)
                      hmap hmem with
                    ⟨r, hr_mem, happly_r⟩
                  have hr_eq : r = firstShared := by
                    have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                      simpa [happly_r] using happly
                    exact Except.ok.inj hEq
                  subst hr_eq
                  simpa [heq_results] using hr_mem
                have hfirstShared_etyp : firstShared.qualType.etyp = result3Shared.qualType.etyp := by
                  rw [hfirstShared]; unfold normalizeAppResultByProvenance; split_ifs <;> rfl
                have hres1_to_src_mono :
                    Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      (ctxAfter ctxᵢ firstShared).regime := by
                  have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                    regime_monotone bodyCtx body₀ fuelBody result3Shared htcBody'
                  simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                have hlookup_back_res1_to_src :
                    ∀ k b,
                      (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
                  intro k b hk_src
                  have hRdef_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k ≠ none := by
                    intro hnone
                    rw [hk_src] at hnone
                    contradiction
                  have hRdef_res1 :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                    hres1_to_src_mono.2 k hRdef_src
                  cases hk_res1 : (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
                  | none =>
                      exact False.elim (hRdef_res1 hk_res1)
                  | some b1 =>
                      have hcases := hres1_to_src_mono.1 k b1 hk_res1
                      cases hcases with
                      | inl hk_src' =>
                          have hb_eq : b1 = b := by
                            have : some b1 = some b := by
                              calc
                                some b1 = (ctxAfter ctxᵢ firstShared).regime.lookup? k := hk_src'.symm
                                _ = some b := hk_src
                            exact Option.some.inj this
                          simp [hb_eq]
                      | inr hnone_src =>
                          rw [hnone_src] at hk_src
                          cases hk_src
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAgree_out_body, ?_, ?_, ?_⟩
                · -- shared-member valueHasETyp -> joined valueHasETyp (run 0).
                  have hv_src₀ : valueHasETyp θ₀_body o₀ firstShared.qualType.etyp := by
                    rw [hfirstShared_etyp]
                    exact _hv_body₀_typed
                  exact
                    joinTypeResults_transport_valueHasETyp_from_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (θ := θ₀_body) (v := o₀)
                      h_join hsrc_mem' hv_src₀
                · -- shared-member valueHasETyp -> joined valueHasETyp (run 1).
                  have hv_src₁ : valueHasETyp θ₁_body o₁ firstShared.qualType.etyp := by
                    rw [hfirstShared_etyp]
                    exact _hv_body₁_typed
                  exact
                    joinTypeResults_transport_valueHasETyp_from_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (θ := θ₁_body) (v := o₁)
                      h_join hsrc_mem' hv_src₁
                · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hsrc_mem_to_res :
                      ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                    joinTypeResults_mem_contains_of_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem'
                  constructor
                  · intro l a hθ
                    have hloc_src := _hric_body_final₀.1 l a hθ
                    rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                    have hcontains_src : firstShared.memEnv'.contains l := by
                      simpa [ctxAfter, hfirstShared] using hcontains_src_body
                    refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                    simpa [hmem₀_eq] using hmem_contains
                  · intro x qt hlookup
                    have hlookup_ctx :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                      simpa [ctxAfter] using hlookup
                    rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                    refine ⟨v, ?_⟩
                    constructor
                    · simpa [hvar₀_eq] using hlookup_v
                    · exact valueHasETyp_extends _hθext₀_body.1 hv_typ
                · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  have hsrc_mem_to_res :
                      ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                    joinTypeResults_mem_contains_of_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem'
                  constructor
                  · intro l a hθ
                    have hloc_src := _hric_body_final₁.1 l a hθ
                    rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                    have hcontains_src : firstShared.memEnv'.contains l := by
                      simpa [ctxAfter, hfirstShared] using hcontains_src_body
                    refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                    simpa [hmem₁_eq] using hmem_contains
                  · intro x qt hlookup
                    have hlookup_ctx :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                      simpa [ctxAfter] using hlookup
                    rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                    refine ⟨v, ?_⟩
                    constructor
                    · simpa [hvar₁_eq] using hlookup_v
                    · exact valueHasETyp_extends _hθext₁_body.1 hv_typ
                · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hpred_compat₀ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₀.memory v' ↔
                          qtypPredHolds predSat qt' cf₀.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₀1)
                      (μ := c₁₀.memory) (μ' := cf₀.memory)
                  have hcwr_src₀ :
                      consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        (ctxAfter ctxᵢ firstShared) cf₀.memory cf₀.varEnv θ₀_body := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro l qt k hlookup hguard hRdef
                      have hlookup_body :
                          (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                        simpa [ctxAfter, hfirstShared] using hlookup
                      have hguard_body : qtypGuardTag qt = some k := by
                        simpa [ctxAfter, hfirstShared] using hguard
                      have hRdef_body :
                          (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                        simpa [ctxAfter, hfirstShared] using hRdef
                      have hloc_body :=
                        _hcwr_body_final₀.1 l qt k hlookup_body hguard_body hRdef_body
                      simpa [ctxAfter, hfirstShared, hmem₀_eq] using hloc_body
                    · intro x qt k hlookup hguard hRdef
                      cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                      | none =>
                          exact False.elim (hRdef hk_src)
                      | some b =>
                          have hRdef_res1 :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                            intro hnone
                            have hk_back := hlookup_back_res1_to_src k b hk_src
                            rw [hk_back] at hnone
                            contradiction
                          have hlookup_res1_ctx :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                            simpa [ctxAfter] using hlookup
                          have hvar_res1 :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                c₁₀.memory c₁₀.varEnv (x, qt) :=
                            hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                          have hvar_res1_mem :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                cf₀.memory c₁₀.varEnv (x, qt) :=
                            varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                          have hvar_src :
                              varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                                cf₀.memory c₁₀.varEnv (x, qt) :=
                            varsRegime_transport_active_lookup_back
                              (predSat := predSat)
                              (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                              (R' := (ctxAfter ctxᵢ firstShared).regime)
                              (μ := cf₀.memory) (ρ := c₁₀.varEnv) (entry := (x, qt))
                              hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                          simpa [hvar₀_eq] using hvar_src
                    · intro x qt v hlookup hlookup_v
                      have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                        (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                      exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ _hθext₀_body.1
                        (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                  exact
                    joinTypeResults_transport_consistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                      h_join hsrc_mem' hcwr_src₀
                · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  have hpred_compat₁ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₁.memory v' ↔
                          qtypPredHolds predSat qt' cf₁.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₁1)
                      (μ := c₁₁.memory) (μ' := cf₁.memory)
                  have hcwr_src₁ :
                      consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        (ctxAfter ctxᵢ firstShared) cf₁.memory cf₁.varEnv θ₁_body := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro l qt k hlookup hguard hRdef
                      have hlookup_body :
                          (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                        simpa [ctxAfter, hfirstShared] using hlookup
                      have hguard_body : qtypGuardTag qt = some k := by
                        simpa [ctxAfter, hfirstShared] using hguard
                      have hRdef_body :
                          (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                        simpa [ctxAfter, hfirstShared] using hRdef
                      have hloc_body :=
                        _hcwr_body_final₁.1 l qt k hlookup_body hguard_body hRdef_body
                      simpa [ctxAfter, hfirstShared, hmem₁_eq] using hloc_body
                    · intro x qt k hlookup hguard hRdef
                      cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                      | none =>
                          exact False.elim (hRdef hk_src)
                      | some b =>
                          have hRdef_res1 :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                            intro hnone
                            have hk_back := hlookup_back_res1_to_src k b hk_src
                            rw [hk_back] at hnone
                            contradiction
                          have hlookup_res1_ctx :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                            simpa [ctxAfter] using hlookup
                          have hvar_res1 :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                c₁₁.memory c₁₁.varEnv (x, qt) :=
                            hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                          have hvar_res1_mem :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                cf₁.memory c₁₁.varEnv (x, qt) :=
                            varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                          have hvar_src :
                              varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                                cf₁.memory c₁₁.varEnv (x, qt) :=
                            varsRegime_transport_active_lookup_back
                              (predSat := predSat)
                              (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                              (R' := (ctxAfter ctxᵢ firstShared).regime)
                              (μ := cf₁.memory) (ρ := c₁₁.varEnv) (entry := (x, qt))
                              hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                          simpa [hvar₁_eq] using hvar_src
                    · intro x qt v hlookup hlookup_v
                      have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                        (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                      exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ _hθext₁_body.1
                        (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                  exact
                    joinTypeResults_transport_consistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                      h_join hsrc_mem' hcwr_src₁
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hval_src₀ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        firstShared.qualType cf₀.memory θ₀_body o₀ := by
                    have hval_first :
                        valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          evalCfg₀.memory θ₀_body o₀ :=
                      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) _hvalc_body₀
                    simpa [ctxAfter, hfirstShared, hmem₀_eq] using hval_first
                  exact
                    joinTypeResults_transport_valueConsistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                      h_join hsrc_mem' hval_src₀
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hval_src₁ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        firstShared.qualType cf₁.memory θ₁_body o₁ := by
                    have hval_first :
                        valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          evalCfg₁.memory θ₁_body o₁ :=
                      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) _hvalc_body₁
                    simpa [ctxAfter, hfirstShared, hmem₁_eq] using hval_first
                  exact
                    joinTypeResults_transport_valueConsistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                      h_join hsrc_mem' hval_src₁
                · -- shared-member resultAgreesIfClean -> joined result qualType.
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hres_agree_src :
                      resultAgreesIfClean predSat (ctxAfter ctxᵢ firstShared).regime
                        cf₀.memory cf₁.memory θ₀_body θ₁_body firstShared.qualType o₀ o₁ := by
                    have hres_agree_first :
                        resultAgreesIfClean predSat (ctxAfter bodyCtx result3Shared).regime
                          evalCfg₀.memory evalCfg₁.memory θ₀_body θ₁_body
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          o₀ o₁ :=
                      resultAgreesIfClean_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ₀ := evalCfg₀.memory) (μ₁ := evalCfg₁.memory)
                        (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                        _hres_agree_body
                    simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hres_agree_first
                  exact
                    joinTypeResults_transport_resultAgreesIfClean_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ₀ := cf₀.memory) (μ₁ := cf₁.memory) (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                      (o₀ := o₀) (o₁ := o₁)
                      h_join hsrc_mem' hres_agree_src
              exact ⟨θ₀_body, θ₁_body,
                wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 _hθext₀_body),
                wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 _hθext₁_body),
                hOutPack_body⟩
            · -- Fallback: no shared closure (¬ internalPoisonClean).
              have hptrue : p = true := by
                have : ¬ p = false := by
                  simpa [hetyp1, internalPoisonClean, getInternalPoison] using hdirty
                cases p <;> simp at this
                rfl
              have h_p1p : joinPoison p1 p = true := by
                simp [hptrue, joinPoison]
              exact hOutMapChoice_p1p_true h_p1p
          · -- Fallback: ¬ qtypCleanUnder result1.qualType. resultAgreesIfClean is vacuous (arrow ⇒ p1=true ⇒ res poison/noPred); rest needs unary member-evidence helper.
            have hpoison1_true : result1.qualType.poison = true := by
              by_contra hfalse
              have hpoison_false : result1.qualType.poison = false := Bool.eq_false_iff.mpr hfalse
              have hclean : qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType :=
                qtypCleanUnder.clean hpoison_false
              exact hclean1_e1 hclean
            have h_p1p : joinPoison p1 p = true := by
              rw [← hp1]
              simp [hpoison1_true, joinPoison]
            exact hOutMapChoice_p1p_true h_p1p
        rcases hOutMapChoice with ⟨θ₀_out, θ₁_out, hθext_out₀, hθext_out₁, hOutPack⟩
        rcases hOutPack with
          ⟨hv_out₀, hv_out₁, hric_out₀, hric_out₁,
            hcwr_out₀, hcwr_out₁, hAgree_out, hvalc_out₀, hvalc_out₁, hres_agree_out⟩
        have hwf_result1 : wfTypeResult result1 := by
          simp only [ctxAfter, wfTypeContext, wfTypeResult] at hwf1 ⊢
          exact hwf1.1
        have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := hqt2 ▸ hresTm2
        have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
          QTypRespectsTagMeaning_transport_etyp_pred
            (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
            (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hresTm2_arg rfl rfl
        have hresults_wf :
            ∀ r, r ∈ results → wfTypeResult r :=
          mapM_applyFnTClosure_forall_wfTypeResult
            (fuel_top := fuel' + 1)
            (IH := fun m _ e ctx' res' hwf htc =>
              typecheckExpr_preserves_wfTypeResult ctx' e m res' hwf htc)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result_fn := result1) (fuel_call := fuel')
            (h_call_lt := Nat.lt_succ_self fuel')
            hwf_result1
            (tcls := tcls) (results := results)
            (by -- CapturedEnvRefLocsFullBounded for each closure
                have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1
                  (wfTypeContext_of_wfTypeResult ctxᵢ result2
                    (typecheckExpr_preserves_wfTypeResult ctxᵢ e2 fuel' result2 hwf htc2')
                    hwf (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2'))
                  htc1'
                rw [hetyp1] at hClosRL; intro tcl htcl; exact hClosRL tcl htcl)
            (by -- etypRefLocsBounded for arg at result1.nextLoc'
                have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                simp [hqt2] at h
                exact etypRefLocsBounded_mono h
                  (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
            (by -- etypClosuresCapturedRefLocsBounded for arg at result1.nextLoc'
                have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                simp [hqt2] at h
                exact etypClosuresCapturedRefLocsBounded_mono h
                  (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
            hmap
        have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctxᵢ result1) := by
          simpa [ctxAfter] using hTm1
        have hresults_tm :
            ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctxᵢ r) :=
          mapM_applyFnTClosure_forall_wfTagMeaningCtx
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx hresTm1 hetyp1 hresTm2_arg hmap
        have hresults_regime :
            ∀ r, r ∈ results →
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          have htagR1_ctx :
              regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
            simpa [ctxAfter] using htagR1
          exact
            mapM_applyFnTClosure_forall_regimeConsistentWithCtx
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              htagR1_ctx hmap
        have hresults_qtm :
            ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
          mapM_applyFnTClosure_forall_QTypRespectsTagMeaning
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx hresTm1 hetyp1 hresTm2_arg hmap
        have hfirst_in_results : first ∈ results := by
          simp [heq_results]
        have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
        have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctxᵢ first) := hresults_tm first hfirst_in_results
        have h_first_regime :
            regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
          hresults_regime first hfirst_in_results
        have h_first_qtm : QTypRespectsTagMeaning tm first.qualType :=
          by
            intro qt' k d hinq hqd
            exact hresults_qtm first hfirst_in_results hinq hqd
        have h_rest_wf : ∀ r ∈ rest, wfTypeResult r := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_wf r hmem_results
        have h_rest_regime :
            ∀ r ∈ rest,
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_regime r hmem_results
        have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          intro qt' k d hinq hqd
          exact hresults_qtm r hmem_results hinq hqd
        have h_mem_join :
            ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l :=
          joinTypeResults_mem_contains_head_or_rest
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_tag_join :
            tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv (ctxAfter ctxᵢ res).regime :=
          joinTypeResults_tagEnvConsistentWithRegime
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
            h_join h_first_regime h_rest_regime
        refine ⟨?_, θ₀_out, θ₁_out,
          ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- QTypRespectsTagMeaning tm res.qualType
          exact
            joinTypeResults_QTypRespectsTagMeaning
              (tm := tm)
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_first_qtm h_rest_qtm
        · -- wfExtendsMap θ₀ θ₀'
          exact hθext_out₀
        · -- wfExtendsMap θ₁ θ₁'
          exact hθext_out₁
        · -- valueHasETyp θ₀1 o₀ res.qualType.etyp
          exact hv_out₀
        · -- valueHasETyp θ₁1 o₁ res.qualType.etyp
          exact hv_out₁
        · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
          exact
            join_transport_wfTagMeaningCtx
              (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_first_tm
        · -- wfTypeContext (ctxAfter ctxᵢ res)
          exact
            join_transport_wfTypeContext
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_mem_join
              (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                (Nat.le_trans
                  (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                    (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                  (mapM_applyFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel' tcls results hmap first hfirst_in_results)))
              h_rest_wf
        · -- TagBoundedCtx (ctxAfter ctxᵢ res)
          exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
        · -- wfConfig cf₀
          exact (wfConfig_preserved (Expr.app e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
        · -- wfConfig cf₁
          exact (wfConfig_preserved (Expr.app e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
        · -- runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀1
          exact hric_out₀
        · -- runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁1
          exact hric_out₁
        · -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
          exact
            join_transport_regimeConsistentWithCtx
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_tag_join h_first_regime
        · -- consistentWithRegime ... cf₀
          exact hcwr_out₀
        · -- consistentWithRegime ... cf₁
          exact hcwr_out₁
        · -- agreeOnClean ...
          exact hAgree_out
        · -- valueConsistentWithRegime ... cf₀.memory o₀
          exact hvalc_out₀
        · -- valueConsistentWithRegime ... cf₁.memory o₁
          exact hvalc_out₁
        · -- resultAgreesIfClean ...
          exact hres_agree_out
      · -- Run 1: peClosure (mixed case, impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₁1_arrow : valueHasETyp θ₁1 (Value.peClosure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        cases hv₁1_arrow
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Run 0: peClosure, Run 1: closure (mixed case, impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_arrow
      · -- Run 0: peClosure, Run 1: peClosure (impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_arrow
  | inr h_parrow =>
    -- Pure arrow case (peClosure)
    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, hp1, _hnempty, _hsub,
            hmap, heq_results, h_join⟩ := h_parrow
    have htc2' : typecheck ctxᵢ e2 fuel' = .ok result2 := by
      simpa [typecheck] using htc2
    have htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
      simp [ctxAfter] at htc1 ⊢
      exact htc1
    intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm htagBounded result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    have hstruct₀ := terminatesTo_app_inv' e1 e2 cinit₀ cf₀ o₀ ht₀
    have hstruct₁ := terminatesTo_app_inv' e1 e2 cinit₁ cf₁ o₁ ht₁
    -- Handle runtime closure/peClosure splits for the parrow-typed branch.
    rcases hstruct₀ with h_clo₀ | h_peclo₀
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Both runs: closure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_parrow
      · -- Run 0: closure, Run 1: peClosure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_parrow
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Run 0: peClosure, Run 1: closure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₁1_parrow : valueHasETyp θ₁1 (Value.closure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        cases hv₁1_parrow
      · -- Both runs: peClosure (the real case for parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        -- Phase A: Apply IH for e2
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        -- Phase B: Apply IH for e1
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        -- Phase C: Invert peClosure typing to extract closure structure
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        have hv₁1_parrow : valueHasETyp θ₁1 (Value.peClosure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        -- Invert peClosure typing for both runs
        cases hv₀1_parrow with
        | peClosure hpure₀ htcl₀ henv₀_typing hcover₀ =>
        cases hv₁1_parrow with
        | peClosure hpure₁ htcl₁ henv₁_typing hcover₁ =>
        -- Phase D: Extract body typing from applyPFnTClosure via mapM membership
        rcases applyPFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₀ _ _ hmap htcl₀
          with ⟨fuelBody₀, first₀, result3₀, _happly₀, hfuel₀, htc_body₀, _hsub₀, hfirst₀_eq⟩
        -- Synchronization is used only under a clean-result assumption for `result1`.
        -- Keep it deferred to avoid requiring a global clean fact at this point.
        have _hsync1_of_clean :
              ∀ hclean1_e1 :
                  qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
              (∃ x pbody σcap,
                  Expr.toPExpr? body₀ = some pbody ∧
                  PFnTClosure.regular x pbody σcap ∈ tcls ∧
                  x₀ = x ∧
                  x₁ = x ∧
                  body₀ = body₁ ∧
                  agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory σcap env₀ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory θ₀1 σcap env₀ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory σcap env₁ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory θ₁1 σcap env₁)
              ∨ (¬ internalPoisonClean result1.qualType) :=
          fun hclean1_e1 =>
            stepFR_app_parrow_sync_from_clean
              (predSat := predSat)
              (ctx := (ctxAfter ctxᵢ result2))
              (res1 := result1)
              (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
              (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
              (θ₀ := θ₀1) (θ₁ := θ₁1)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              (env₀ := env₀) (env₁ := env₁)
              hetyp1 hclean1_e1 hres_agree1
        have _hextract_shared_of_sync :
            (∃ x pbody σcap,
                Expr.toPExpr? body₀ = some pbody ∧
                PFnTClosure.regular x pbody σcap ∈ tcls ∧
                x₀ = x ∧
                x₁ = x ∧
                body₀ = body₁) →
              ∃ x pbody σcap fuelBody first result3,
                Expr.toPExpr? body₀ = some pbody ∧
                PFnTClosure.regular x pbody σcap ∈ tcls ∧
                x₀ = x ∧
                x₁ = x ∧
                body₀ = body₁ ∧
                applyPFnTClosure (PFnTClosure.regular x pbody σcap) st1 st2 p p1
                  etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok first ∧
                fuel' = Nat.succ fuelBody ∧
                typecheckExpr
                  { ctxᵢ with
                    pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                    memEnv := result1.memEnv'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                    tagEnv := result1.tagEnv'
                    pureCtx := true
                    nextTag := result1.nextTag'
                    nextLoc := result1.nextLoc'
                    regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
                isSubtype st2 result3.qualType = true ∧
                first =
                  { result3 with
                    qualType :=
                      normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } :=
          fun hsync =>
            stepFR_app_parrow_extract_shared_member
              (ctx := ctxᵢ)
              (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              hmap hsync
        have _sync_extract_of_clean :
            ∀ hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
              (∃ x pbody σcap fuelBody firstShared result3Shared,
                  Expr.toPExpr? body₀ = some pbody ∧
                  PFnTClosure.regular x pbody σcap ∈ tcls ∧
                  x₀ = x ∧
                  x₁ = x ∧
                  body₀ = body₁ ∧
                  agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory σcap env₀ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory θ₀1 σcap env₀ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory σcap env₁ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory θ₁1 σcap env₁ ∧
                  applyPFnTClosure (PFnTClosure.regular x pbody σcap) st1 st2 p p1
                    etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok firstShared ∧
                  fuel' = Nat.succ fuelBody ∧
                  typecheckExpr
                    { ctxᵢ with
                      pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                      memEnv := result1.memEnv'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                      tagEnv := result1.tagEnv'
                      pureCtx := true
                      nextTag := result1.nextTag'
                      nextLoc := result1.nextLoc'
                      regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3Shared ∧
                  isSubtype st2 result3Shared.qualType = true ∧
                  firstShared =
                    { result3Shared with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) } })
              ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          rcases _hsync1_of_clean hclean1_e1 with hsync | hdirty
          · left
            rcases hsync with ⟨x, pbody, σcap, htoPExpr, hmem, hx₀, hx₁, hbody, hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
            rcases applyPFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x pbody σcap hmap hmem with
              ⟨fuelBody, firstShared, result3Shared, happly', hfuel', htc', hsub', hfirst'⟩
            exact ⟨x, pbody, σcap, fuelBody, firstShared, result3Shared, htoPExpr,
              hmem, hx₀, hx₁, hbody, hcap, hmv₀, hmc₀, hmv₁, hmc₁, happly', hfuel', htc', hsub', hfirst'⟩
          · right
            exact hdirty
        -- htc_body₀ : typecheckExpr bodyCtx (PExpr.toExpr pbody₀) fuelBody₀ = .ok result3₀
        -- hfuel₀ : fuel' = Nat.succ fuelBody₀
        -- Phase E: Simplify using cf₀ = c₁₀, cf₁ = c₁₁ (pure closure config preservation)
        subst heq_cfg₀ heq_cfg₁
        -- Phase F: Per-member preservation via mapM transport
        have hwf_result1 : wfTypeResult result1 := by
          simp only [ctxAfter, wfTypeContext, wfTypeResult] at hwf1 ⊢
          exact hwf1.1
        have hresults_wf :
            ∀ r, r ∈ results → wfTypeResult r :=
          mapM_applyPFnTClosure_forall_wfTypeResult'
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            hwf_result1
            (tcls := tcls) (results := results)
            (by -- CapturedEnvRefLocsFullBounded for each parrow closure
                have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
                rw [hetyp1] at hClosRL; intro tcl htcl; exact hClosRL tcl htcl)
            (by -- etypRefLocsBounded for arg at result1.nextLoc'
                have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypRefLocsBounded_mono h
                  (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
            (by -- etypClosuresCapturedRefLocsBounded for arg
                have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                  (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
            hmap
        have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctxᵢ result1) := by
          simpa [ctxAfter] using _hTm1
        have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
          simpa [hqt2] using (_hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
        have hresults_tm :
            ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctxᵢ r) :=
          mapM_applyPFnTClosure_forall_wfTagMeaningCtx
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx _hresTm1 hetyp1 hresTm2_arg hmap
        have hresults_regime :
            ∀ r, r ∈ results →
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          have htagR1_ctx :
              regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
            simpa [ctxAfter] using htagR1
          exact
            mapM_applyPFnTClosure_forall_regimeConsistentWithCtx
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              htagR1_ctx hmap
        have hresults_qtm :
            ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
          mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx _hresTm1 hetyp1 hresTm2_arg hmap
        have hfirst_in_results : first ∈ results := by
          simp [heq_results]
        have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
        have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctxᵢ first) := hresults_tm first hfirst_in_results
        have h_first_regime :
            regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
          hresults_regime first hfirst_in_results
        have h_first_qtm : QTypRespectsTagMeaning tm first.qualType := by
          intro qt' k d hinq hqd
          exact hresults_qtm first hfirst_in_results hinq hqd
        have h_rest_wf : ∀ r ∈ rest, wfTypeResult r := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_wf r hmem_results
        have h_rest_regime :
            ∀ r ∈ rest,
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_regime r hmem_results
        have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          intro qt' k d hinq hqd
          exact hresults_qtm r hmem_results hinq hqd
        have h_mem_join :
            ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l :=
          joinTypeResults_mem_contains_head_or_rest
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_tag_join :
            tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv (ctxAfter ctxᵢ res).regime :=
          joinTypeResults_tagEnvConsistentWithRegime
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
            h_join h_first_regime h_rest_regime
        -- Case split: clean vs not-clean for result1
        have hOutPack_p1p_true
            (h_p1p : joinPoison p1 p = true) :
            QTypRespectsTagMeaning tm res.qualType ∧
            ∃ θ₀' θ₁',
              wfExtendsMap θ₀ θ₀' ∧
              wfExtendsMap θ₁ θ₁' ∧
              valueHasETyp θ₀' o₀ res.qualType.etyp ∧
              valueHasETyp θ₁' o₁ res.qualType.etyp ∧
              wfTagMeaningCtx tm (ctxAfter ctxᵢ res) ∧
              wfTypeContext (ctxAfter ctxᵢ res) ∧
              TagBoundedCtx (ctxAfter ctxᵢ res) ∧
              wfConfig cf₀ ∧
              wfConfig cf₁ ∧
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' ∧
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' ∧
              regimeConsistentWithCtx (ctxAfter ctxᵢ res) ∧
              consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀' ∧
              consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁' ∧
              agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' ∧
              valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀' o₀ ∧
              valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁' o₁ ∧
              resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁ := by
          rcases list_mapM_ok_mem_output_exists_input
              (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
              (xs := tcls) (ys := results) (y := first) hmap (by simp [heq_results])
            with ⟨tcl, _htcl_mem, happly_first⟩
          have hfirst_pack :
              first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
            applyPFnTClosure_ok_poison_pred_of_p1p_true
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result2 := result1) (fuel := fuel') (tcl := tcl) (r := first)
              h_p1p happly_first
          have hres_pack :
              res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred :=
            joinTypeResults_poison_pred_of_head_true_noPred
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join hfirst_pack.1 hfirst_pack.2
          -- ===== Per-run body IH for not qtypCleanUnder (p1=true) =====
          -- Extract σcap + pbody from closureCapturedVarsRegime for each run.
          have ⟨σcapA₀, pbodyA₀, htoPExprA₀, hσcapA₀_mem, hσcapA₀_regime, hσcapA₀_typing, hσcapA₀_rec⟩ :=
            closureCapturedVarsRegime_peClosure_extract hetyp1
              (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
          have ⟨σcapA₁, pbodyA₁, htoPExprA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
            closureCapturedVarsRegime_peClosure_extract hetyp1
              (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
          -- body₀ = PExpr.toExpr pbodyA₀ (and similarly for body₁)
          have hbody₀_eq : PExpr.toExpr pbodyA₀ = body₀ :=
            PExpr_toExpr_of_toPExpr?_some body₀ pbodyA₀ htoPExprA₀
          have hbody₁_eq : PExpr.toExpr pbodyA₁ = body₁ :=
            PExpr_toExpr_of_toPExpr?_some body₁ pbodyA₁ htoPExprA₁
          -- Get body typing for σcapA₀ and σcapA₁ from applyPFnTClosure
          rcases applyPFnTClosure_regular_inv_of_mapM_mem
              ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
              x₀ pbodyA₀ σcapA₀ hmap hσcapA₀_mem with
            ⟨fuelBodyA₀, firstA₀, result3A₀, happlyA₀, hfuelA₀,
              htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
          rcases applyPFnTClosure_regular_inv_of_mapM_mem
              ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
              x₁ pbodyA₁ σcapA₁ hmap hσcapA₁_mem with
            ⟨fuelBodyA₁, firstA₁, result3A₁, happlyA₁, hfuelA₁,
              htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
          -- Get membership in first :: rest (for join transport)
          have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
            rcases list_mapM_ok_mem_input_exists_output
                (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                  ctxᵢ result1 fuel')
                hmap hσcapA₀_mem with ⟨y, hy_mem, hy_eq⟩
            rw [← heq_results]
            have : y = firstA₀ := Except.ok.inj (hy_eq.symm.trans happlyA₀)
            rwa [this] at hy_mem
          have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
            rcases list_mapM_ok_mem_input_exists_output
                (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                  ctxᵢ result1 fuel')
                hmap hσcapA₁_mem with ⟨y, hy_mem, hy_eq⟩
            rw [← heq_results]
            have : y = firstA₁ := Except.ok.inj (hy_eq.symm.trans happlyA₁)
            rwa [this] at hy_mem
          -- Define body contexts (parrow: pc has ctxᵢ.pc before p1, pureCtx := true)
          let bodyCtxA₀ : TypeContext :=
            { ctxᵢ with
              pc := joinPoison p (joinPoison ctxᵢ.pc p1)
              memEnv := result1.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
              tagEnv := result1.tagEnv'
              pureCtx := true
              nextTag := result1.nextTag'
              nextLoc := result1.nextLoc'
              regime := result1.regime' }
          let bodyCtxA₁ : TypeContext :=
            { ctxᵢ with
              pc := joinPoison p (joinPoison ctxᵢ.pc p1)
              memEnv := result1.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
              tagEnv := result1.tagEnv'
              pureCtx := true
              nextTag := result1.nextTag'
              nextLoc := result1.nextLoc'
              regime := result1.regime' }
          -- Common setup
          have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
          have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
          have h_mono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
            regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
          -- Fuel bounds
          have hfuel_ltA₀ : fuelBodyA₀ < Nat.succ (Nat.succ fuel') := by
            have : fuelBodyA₀ < fuel' := by rw [hfuelA₀]; exact Nat.lt_succ_self _
            exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          have hfuel_ltA₁ : fuelBodyA₁ < Nat.succ (Nat.succ fuel') := by
            have : fuelBodyA₁ < fuel' := by rw [hfuelA₁]; exact Nat.lt_succ_self _
            exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          -- ===== Run 0: unary body witness =====
          have hTmBodyA₀ : wfTagMeaningCtx tm bodyCtxA₀ := by
            have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
              QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (hqt2 ▸ _hresTm2) rfl rfl
            simpa [bodyCtxA₀, ctxAfter] using
              wfTagMeaningCtx_pclosure_body
                (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                (p := p) (tcls := tcls)
                (xFun := x₀) (pbody := pbodyA₀) (σcap := σcapA₀)
                (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                _hTm1 hresTm1' hetyp1 hσcapA₀_mem hargTm
          have htcBodyA₀' : typecheck bodyCtxA₀ (PExpr.toExpr pbodyA₀) fuelBodyA₀ = .ok result3A₀ := by
            simpa [bodyCtxA₀, typecheck] using htc_bodyA₀
          -- Rewrite body typecheck target to body₀ for IH compatibility
          have htcBodyA₀_body₀ : typecheck bodyCtxA₀ body₀ fuelBodyA₀ = .ok result3A₀ := by
            rw [← hbody₀_eq]; exact htcBodyA₀'
          have hwfBodyCtxA₀ : wfTypeContext bodyCtxA₀ := by
            simp only [bodyCtxA₀, wfTypeContext]
            have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
              (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
            have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            exact ⟨hwf1.1,
              varEnvRefLocsBounded_update
                (varEnvRefLocsBounded_ofCaptured
                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)))
                (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
              varEnvClosuresCapturedRefLocsBounded_update
                (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem))
                (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
          have hric_bodyA₀ :
              runtimeInstantiatesCtx bodyCtxA₀ cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
            have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
              simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
            let ctxCapBaseA₀ : TypeContext :=
              { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₀ }
            have hric_cap_baseA₀ :
                runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₀ result1)
                  cf₀.memory env₀ θ₀1 := by
              constructor
              · intro l a hlookup
                exact hric₀1.1 l a hlookup
              · intro y qt hlookup
                have hlookup_list :=
                  list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                rcases hσcapA₀_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hlookup_list hv⟩
            have hric_bodyA₀' :
                runtimeInstantiatesCtx
                  { ctxCapBaseA₀ with
                    memEnv := result1.memEnv'
                    tagEnv := result1.tagEnv'
                    nextLoc := result1.nextLoc'
                    nextTag := result1.nextTag'
                    regime := result1.regime'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
              runtimeInstantiatesCtx_closure_body
                (ctx := ctxCapBaseA₀) (result2 := result1) (x := x₀)
                (tenv := σcapA₀)
                (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (argVal := v₂₀) (μ := cf₀.memory) (ρ := env₀) (θ := θ₀1)
                hric_cap_baseA₀ harg₀_typed
                (fun y qt hlookup => by
                  have hl := list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                  rcases hσcapA₀_typing.2.1 y qt hl with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hl hv⟩)
            simpa [runtimeInstantiatesCtx, bodyCtxA₀, ctxCapBaseA₀, ctxAfter]
              using hric_bodyA₀'
          have htagR_bodyA₀ : regimeConsistentWithCtx bodyCtxA₀ := by
            simpa [bodyCtxA₀, ctxAfter, regimeConsistentWithCtx] using htagR1
          have hcwr_bodyA₀ :
              consistentWithRegime predSat bodyCtxA₀.regime bodyCtxA₀
                cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
            have hlocs_src₀ :
                ∀ l qt k,
                  result1.memEnv'.lookup l = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  locsRegime predSat result1.regime' cf₀.memory θ₀1 (l, qt) :=
              fun l qt k hlookup hguard hRdef =>
                hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
            have hvars_capA₀ :
                ∀ x qt k,
                  (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₀.memory env₀ (x, qt) :=
              fun x qt k hlookup hguard hRdef =>
                hσcapA₀_regime x qt k
                  (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hguard hRdef
            have hvars_argA₀ :
                ∀ k,
                  qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₀.memory
                    (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
              intro k hguard hRdef
              have hvalc_arg_e2 :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                valueConsistentWithRegime_transport_pred
                  (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                  (qt := result2.qualType)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                  (by simp [hqt2]) (hetyp := by simp [hqt2])
                  (by simpa [ctxAfter] using _hvalc₂₀)
              have hvalc_arg_e1 :=
                valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
              exact
                varsRegime_transport_predHolds
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                    c₂'₀.memory cf₀.memory)
                  (varsRegime_of_valueConsistentWithRegime_active
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                    (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (v := v₂₀) (k := k)
                    (by simp [VarEnv.update, VarEnv.lookup])
                    hguard hRdef hvalc_arg_e1)
            have h_cap_cvcrA₀ :
                ∀ x qt v,
                  (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                  env₀.lookup x = some v →
                  closureCapturedVarsRegime predSat result1.regime' qt
                    cf₀.memory θ₀1 v :=
              fun x qt v hlookup hv =>
                hσcapA₀_rec x qt v
                  (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hv
            exact
              consistentWithRegime_closure_body_start
                predSat ctxᵢ result1
                σcapA₀ x₀ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                cf₀.memory θ₀1 env₀ v₂₀
                hlocs_src₀ hvars_capA₀ hvars_argA₀ h_cap_cvcrA₀
                (closureCapturedVarsRegime_transport_μ_θ
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                    c₂'₀.memory cf₀.memory)
                  hθext₀1.1
                  (closureCapturedVarsRegime_monotone h_mono1
                    (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                      (valueConsistentWithRegime_closureCapturedVarsRegime
                        _hvalc₂₀))))
          have hwfcfg_body_initA₀ :
              wfConfig
                { memory := cf₀.memory
                  varEnv := env₀.update x₀ v₂₀
                  nextAddr := cf₀.nextAddr
                  pureMode := true } := by
            have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
              (wfConfig_preserved e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
            have hnext₂_to₁ : c₂'₀.nextAddr ≤ cf₀.nextAddr :=
              terminatesTo_nextAddr_mono e1 c₂'₀ cf₀
                (Value.peClosure x₀ body₀ env₀) ht₀_e1
            have hv₂₀_wf : wfValue cf₀.nextAddr v₂₀ :=
              wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
            have henv₀_wf : wfVarEnv cf₀.nextAddr env₀ := by
              cases (wfConfig_preserved e1 _ cf₀ _ ht₀_e1 hwfcf₂₀).2 with
              | peClosure _ _ _ henv => exact henv
            constructor
            · intro a ha; exact hwfcf₁₀.1 a ha
            · simpa [VarEnv.update] using wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf
          -- The body terminatesTo uses body₀, but init config has pureMode := true
          have ht₀_body' : terminatesTo body₀
              { memory := cf₀.memory, varEnv := env₀.update x₀ v₂₀,
                nextAddr := cf₀.nextAddr, pureMode := true } evalCfg₀ o₀ := ht₀_body
          have hSingle_bodyA₀ :=
            singleIH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀ result3A₀ htcBodyA₀_body₀
          have hpc_bodyA₀_run : bodyCtxA₀.pc = true := by
            simp [bodyCtxA₀, joinPoison] at h_p1p ⊢
            cases p1 <;> cases p <;> simp at h_p1p ⊢
          have hsr₀ :=
            hSingle_bodyA₀ hpredlaws hTmBodyA₀
              cf₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
              hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀
              hcwr_bodyA₀ cf₀.nextAddr true hwfcfg_body_initA₀ ht₀_body'
              hpc_bodyA₀_run
          rcases hsr₀ with
            ⟨θ₀_body, hθext₀_body, hv₀_body_typed,
              hric_bodyA₀_final, hcwr_bodyA₀_final, hvalc_bodyA₀, hpres₀, _hfresh₀_body⟩
          -- ===== Run 1: unary body witness =====
          have hTmBodyA₁ : wfTagMeaningCtx tm bodyCtxA₁ := by
            have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
              QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (hqt2 ▸ _hresTm2) rfl rfl
            simpa [bodyCtxA₁, ctxAfter] using
              wfTagMeaningCtx_pclosure_body
                (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                (p := p) (tcls := tcls)
                (xFun := x₁) (pbody := pbodyA₁) (σcap := σcapA₁)
                (xArg := x₁) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                _hTm1 hresTm1' hetyp1 hσcapA₁_mem hargTm
          have htcBodyA₁' : typecheck bodyCtxA₁ (PExpr.toExpr pbodyA₁) fuelBodyA₁ = .ok result3A₁ := by
            simpa [bodyCtxA₁, typecheck] using htc_bodyA₁
          have htcBodyA₁_body₁ : typecheck bodyCtxA₁ body₁ fuelBodyA₁ = .ok result3A₁ := by
            rw [← hbody₁_eq]; exact htcBodyA₁'
          have hwfBodyCtxA₁ : wfTypeContext bodyCtxA₁ := by
            simp only [bodyCtxA₁, wfTypeContext]
            have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
              (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
            have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            exact ⟨hwf1.1,
              varEnvRefLocsBounded_update
                (varEnvRefLocsBounded_ofCaptured
                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))))
                (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
              varEnvClosuresCapturedRefLocsBounded_update
                (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption)))
                (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
          have hric_bodyA₁ :
              runtimeInstantiatesCtx bodyCtxA₁ cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
            have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
              simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
            let ctxCapBaseA₁ : TypeContext :=
              { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₁ }
            have hric_cap_baseA₁ :
                runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₁ result1)
                  cf₁.memory env₁ θ₁1 := by
              constructor
              · intro l a hlookup
                exact hric₁1.1 l a hlookup
              · intro y qt hlookup
                have hlookup_list :=
                  list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                rcases hσcapA₁_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hlookup_list hv⟩
            have hric_bodyA₁' :
                runtimeInstantiatesCtx
                  { ctxCapBaseA₁ with
                    memEnv := result1.memEnv'
                    tagEnv := result1.tagEnv'
                    nextLoc := result1.nextLoc'
                    nextTag := result1.nextTag'
                    regime := result1.regime'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 :=
              runtimeInstantiatesCtx_closure_body
                (ctx := ctxCapBaseA₁) (result2 := result1) (x := x₁)
                (tenv := σcapA₁)
                (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (argVal := v₂₁) (μ := cf₁.memory) (ρ := env₁) (θ := θ₁1)
                hric_cap_baseA₁ harg₁_typed
                (fun y qt hlookup => by
                  have hl := list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                  rcases hσcapA₁_typing.2.1 y qt hl with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hl hv⟩)
            simpa [runtimeInstantiatesCtx, bodyCtxA₁, ctxCapBaseA₁, ctxAfter]
              using hric_bodyA₁'
          have htagR_bodyA₁ : regimeConsistentWithCtx bodyCtxA₁ := by
            simpa [bodyCtxA₁, ctxAfter, regimeConsistentWithCtx] using htagR1
          have hcwr_bodyA₁ :
              consistentWithRegime predSat bodyCtxA₁.regime bodyCtxA₁
                cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
            have hlocs_src₁ :
                ∀ l qt k,
                  result1.memEnv'.lookup l = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  locsRegime predSat result1.regime' cf₁.memory θ₁1 (l, qt) :=
              fun l qt k hlookup hguard hRdef =>
                hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
            have hvars_capA₁ :
                ∀ x qt k,
                  (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₁.memory env₁ (x, qt) :=
              fun x qt k hlookup hguard hRdef =>
                hσcapA₁_regime x qt k
                  (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hguard hRdef
            have hvars_argA₁ :
                ∀ k,
                  qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₁.memory
                    (env₁.update x₁ v₂₁) (x₁, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
              intro k hguard hRdef
              have hvalc_arg_e2 :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                valueConsistentWithRegime_transport_pred
                  (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                  (qt := result2.qualType)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                  (by simp [hqt2]) (hetyp := by simp [hqt2])
                  (by simpa [ctxAfter] using _hvalc₂₁)
              have hvalc_arg_e1 :=
                valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
              exact
                varsRegime_transport_predHolds
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                    c₂'₁.memory cf₁.memory)
                  (varsRegime_of_valueConsistentWithRegime_active
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₁.memory) (ρ := env₁.update x₁ v₂₁)
                    (x := x₁) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (v := v₂₁) (k := k)
                    (by simp [VarEnv.update, VarEnv.lookup])
                    hguard hRdef hvalc_arg_e1)
            have h_cap_cvcrA₁ :
                ∀ x qt v,
                  (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                  env₁.lookup x = some v →
                  closureCapturedVarsRegime predSat result1.regime' qt
                    cf₁.memory θ₁1 v :=
              fun x qt v hlookup hv =>
                hσcapA₁_rec x qt v
                  (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hv
            exact
              consistentWithRegime_closure_body_start
                predSat ctxᵢ result1
                σcapA₁ x₁ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                cf₁.memory θ₁1 env₁ v₂₁
                hlocs_src₁ hvars_capA₁ hvars_argA₁ h_cap_cvcrA₁
                (closureCapturedVarsRegime_transport_μ_θ
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                    c₂'₁.memory cf₁.memory)
                  hθext₁1.1
                  (closureCapturedVarsRegime_monotone h_mono1
                    (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                      (valueConsistentWithRegime_closureCapturedVarsRegime
                        _hvalc₂₁))))
          have hwfcfg_body_initA₁ :
              wfConfig
                { memory := cf₁.memory
                  varEnv := env₁.update x₁ v₂₁
                  nextAddr := cf₁.nextAddr
                  pureMode := true } := by
            have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
              (wfConfig_preserved e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
            have hnext₂_to₁ : c₂'₁.nextAddr ≤ cf₁.nextAddr :=
              terminatesTo_nextAddr_mono e1 c₂'₁ cf₁
                (Value.peClosure x₁ body₁ env₁) ht₁_e1
            have hv₂₁_wf : wfValue cf₁.nextAddr v₂₁ :=
              wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
            have henv₁_wf : wfVarEnv cf₁.nextAddr env₁ := by
              cases (wfConfig_preserved e1 _ cf₁ _ ht₁_e1 hwfcf₂₁).2 with
              | peClosure _ _ _ henv => exact henv
            constructor
            · intro a ha; exact hwfcf₁₁.1 a ha
            · simpa [VarEnv.update] using wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf
          have ht₁_body' : terminatesTo body₁
              { memory := cf₁.memory, varEnv := env₁.update x₁ v₂₁,
                nextAddr := cf₁.nextAddr, pureMode := true } evalCfg₁ o₁ := ht₁_body
          have hSingle_bodyA₁ :=
            singleIH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁ result3A₁ htcBodyA₁_body₁
          have hpc_bodyA₁_run : bodyCtxA₁.pc = true := by
            simp [bodyCtxA₁, joinPoison] at h_p1p ⊢
            cases p1 <;> cases p <;> simp at h_p1p ⊢
          have hsr₁ :=
            hSingle_bodyA₁ hpredlaws hTmBodyA₁
              cf₁.memory (env₁.update x₁ v₂₁) θ₁1 evalCfg₁ o₁
              hθ₁1wf hwfBodyCtxA₁ hric_bodyA₁ htagR_bodyA₁
              hcwr_bodyA₁ cf₁.nextAddr true hwfcfg_body_initA₁ ht₁_body'
              hpc_bodyA₁_run
          rcases hsr₁ with
            ⟨θ₁_body, hθext₁_body, hv₁_body_typed,
              hric_bodyA₁_final, hcwr_bodyA₁_final, hvalc_bodyA₁, hpres₁, _hfresh₁_body⟩
          -- ===== Transport to joined result and pack =====
          -- etyp agreement: body result etyp = firstA etyp (normalizeAppResultByProvenance preserves etyp)
          have hfirstA₀_etyp : firstA₀.qualType.etyp = result3A₀.qualType.etyp := by
            rw [hfirstA₀_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
          have hfirstA₁_etyp : firstA₁.qualType.etyp = result3A₁.qualType.etyp := by
            rw [hfirstA₁_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
          -- regime monotonicity from result1 to body results
          have h_mono_bodyA₀ : Regime.monotoneStep bodyCtxA₀.regime result3A₀.regime' :=
            regime_monotone bodyCtxA₀ (PExpr.toExpr pbodyA₀) fuelBodyA₀ result3A₀ htcBodyA₀'
          have h_mono_bodyA₁ : Regime.monotoneStep bodyCtxA₁.regime result3A₁.regime' :=
            regime_monotone bodyCtxA₁ (PExpr.toExpr pbodyA₁) fuelBodyA₁ result3A₁ htcBodyA₁'
          have hres1_to_firstA₀_mono :
              Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                (ctxAfter ctxᵢ firstA₀).regime := by
            simpa [bodyCtxA₀, ctxAfter, hfirstA₀_eq] using h_mono_bodyA₀
          have hres1_to_firstA₁_mono :
              Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                (ctxAfter ctxᵢ firstA₁).regime := by
            simpa [bodyCtxA₁, ctxAfter, hfirstA₁_eq] using h_mono_bodyA₁
          -- lookup-back for regime: firstA₀.regime' -> result1.regime'
          have hlookup_back_res1_to_A₀ :
              ∀ k b,
                (ctxAfter ctxᵢ firstA₀).regime.lookup? k = some b →
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
            intro k b hk_src
            have hRdef_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k ≠ none := by
              intro hnone; rw [hk_src] at hnone; contradiction
            have hRdef_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
              hres1_to_firstA₀_mono.2 k hRdef_src
            cases hk_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
            | none => exact False.elim (hRdef_res1 hk_res1)
            | some b1 =>
                rcases hres1_to_firstA₀_mono.1 k b1 hk_res1 with hk_src' | hnone_src
                · have : some b1 = some b := hk_src'.symm.trans hk_src
                  simp [Option.some.inj this]
                · rw [hnone_src] at hk_src; cases hk_src
          have hlookup_back_res1_to_A₁ :
              ∀ k b,
                (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
            intro k b hk_src
            have hRdef_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k ≠ none := by
              intro hnone; rw [hk_src] at hnone; contradiction
            have hRdef_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
              hres1_to_firstA₁_mono.2 k hRdef_src
            cases hk_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
            | none => exact False.elim (hRdef_res1 hk_res1)
            | some b1 =>
                rcases hres1_to_firstA₁_mono.1 k b1 hk_res1 with hk_src' | hnone_src
                · have : some b1 = some b := hk_src'.symm.trans hk_src
                  simp [Option.some.inj this]
                · rw [hnone_src] at hk_src; cases hk_src
          -- Memory/varEnv equalities (pure closure: cf = c₁ after subst, body memory preserved in pure mode)
          -- In pure mode, the body cannot allocate or modify memory, so evalCfg.memory = bodyInit.memory = cf.memory
          have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
            obtain ⟨fuel_b₀, verbose_b₀, hbeval_b₀⟩ := ht₀_body'
            exact (beval_pure_memory_eq body₀ fuel_b₀ _ evalCfg₀ o₀ verbose_b₀
              pbodyA₀
              htoPExprA₀ rfl hbeval_b₀).symm
          have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
            obtain ⟨fuel_b₁, verbose_b₁, hbeval_b₁⟩ := ht₁_body'
            exact (beval_pure_memory_eq body₁ fuel_b₁ _ evalCfg₁ o₁ verbose_b₁
              pbodyA₁
              htoPExprA₁ rfl hbeval_b₁).symm
          -- predSat compat for memory transport (trivial after hmem_eq, but stated for uniformity with arrow)
          have hpred_compat₀ :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cf₀.memory v' ↔
                  qtypPredHolds predSat qt' cf₀.memory v' :=
            fun _ _ => Iff.rfl
          have hpred_compat₁ :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cf₁.memory v' ↔
                  qtypPredHolds predSat qt' cf₁.memory v' :=
            fun _ _ => Iff.rfl
          exact ⟨joinTypeResults_QTypRespectsTagMeaning tm ctxᵢ first rest res
              h_join h_first_qtm h_rest_qtm,
            θ₀_body, θ₁_body,
            wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 hθext₀_body),
            wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 hθext₁_body),
            -- valueHasETyp run 0
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
              (θ := θ₀_body) (v := o₀)
              h_join hfirstA₀_mem' (hfirstA₀_etyp ▸ hv₀_body_typed),
            -- valueHasETyp run 1
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
              (θ := θ₁_body) (v := o₁)
              h_join hfirstA₁_mem' (hfirstA₁_etyp ▸ hv₁_body_typed),
            -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
            join_transport_wfTagMeaningCtx tm ctxᵢ first rest res h_join h_first_tm,
            -- wfTypeContext (ctxAfter ctxᵢ res)
            join_transport_wfTypeContext ctxᵢ first rest res h_join h_mem_join
              (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                (Nat.le_trans
                  (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                    (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                  (mapM_applyPFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel' tcls results hmap first hfirst_in_results)))
              (fun r hr => hresults_wf r (heq_results ▸ List.mem_cons_of_mem first hr)),
            -- TagBoundedCtx (ctxAfter ctxᵢ res)
            typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded,
            -- wfConfig cf₀ (after subst heq_cfg₀, cf₀ = c₁₀)
            hwfcf₁₀,
            -- wfConfig cf₁ (after subst heq_cfg₁, cf₁ = c₁₁)
            hwfcf₁₁,
            -- runtimeInstantiatesCtx run 0
            by
              have hmem_to_res₀ :
                  ∀ l, firstA₀.memEnv'.contains l → res.memEnv'.contains l :=
                joinTypeResults_mem_contains_of_member
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest)
                  (res := res) h_join hfirstA₀_mem'
              constructor
              · intro l a hθ
                have hloc := hric_bodyA₀_final.1 l a hθ
                rcases hloc with ⟨hcontains_body, hmem_contains⟩
                have hcontains_src : firstA₀.memEnv'.contains l := by
                  simpa [ctxAfter, hfirstA₀_eq] using hcontains_body
                exact ⟨hmem_to_res₀ l hcontains_src, by simpa [hmem₀_eq] using hmem_contains⟩
              · intro x qt hlookup
                have hlookup_ctx :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                exact ⟨v, hlookup_v,
                  valueHasETyp_extends hθext₀_body.1 hv_typ⟩,
            -- runtimeInstantiatesCtx run 1
            by
              have hmem_to_res₁ :
                  ∀ l, firstA₁.memEnv'.contains l → res.memEnv'.contains l :=
                joinTypeResults_mem_contains_of_member
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest)
                  (res := res) h_join hfirstA₁_mem'
              constructor
              · intro l a hθ
                have hloc := hric_bodyA₁_final.1 l a hθ
                rcases hloc with ⟨hcontains_body, hmem_contains⟩
                have hcontains_src : firstA₁.memEnv'.contains l := by
                  simpa [ctxAfter, hfirstA₁_eq] using hcontains_body
                exact ⟨hmem_to_res₁ l hcontains_src, by simpa [hmem₁_eq] using hmem_contains⟩
              · intro x qt hlookup
                have hlookup_ctx :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                exact ⟨v, hlookup_v,
                  valueHasETyp_extends hθext₁_body.1 hv_typ⟩,
            -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
            join_transport_regimeConsistentWithCtx ctxᵢ first rest res h_join
              h_tag_join h_first_regime,
            -- consistentWithRegime run 0
            by
              have hcwr_src₀ :
                  consistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                    (ctxAfter ctxᵢ firstA₀) cf₀.memory cf₀.varEnv θ₀_body := by
                refine ⟨?_, ?_, ?_⟩
                · intro l qt k hlookup hguard hRdef
                  have hlookup_body :
                      (ctxAfter bodyCtxA₀ result3A₀).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstA₀_eq] using hlookup
                  have hguard_body : qtypGuardTag qt = some k := by
                    simpa [ctxAfter, hfirstA₀_eq] using hguard
                  have hRdef_body :
                      (ctxAfter bodyCtxA₀ result3A₀).regime.lookup? k ≠ none := by
                    simpa [ctxAfter, hfirstA₀_eq] using hRdef
                  simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using
                    hcwr_bodyA₀_final.1 l qt k hlookup_body hguard_body hRdef_body
                · intro x qt k hlookup hguard hRdef
                  cases hk_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k with
                  | none => exact False.elim (hRdef hk_src)
                  | some b =>
                      have hRdef_res1 :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                        intro hnone
                        have hk_back := hlookup_back_res1_to_A₀ k b hk_src
                        rw [hk_back] at hnone; contradiction
                      have hlookup_res1_ctx :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                            some qt := by
                        simpa [ctxAfter] using hlookup
                      have hvar_res1 :=
                        hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                      have hvar_res1_mem :=
                        varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                      exact
                        varsRegime_transport_active_lookup_back
                          (predSat := predSat)
                          (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                          (R' := (ctxAfter ctxᵢ firstA₀).regime)
                          (μ := cf₀.memory) (ρ := cf₀.varEnv) (entry := (x, qt))
                          hlookup_back_res1_to_A₀ hguard hk_src hvar_res1_mem
                · intro x qt v hlookup hlookup_v
                  have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                    hlookup_v
                  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ hθext₀_body.1
                    (closureCapturedVarsRegime_transport_lookup_back
                      hlookup_back_res1_to_A₀ hcvcr)
              exact
                joinTypeResults_transport_consistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                  h_join hfirstA₀_mem' hcwr_src₀,
            -- consistentWithRegime run 1
            by
              have hcwr_src₁ :
                  consistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                    (ctxAfter ctxᵢ firstA₁) cf₁.memory cf₁.varEnv θ₁_body := by
                refine ⟨?_, ?_, ?_⟩
                · intro l qt k hlookup hguard hRdef
                  have hlookup_body :
                      (ctxAfter bodyCtxA₁ result3A₁).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstA₁_eq] using hlookup
                  have hguard_body : qtypGuardTag qt = some k := by
                    simpa [ctxAfter, hfirstA₁_eq] using hguard
                  have hRdef_body :
                      (ctxAfter bodyCtxA₁ result3A₁).regime.lookup? k ≠ none := by
                    simpa [ctxAfter, hfirstA₁_eq] using hRdef
                  simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using
                    hcwr_bodyA₁_final.1 l qt k hlookup_body hguard_body hRdef_body
                · intro x qt k hlookup hguard hRdef
                  cases hk_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k with
                  | none => exact False.elim (hRdef hk_src)
                  | some b =>
                      have hRdef_res1 :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                        intro hnone
                        have hk_back := hlookup_back_res1_to_A₁ k b hk_src
                        rw [hk_back] at hnone; contradiction
                      have hlookup_res1_ctx :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                            some qt := by
                        simpa [ctxAfter] using hlookup
                      have hvar_res1 :=
                        hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                      have hvar_res1_mem :=
                        varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                      exact
                        varsRegime_transport_active_lookup_back
                          (predSat := predSat)
                          (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                          (R' := (ctxAfter ctxᵢ firstA₁).regime)
                          (μ := cf₁.memory) (ρ := cf₁.varEnv) (entry := (x, qt))
                          hlookup_back_res1_to_A₁ hguard hk_src hvar_res1_mem
                · intro x qt v hlookup hlookup_v
                  have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                    hlookup_v
                  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ hθext₁_body.1
                    (closureCapturedVarsRegime_transport_lookup_back
                      hlookup_back_res1_to_A₁ hcvcr)
              exact
                joinTypeResults_transport_consistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                  h_join hfirstA₁_mem' hcwr_src₁,
            -- agreeOnClean for ¬qtypCleanUnder (p1=true, parrow, different closure bodies)
            by
              -- Regime monotonicity: result1.regime' → res.regime' (through the join)
              have h_all_members_mono :
                  ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                apply List.mapM_Except_preserves_property
                  (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  (P := fun x => Regime.monotoneStep result1.regime' x.regime')
                · intro tcl result _htcl
                  exact applyPFnTClosure_regime_mono tcl ctxᵢ st1 st2 p p1 etyp2 p2 pred2
                    result1 result fuel'
                    (fun m _hlt e ctx' res' htc =>
                      by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                    _htcl
                · rw [← heq_results]; exact hmap
              have h_mono_res : Regime.monotoneStep result1.regime' res.regime' :=
                joinTypeResults_regime_monotone ctxᵢ first rest res result1.regime'
                  (h_all_members_mono first (by simp))
                  (fun x hx => h_all_members_mono x (List.mem_cons_of_mem _ hx))
                  h_join
              -- Clean transfer: qtypCleanUnder res → qtypCleanUnder result1
              have h_clean_res_to_pre :
                  ∀ qt, qtypCleanUnder res.regime' qt →
                    qtypCleanUnder result1.regime' qt :=
                fun qt hc => cleanUnder_of_monotone h_mono_res hc
              constructor
              · -- Locations conjunct
                intro l qt hlookup hclean
                have hclean_res : qtypCleanUnder res.regime' qt := by
                  simpa [ctxAfter] using hclean
                have hlookup_res : res.memEnv'.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup
                -- Case split: is l inherited from result1.memEnv'?
                cases hlookup_body : (result1.memEnv'.lookup l) with
                | none =>
                  -- l is NOT in result1.memEnv' but IS in res.memEnv'. Contradiction:
                  -- every alternative's memEnv' ⊆ result1.memEnv' (pure bodies can't grow memEnv)
                  exfalso
                  have hcontains_res :=
                    memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
                  have hcontains_l : result1.memEnv'.contains l := by
                    rcases joinTypeResults_mem_contains_head_or_rest ctxᵢ first rest res
                        h_join l hcontains_res with hfirst | ⟨r, hr, hrl⟩
                    · rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          hmap (show first ∈ results by rw [heq_results]; exact List.Mem.head rest)
                        with ⟨tcl, _, happly⟩
                      exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                        pred2 result1 fuel' tcl first happly l hfirst
                    · rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          hmap (by rw [heq_results]; exact List.mem_cons_of_mem first hr)
                        with ⟨tcl, _, happly⟩
                      exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                        pred2 result1 fuel' tcl r happly l hrl
                  rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_l
                    with ⟨_, hlookup'⟩
                  exact Option.noConfusion (hlookup_body ▸ hlookup')
                | some qt' =>
                  -- Inherited location: l is in result1.memEnv' with type qt'
                  have hetyp_qt : qt.etyp = ETyp.int :=
                    memEnv_lookup_etyp_int res.memEnv' l qt hlookup_res
                  have hetyp_qt' : qt'.etyp = ETyp.int :=
                    memEnv_lookup_etyp_int result1.memEnv' l qt' hlookup_body
                  have hfirstA₀_lookup :=
                    applyPFnTClosure_preserves_memEnv_lookup ctxᵢ st1 st2 p p1
                      etyp2 p2 pred2 result1 fuel'
                      (PFnTClosure.regular x₀ pbodyA₀ σcapA₀) firstA₀
                      happlyA₀ l qt' hlookup_body
                  have hclean_member :
                      qtypCleanUnder (ctxAfter ctxᵢ firstA₀).regime qt' := by
                    exact
                      joinTypeResults_lookup_member_clean_compat ctxᵢ first firstA₀
                        rest res h_join hfirstA₀_mem' l qt qt'
                        (by simpa [ctxAfter] using hlookup_res)
                        (by simpa [ctxAfter] using hclean_res)
                        (by simpa [ctxAfter] using hfirstA₀_lookup)
                  -- qt' is clean under result1.regime' (needed for hagree1 and hpres)
                  -- Proof: applyPFnTClosure preserves memEnv values for PExpr bodies,
                  -- so firstA₀.memEnv'.lookup l = some qt'. Then
                  -- joinTypeResults_lookup_member_clean_compat gives cleanness at
                  -- firstA₀.regime', and backward monotonicity gives result1.regime'.
                  have hclean_pre' : qtypCleanUnder result1.regime' qt' := by
                    exact cleanUnder_of_monotone hres1_to_firstA₀_mono hclean_member
                  have hfirstA₁_lookup :=
                    applyPFnTClosure_preserves_memEnv_lookup ctxᵢ st1 st2 p p1
                      etyp2 p2 pred2 result1 fuel'
                      (PFnTClosure.regular x₁ pbodyA₁ σcapA₁) firstA₁
                      happlyA₁ l qt' hlookup_body
                  have hclean_member₁ :
                      qtypCleanUnder (ctxAfter ctxᵢ firstA₁).regime qt' := by
                    exact
                      joinTypeResults_lookup_member_clean_compat ctxᵢ first firstA₁
                        rest res h_join hfirstA₁_mem' l qt qt'
                        (by simpa [ctxAfter] using hlookup_res)
                        (by simpa [ctxAfter] using hclean_res)
                        (by simpa [ctxAfter] using hfirstA₁_lookup)
                  -- Pre-body agreement from hagree1
                  have hlookup_pre :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).memEnv.lookup l = some qt' := by
                    simpa [ctxAfter] using hlookup_body
                  have hloc_pre := hagree1.1 l qt' hlookup_pre hclean_pre'
                  -- Per-run preservation
                  rcases hpres₀ with ⟨hpres₀_fn⟩
                  have hpres_l₀ := hpres₀_fn l qt' qt'
                    (by simp only [bodyCtxA₀]; exact hlookup_body)
                    (by simpa [hfirstA₀_eq] using hfirstA₀_lookup)
                    (by simpa [ctxAfter, hfirstA₀_eq] using hclean_member)
                  rcases hpres₁ with ⟨hpres₁_fn⟩
                  have hpres_l₁ := hpres₁_fn l qt' qt'
                    (by simp only [bodyCtxA₁]; exact hlookup_body)
                    (by simpa [hfirstA₁_eq] using hfirstA₁_lookup)
                    (by simpa [ctxAfter, hfirstA₁_eq] using hclean_member₁)
                  -- Case split on pre-body loc agreement × run-0 preservation
                  cases hloc_pre with
                  | both_unrealized _ _ hθ₀_none hθ₁_none =>
                    cases hpres_l₀ with
                    | both_unrealized _ hout₀ =>
                      cases hpres_l₁ with
                      | both_unrealized _ hout₁ =>
                        exact agreeLocUnder.both_unrealized l qt hout₀ hout₁
                      | preserve_value a n hin _ _ _ =>
                        exact absurd (hθ₁_none ▸ hin) (by exact Option.noConfusion)
                    | preserve_value a n hin _ _ _ =>
                      exact absurd (hθ₀_none ▸ hin) (by exact Option.noConfusion)
                  | agree_values _ _ a₀ a₁ n₀ n₁ hθ₀_in hθ₁_in hm₀_in hm₁_in hagree_val =>
                    cases hpres_l₀ with
                    | both_unrealized hin₀ _ =>
                      exact absurd (hin₀ ▸ hθ₀_in) (by exact Option.noConfusion)
                    | preserve_value a₀' n₀' hθ₀_in' hm₀_in' hθ₀_out hm₀_out =>
                      cases hpres_l₁ with
                      | both_unrealized hin₁ _ =>
                        exact absurd (hin₁ ▸ hθ₁_in) (by exact Option.noConfusion)
                      | preserve_value a₁' n₁' hθ₁_in' hm₁_in' hθ₁_out hm₁_out =>
                        -- Equate addresses via unique θ lookups
                        have ha₀ : a₀' = a₀ :=
                          Option.some.inj (hθ₀_in'.symm.trans hθ₀_in)
                        have ha₁ : a₁' = a₁ :=
                          Option.some.inj (hθ₁_in'.symm.trans hθ₁_in)
                        -- Equate values via unique memory lookups
                        have hn₀ : n₀' = n₀ := by
                          rw [ha₀] at hm₀_in'
                          exact Option.some.inj (hm₀_in'.symm.trans hm₀_in)
                        have hn₁ : n₁' = n₁ := by
                          rw [ha₁] at hm₁_in'
                          exact Option.some.inj (hm₁_in'.symm.trans hm₁_in)
                        -- Extract pre-body value equality (clean ints must agree)
                        have heq_pre : n₀ = n₁ := by
                          cases hagree_val with
                          | clean_eq_nonref_nonarrow _ _ _ hEq =>
                            exact Value.num.inj hEq
                          | withPred_true_eq _ _ _ _ _ hEq =>
                            exact Value.num.inj hEq
                          | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                            cases hv₀
                          | dirty_internal_arrow _ hisA htyp₀ _ =>
                            simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                          | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                            cases hv₀
                          | dirty_internal_parrow _ hisP htyp₀ _ =>
                            simp [valueHasETyp_num_etyp htyp₀, ETyp.isParrow] at hisP
                          | clean_ref _ _ _ _ hv₀ _ _ => cases hv₀
                          | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ => cases hv₀
                        -- Post-body values equal: n₀' = n₁'
                        have heq_post : n₀' = n₁' := by
                          rw [hn₀, hn₁, heq_pre]
                        -- Construct post-body agreeLocUnder
                        -- (rewrite evalCfg.memory → cf.memory using pure-body memory preservation)
                        refine agreeLocUnder.agree_values l qt a₀' a₁'
                          n₀' n₁' hθ₀_out hθ₁_out
                          (by rw [hmem₀_eq]; exact hm₀_out)
                          (by rw [hmem₁_eq]; exact hm₁_out) ?_
                        rw [heq_post]
                        -- Build agreeValueUnder for clean qt with equal int values
                        cases hclean_res with
                        | clean hpoison =>
                          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison
                            (by simp [hetyp_qt, ETyp.isFunctionType, ETyp.isArrow,
                                      ETyp.isParrow])
                            (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                        | guard k htag hregime hnotfun =>
                          exact agreeValueUnder.withPred_true_eq k htag
                            (by simpa [ctxAfter] using hregime) hnotfun
                            (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
              · -- Variables conjunct
                intro x qt hlookup hclean
                have hlookup_pre :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                have hclean_pre : qtypCleanUnder result1.regime' qt :=
                  h_clean_res_to_pre qt (by simpa [ctxAfter] using hclean)
                cases hagree1.2 x qt hlookup_pre hclean_pre with
                | agree_values x qt v₀ v₁ hv₀_pre hv₁_pre hagree_val =>
                  refine agreeVarUnder.agree_values x qt v₀ v₁
                    hv₀_pre hv₁_pre ?_
                  -- Transport agreeValueUnder:
                  -- 1. Extend memory/θ (result1 context → body output context)
                  have hagree_ext :=
                    agreeValueUnder_clean_extends
                      hpred_compat₀ hpred_compat₁ hclean_pre hθext₀_body.1 hθext₁_body.1
                      hagree_val
                  -- 2. Change regime (result1 → res)
                  exact agreeValueUnder_clean_monotoneRegime h_mono_res
                    (by simpa [ctxAfter] using hclean) hagree_ext
                | both_none x qt hv₀_pre hv₁_pre =>
                  exact agreeVarUnder.both_none x qt
                    hv₀_pre hv₁_pre,
            -- valueConsistentWithRegime run 0
            by
              have hfirstA₀_eq_regime : firstA₀.regime' = result3A₀.regime' := by
                simp [hfirstA₀_eq]
              have hval_src₀ :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                    firstA₀.qualType cf₀.memory θ₀_body o₀ := by
                have hval_first :
                    valueConsistentWithRegime predSat (ctxAfter bodyCtxA₀ result3A₀).regime
                      (normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3A₀.qualType with
                          poison := joinPoison p1 (joinPoison p result3A₀.qualType.poison) })
                      evalCfg₀.memory θ₀_body o₀ :=
                  valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                    (predSat := predSat) (R := (ctxAfter bodyCtxA₀ result3A₀).regime)
                    (p := p) (p1 := p1) (qt := result3A₀.qualType)
                    (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) hvalc_bodyA₀
                simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using hval_first
              exact
                joinTypeResults_transport_valueConsistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                  (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                  h_join hfirstA₀_mem' hval_src₀,
            -- valueConsistentWithRegime run 1
            by
              have hval_src₁ :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                    firstA₁.qualType cf₁.memory θ₁_body o₁ := by
                have hval_first :
                    valueConsistentWithRegime predSat (ctxAfter bodyCtxA₁ result3A₁).regime
                      (normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3A₁.qualType with
                          poison := joinPoison p1 (joinPoison p result3A₁.qualType.poison) })
                      evalCfg₁.memory θ₁_body o₁ :=
                  valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                    (predSat := predSat) (R := (ctxAfter bodyCtxA₁ result3A₁).regime)
                    (p := p) (p1 := p1) (qt := result3A₁.qualType)
                    (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) hvalc_bodyA₁
                simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using hval_first
              exact
                joinTypeResults_transport_valueConsistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                  (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                  h_join hfirstA₁_mem' hval_src₁,
            -- resultAgreesIfClean (vacuously true since poison=true and pred=noPred)
            resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
        by_cases hclean1_e1 :
            qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
        · -- Clean case: shared pure-body IH (TODO: fill later)
          rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
          · rcases hshared with
              ⟨x, pbody, σcap, fuelBody, firstShared, result3Shared,
                htoPExpr, hmem, hx₀, hx₁, hbody,
                hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                happly, hfuel, htcBody, hsubBody, hfirstShared⟩
            -- Phase 1: Define bodyCtx (parrow: pureCtx := true, pc order swapped vs arrow)
            let bodyCtx : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                pureCtx := true
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
            have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
            have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
              have hfuel_lt' : fuelBody < fuel' := by
                rw [hfuel]
                exact Nat.lt_succ_self fuelBody
              exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
              have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                simpa [hqt2] using (_hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
              have hargTm' :
                  ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                    QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                    qtypGuardDesc? qt' = some (k, d) →
                    tm.lookup k = some d :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm)
                  (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hresTm2_arg rfl rfl
              exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
            have hTmBody : wfTagMeaningCtx tm bodyCtx := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
              have hTmBody' :=
                wfTagMeaningCtx_pclosure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x) (pbody := pbody) (σcap := σcap)
                  (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  _hTm1 hresTm1' hetyp1 hmem hargTm
              simp only [wfTagMeaningCtx, bodyCtx] at hTmBody' ⊢
              exact hTmBody'
            have htcBody' : typecheck bodyCtx (PExpr.toExpr pbody) fuelBody = .ok result3Shared := by
              simp only [bodyCtx, typecheck, hx₀]
              exact htcBody
            have htagBoundedBody : TagBoundedCtx bodyCtx := by
                obtain ⟨hb_tag1, ⟨hb_predV1, hb_predM1⟩, hb_clos1⟩ := _htagBounded1
                have hb_predCtx2 := (_htagBounded2 : TagBoundedCtx (ctxAfter ctxᵢ result2)).2.1
                have hb_closCtx2 := (_htagBounded2 : TagBoundedCtx (ctxAfter ctxᵢ result2)).2.2
                have hClosFull := typecheckExpr_preserves_closureCapturedBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1
                  (by simpa [typecheck] using htc1') hb_predCtx2 hb_closCtx2
                rw [hetyp1] at hClosFull
                have hCapBound : CapturedEnvFullBounded σcap result1.nextTag' := hClosFull _ hmem
                have hCapPred := capturedPredTagsBounded_of_fullBounded hCapBound
                have hmono_r2_r1 : result2.nextTag' ≤ result1.nextTag' :=
                  typecheck_normal_nextTag_mono (ctxAfter ctxᵢ result2) e1 fuel' result1
                    (by simpa [typecheck] using htc1')
                have hArgPred : qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ result1.nextTag' := by
                  have := (typecheckExpr_preserves_predTagsBounded ctxᵢ e2 fuel' result2
                    (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2).2
                  rw [hqt2] at this
                  exact qtypPredTagBounded_mono this hmono_r2_r1
                have hArgClos : etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp result1.nextTag' := by
                  have := typecheckExpr_preserves_closureCapturedBounded ctxᵢ e2 fuel' result2
                    (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2
                  rw [hqt2] at this; exact etypClosuresFullBounded_mono this hmono_r2_r1
                refine ⟨by simpa [bodyCtx] using hb_tag1,
                  ⟨predTagsBoundedInVarEnv_update
                    (predTagsBoundedInVarEnv_ofCaptured hCapPred) hArgPred,
                   by simpa [bodyCtx] using hb_predM1⟩,
                  varEnvClosuresCapturedBounded_update
                    (varEnvClosuresCapturedBounded_ofCaptured hCapBound) hArgClos⟩
            have hIH_body :=
              IH fuelBody hfuel_lt (PExpr.toExpr pbody) bodyCtx hTmBody htagBoundedBody result3Shared htcBody'
            have hwfBodyCtx : wfTypeContext bodyCtx := by
              simp only [bodyCtx, wfTypeContext]
              have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
              have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
              exact ⟨hwf1.1,
                varEnvRefLocsBounded_update
                  (varEnvRefLocsBounded_ofCaptured
                    (capturedEnvRefLocsBounded_of_fullBounded_refLocs (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))))
                  (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypRefLocsBounded_mono h hmono_e1),
                varEnvClosuresCapturedRefLocsBounded_update
                  (varEnvClosuresCapturedRefLocsBounded_ofCaptured (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption)))
                  (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h hmono_e1)⟩
            -- Phase 2: runtimeInstantiatesCtx for both runs
            have hric_body₀ :
                runtimeInstantiatesCtx bodyCtx cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              let ctxCapBase : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
              have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
              have hric_cap_base :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) cf₀.memory env₀ θ₀1 := by
                constructor
                · intro l a hlookup
                  exact hric₀1.1 l a hlookup
                · intro y qt hlookup
                  exact
                    agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt hlookup
              have hric_body₀' :
                  runtimeInstantiatesCtx
                    { ctxCapBase with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    cf₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₀) (μ := cf₀.memory) (ρ := env₀) (θ := θ₀1)
                  hric_cap_base harg₀_typed
                  (agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap))
              simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body₀'
            have hric_body₁ :
                runtimeInstantiatesCtx bodyCtx cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              let ctxCapBase : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
              have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
              have hric_cap_base :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) cf₁.memory env₁ θ₁1 := by
                constructor
                · intro l a hlookup
                  exact hric₁1.1 l a hlookup
                · intro y qt hlookup
                  exact
                    agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt hlookup
              have hric_body₁' :
                  runtimeInstantiatesCtx
                    { ctxCapBase with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₁) (μ := cf₁.memory) (ρ := env₁) (θ := θ₁1)
                  hric_cap_base harg₁_typed
                  (agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap))
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter, henv_update]
                using hric_body₁'
            -- Phase 3: regime infrastructure
            have h_mono1 :
                Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
              regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            have htagR_body : regimeConsistentWithCtx bodyCtx := by
              simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
            -- Phase 4: consistentWithRegime for both runs
            have hcwr_body₀ :
                consistentWithRegime predSat bodyCtx.regime bodyCtx
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have hlocs_src₀ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' cf₀.memory θ₀1 (l, qt) := by
                intro l qt k hlookup hguard hRdef
                exact hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_cap₀ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₀.memory env₀ (x, qt) := by
                intro x qt k hlookup hguard hRdef
                rcases
                    agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap) x qt hlookup
                  with ⟨v, hlookup_v, _htyp_v⟩
                exact hmemberVars₀ x qt k v hlookup hlookup_v hguard hRdef
              have hvars_arg₀ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ := by
                  have hvalc₂ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        result2.qualType c₂'₀.memory θ₀2 v₂₀ := by
                    simpa [ctxAfter] using _hvalc₂₀
                  exact
                    valueConsistentWithRegime_transport_pred
                      (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                      (qt := result2.qualType)
                      (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                      (by simp [hqt2]) (hetyp := by simp [hqt2])
                      hvalc₂
                have hvalc_arg_e1 :
                    valueConsistentWithRegime predSat result1.regime'
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                have hlookup_v_body :
                    (env₀.update x₀ v₂₀).lookup x₀ = some v₂₀ := by
                  simp [VarEnv.update, VarEnv.lookup]
                have hvars_arg_e1R_mem₂ :
                    varsRegime predSat result1.regime' c₂'₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  exact
                    varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₀) (k := k)
                      hlookup_v_body hguard hRdef hvalc_arg_e1
                have hPredSat_mem :
                    ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                  predSat_mem_noPred_compat hpredlaws θ₀1
                have hqtypPredHolds_mem :
                    ∀ (qt : QTyp) (v : Value),
                      qtypPredHolds predSat qt c₂'₀.memory v ↔ qtypPredHolds predSat qt cf₀.memory v := by
                  intro qt v
                  constructor <;> intro h
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).1 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).1 hs)
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).2 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).2 hs)
                exact
                  varsRegime_transport_predHolds
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₀.memory) (μ' := cf₀.memory)
                    (ρ := env₀.update x₀ v₂₀)
                    (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                    hqtypPredHolds_mem hvars_arg_e1R_mem₂
              exact
                consistentWithRegime_closure_body_start
                  (predSat := predSat)
                  (ctx := ctxᵢ) (result1 := result1)
                  (σcap := σcap) (xArg := x₀)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := cf₀.memory) (θ := θ₀1) (ρcap := env₀) (vArg := v₂₀)
                  hlocs_src₀ hvars_cap₀ hvars_arg₀
                    hmemberCvcr₀
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory cf₀.memory)
                    hθext₀1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₀))))
            have hcwr_body₁ :
                consistentWithRegime predSat bodyCtx.regime bodyCtx
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hlocs_src₁ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' cf₁.memory θ₁1 (l, qt) := by
                intro l qt k hlookup hguard hRdef
                exact hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_cap₁ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₁.memory env₁ (x, qt) := by
                intro x qt k hlookup hguard hRdef
                rcases
                    agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap) x qt hlookup
                  with ⟨v, hlookup_v, _htyp_v⟩
                exact hmemberVars₁ x qt k v hlookup hlookup_v hguard hRdef
              have hvars_arg₁ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₁.memory
                      (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ := by
                  have hvalc₂ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        result2.qualType c₂'₁.memory θ₁2 v₂₁ := by
                    simpa [ctxAfter] using _hvalc₂₁
                  exact
                    valueConsistentWithRegime_transport_pred
                      (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                      (qt := result2.qualType)
                      (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                      (by simp [hqt2]) (hetyp := by simp [hqt2])
                      hvalc₂
                have hvalc_arg_e1 :
                    valueConsistentWithRegime predSat result1.regime'
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                have hlookup_v_body :
                    (env₁.update x₀ v₂₁).lookup x₀ = some v₂₁ := by
                  simp [VarEnv.update, VarEnv.lookup]
                have hvars_arg_e1R_mem₂ :
                    varsRegime predSat result1.regime' c₂'₁.memory
                      (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  exact
                    varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (ρ := env₁.update x₀ v₂₁)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₁) (k := k)
                      hlookup_v_body hguard hRdef hvalc_arg_e1
                have hPredSat_mem :
                    ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                  predSat_mem_noPred_compat hpredlaws θ₁1
                have hqtypPredHolds_mem :
                    ∀ (qt : QTyp) (v : Value),
                      qtypPredHolds predSat qt c₂'₁.memory v ↔ qtypPredHolds predSat qt cf₁.memory v := by
                  intro qt v
                  constructor <;> intro h
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).1 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).1 hs)
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).2 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).2 hs)
                exact
                  varsRegime_transport_predHolds
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₁.memory) (μ' := cf₁.memory)
                    (ρ := env₁.update x₀ v₂₁)
                    (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                    hqtypPredHolds_mem hvars_arg_e1R_mem₂
              have hcwr_body₁' :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                exact
                  consistentWithRegime_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := cf₁.memory) (θ := θ₁1) (ρcap := env₁) (vArg := v₂₁)
                    hlocs_src₁ hvars_cap₁ hvars_arg₁
                    hmemberCvcr₁
                    (closureCapturedVarsRegime_transport_μ_θ
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory cf₁.memory)
                      hθext₁1.1
                      (closureCapturedVarsRegime_monotone h_mono1
                        (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                          (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₁))))
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [henv_update] using hcwr_body₁'
            -- Phase 5: agreeOnClean for body start
            have hagree_body_start :
                agreeOnClean predSat bodyCtx.regime bodyCtx
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hmem_agree :
                  ∀ l qt,
                    result1.memEnv'.lookup l = some qt →
                    qtypCleanUnder result1.regime' qt →
                    agreeLocUnder predSat result1.regime' cf₀.memory cf₁.memory θ₀1 θ₁1 (l, qt) := by
                intro l qt hlookup hclean
                exact hagree1.1 l qt (by simpa [ctxAfter] using hlookup) hclean
              have hagree_body_start' :
                  agreeOnClean predSat bodyCtx.regime bodyCtx
                    cf₀.memory (env₀.update x₀ v₂₀) θ₀1
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                have harg_agree :
                    qtypCleanUnder result1.regime' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                      agreeValueUnder predSat result1.regime'
                        cf₀.memory cf₁.memory θ₀1 θ₁1
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                  intro hclean_arg
                  have hclean_arg_e2 :
                      qtypCleanUnder (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                    cleanUnder_of_monotone h_mono1 hclean_arg
                  have hclean_res2 :
                      qtypCleanUnder (ctxAfter ctxᵢ result2).regime result2.qualType := by
                    cases hclean_arg_e2 with
                    | clean hpoison =>
                        have hp2_false : p2 = false := (joinPoison_eq_false hpoison).2
                        have hqt2_poison : result2.qualType.poison = false := by
                          simp [hqt2, hp2_false]
                        exact qtypCleanUnder.clean hqt2_poison
                    | guard k htag hk hnotfun =>
                        have htag_orig : qtypGuardTag result2.qualType = some k := by
                          simp [qtypGuardTag] at htag
                          simp [hqt2, qtypGuardTag, htag]
                        have hnotfun' : result2.qualType.etyp.isFunctionType = false := by
                          simpa [hqt2] using hnotfun
                        exact qtypCleanUnder.guard k htag_orig hk hnotfun'
                  have hval_agree_e2 :
                      agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        result2.qualType v₂₀ v₂₁ :=
                    hres_agree2 hclean_res2
                  have hagree_arg_e2 :
                      agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                    refine agreeValueUnder_transport_clean hclean_arg_e2 ?_ ?_ hval_agree_e2
                    · simp [hqt2]
                    · intro hpoison
                      have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                        simpa using hpoison
                      exact by simpa [hqt2] using (joinPoison_eq_false hjoin).2
                  have hagree_arg_e2_to_e1 :
                      agreeValueUnder predSat result1.regime'
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ :=
                    agreeValueUnder_clean_monotoneRegime h_mono1 hclean_arg hagree_arg_e2
                  exact
                    agreeValueUnder_clean_extends_transport_mem
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory cf₀.memory)
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory cf₁.memory)
                      hclean_arg hθext₀1.1 hθext₁1.1 hagree_arg_e2_to_e1
                exact
                  agreeOnClean_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                    (θ₀ := θ₀1) (θ₁ := θ₁1)
                    (ρcap₀ := env₀) (ρcap₁ := env₁)
                    (vArg₀ := v₂₀) (vArg₁ := v₂₁)
                    hmem_agree hcap harg_agree
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [henv_update] using hagree_body_start'
            -- Phase 6: wfConfig for body init
            have hwfcfg_body_init₀ :
                wfConfig
                  { memory := cf₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := cf₀.nextAddr
                    pureMode := true } := by
              have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                (wfConfig_preserved e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
              have hnext₂_to₁ : c₂'₀.nextAddr ≤ cf₀.nextAddr :=
                terminatesTo_nextAddr_mono e1 c₂'₀ cf₀ (Value.peClosure x₀ body₀ env₀) ht₀_e1
              have hv₂₀_wf : wfValue cf₀.nextAddr v₂₀ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
              have hv₀_closure_wf : wfValue cf₀.nextAddr (Value.peClosure x₀ body₀ env₀) :=
                (wfConfig_preserved e1 _ cf₀ _ ht₀_e1 hwfcf₂₀).2
              have henv₀_wf : wfVarEnv cf₀.nextAddr env₀ := by
                cases hv₀_closure_wf with
                | peClosure _ _ _ henv => exact henv
              constructor
              · intro a ha
                exact hwfcf₁₀.1 a ha
              · simpa [VarEnv.update] using (wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf)
            have hwfcfg_body_init₁ :
                wfConfig
                  { memory := cf₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := cf₁.nextAddr
                    pureMode := true } := by
              have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                (wfConfig_preserved e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
              have hnext₂_to₁ : c₂'₁.nextAddr ≤ cf₁.nextAddr :=
                terminatesTo_nextAddr_mono e1 c₂'₁ cf₁ (Value.peClosure x₁ body₁ env₁) ht₁_e1
              have hv₂₁_wf : wfValue cf₁.nextAddr v₂₁ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
              have hv₁_closure_wf : wfValue cf₁.nextAddr (Value.peClosure x₁ body₁ env₁) :=
                (wfConfig_preserved e1 _ cf₁ _ ht₁_e1 hwfcf₂₁).2
              have henv₁_wf : wfVarEnv cf₁.nextAddr env₁ := by
                cases hv₁_closure_wf with
                | peClosure _ _ _ henv => exact henv
              constructor
              · intro a ha
                exact hwfcf₁₁.1 a ha
              · simpa [VarEnv.update] using (wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf)
            -- Phase 7: terminatesTo for body (pureMode := true)
            have ht₀_body' :
                terminatesTo (PExpr.toExpr pbody)
                  { memory := cf₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := cf₀.nextAddr
                    pureMode := true } evalCfg₀ o₀ := by
              have hbody_eq : PExpr.toExpr pbody = body₀ :=
                PExpr_toExpr_of_toPExpr?_some body₀ pbody htoPExpr
              rw [hbody_eq]
              exact ht₀_body
            have ht₁_body' :
                terminatesTo (PExpr.toExpr pbody)
                  { memory := cf₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := cf₁.nextAddr
                    pureMode := true } evalCfg₁ o₁ := by
              have hbody_eq : PExpr.toExpr pbody = body₀ :=
                PExpr_toExpr_of_toPExpr?_some body₀ pbody htoPExpr
              rw [hbody_eq, hbody]
              exact ht₁_body
            -- Phase 8: Apply body IH
            have hstep_body := hIH_body hpredlaws hTmBody
              cf₀.memory cf₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
              evalCfg₀ evalCfg₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwfBodyCtx htagBoundedBody hric_body₀ hric_body₁ htagR_body
              hcwr_body₀ hcwr_body₁ hagree_body_start
              cf₀.nextAddr cf₁.nextAddr true
              hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
            rcases hstep_body with
              ⟨_hresTm_body,
                ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                  _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after, _htagBounded_body_after,
                  _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                  _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                  _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                  _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩⟩
            -- Pure body preserves memory: cf₀.memory = evalCfg₀.memory
            have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
              obtain ⟨fuel_b₀, verbose_b₀, hbeval_b₀⟩ := ht₀_body'
              exact (beval_pure_memory_eq (PExpr.toExpr pbody) fuel_b₀ _ evalCfg₀ o₀ verbose_b₀
                pbody
                (toExpr_toPExpr? pbody) rfl hbeval_b₀).symm
            have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
              obtain ⟨fuel_b₁, verbose_b₁, hbeval_b₁⟩ := ht₁_body'
              exact (beval_pure_memory_eq (PExpr.toExpr pbody) fuel_b₁ _ evalCfg₁ o₁ verbose_b₁
                pbody
                (toExpr_toPExpr? pbody) rfl hbeval_b₁).symm
            -- Phase 9: Transport agreeOnClean from shared body result to joined res
            have hAgree_out_body :
                agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
              have hsrc_mem : firstShared ∈ first :: rest := by
                rcases applyPFnTClosure_ok_of_mem_mapM
                    (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                    (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                    (result2 := result1) (fuel := fuel')
                    (tcls := tcls) (results := results)
                    (tcl := PFnTClosure.regular x pbody σcap)
                    hmap hmem with
                  ⟨r, hr_mem, happly_r⟩
                have hr_eq : r = firstShared := by
                  have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                    simpa [happly_r] using happly
                  exact Except.ok.inj hEq
                subst hr_eq
                simpa [heq_results] using hr_mem
              have hagree_src :
                  agreeOnClean predSat (ctxAfter ctxᵢ firstShared).regime (ctxAfter ctxᵢ firstShared)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                  regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3Shared htcBody'
                have hres1_to_src_mono :
                    Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      (ctxAfter ctxᵢ firstShared).regime := by
                  simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                constructor
                · intro l qt hlookup hclean
                  have hlookup_body :
                      (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstShared] using hlookup
                  have hclean_body :
                      qtypCleanUnder (ctxAfter bodyCtx result3Shared).regime qt := by
                    simpa [ctxAfter, hfirstShared] using hclean
                  have hloc_agree_body := hagree_body_after.1 l qt hlookup_body hclean_body
                  cases hloc_agree_body with
                  | both_unrealized _ _ hnone₀ hnone₁ =>
                      exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                  | agree_values _ _ a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                      have hlookup₀' : cf₀.memory.lookup a₀' = some n₀ := by
                        simpa [hmem₀_eq] using hlookup₀
                      have hlookup₁' : cf₁.memory.lookup a₁' = some n₁ := by
                        simpa [hmem₁_eq] using hlookup₁
                      have hagree_val' :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀_body θ₁_body qt
                            (Value.num n₀) (Value.num n₁) := by
                        simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hagree_val
                      exact
                        agreeLocUnder.agree_values l qt a₀' a₁' n₀ n₁
                          hreal₀ hreal₁ hlookup₀' hlookup₁' hagree_val'
                · intro x qt hlookup hclean
                  have hclean_res1 :
                      qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime qt :=
                    cleanUnder_of_monotone hres1_to_src_mono hclean
                  have hvar_agree1 := hagree1.2 x qt hlookup hclean_res1
                  cases hvar_agree1 with
                  | both_none _ _ hnone₀ hnone₁ =>
                      have hnone₀' : cf₀.varEnv.lookup x = none := by
                        simpa [hvar₀_eq] using hnone₀
                      have hnone₁' : cf₁.varEnv.lookup x = none := by
                        simpa [hvar₁_eq] using hnone₁
                      exact agreeVarUnder.both_none x qt hnone₀' hnone₁'
                  | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree_val1 =>
                      have hlookup₀' : cf₀.varEnv.lookup x = some v₀ := by
                        simpa [hvar₀_eq] using hlookup₀
                      have hlookup₁' : cf₁.varEnv.lookup x = some v₁ := by
                        simpa [hvar₁_eq] using hlookup₁
                      have hagree_src_regime :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀1 θ₁1 qt v₀ v₁ :=
                        agreeValueUnder_clean_monotoneRegime hres1_to_src_mono hclean hagree_val1
                      have hagree_src_final :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀_body θ₁_body qt v₀ v₁ :=
                        by
                          have hqtypPredHolds_mem_app_out₀ :
                              ∀ (qt' : QTyp) (v' : Value),
                                qtypPredHolds predSat qt' cf₀.memory v' ↔
                                  qtypPredHolds predSat qt' cf₀.memory v' :=
                            qtypPredHolds_mem_compat_of_predSatLaws
                              (hpredlaws := hpredlaws) (θ := θ₀1)
                              (μ := cf₀.memory) (μ' := cf₀.memory)
                          have hqtypPredHolds_mem_app_out₁ :
                              ∀ (qt' : QTyp) (v' : Value),
                                qtypPredHolds predSat qt' cf₁.memory v' ↔
                                  qtypPredHolds predSat qt' cf₁.memory v' :=
                            qtypPredHolds_mem_compat_of_predSatLaws
                              (hpredlaws := hpredlaws) (θ := θ₁1)
                              (μ := cf₁.memory) (μ' := cf₁.memory)
                          exact
                            agreeValueUnder_clean_extends_transport_mem
                              hqtypPredHolds_mem_app_out₀ hqtypPredHolds_mem_app_out₁
                              hclean _hθext₀_body.1 _hθext₁_body.1 hagree_src_regime
                      exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀' hlookup₁' hagree_src_final
              have h_clean_res_to_src :
                  ∀ qt,
                    qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                    qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt := by
                intro qt hclean
                cases hclean with
                | clean hpoison =>
                    exact qtypCleanUnder.clean hpoison
                | guard k htag hk hnotfun =>
                    have hk_src :
                        (ctxAfter ctxᵢ firstShared).regime.lookup? k = some true :=
                      joinTypeResults_lookup_member_regime_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem k true hk
                    exact qtypCleanUnder.guard k htag hk_src hnotfun
              have h_mem_from_src_or_unrealized :
                  ∀ l qt,
                    (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
                    qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                    ((∃ qt_src,
                        (ctxAfter ctxᵢ firstShared).memEnv.lookup l = some qt_src ∧
                        qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src ∧
                        qt.etyp = qt_src.etyp ∧
                        (qt.poison = false → qt_src.poison = false)) ∨
                      (θ₀_body.lookup l = none ∧ θ₁_body.lookup l = none)) := by
                intro l qt hlookup hclean
                by_cases hlookup_src_none : (ctxAfter ctxᵢ firstShared).memEnv.lookup l = none
                · right
                  have hlookup_body_none :
                      (ctxAfter bodyCtx result3Shared).memEnv.lookup l = none := by
                    simpa [ctxAfter, hfirstShared] using hlookup_src_none
                  have hnot_contains_body :
                      ¬ (ctxAfter bodyCtx result3Shared).memEnv.contains l := by
                    intro hcontains
                    have hmem' : l ∈ (ctxAfter bodyCtx result3Shared).memEnv :=
                      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                    have hlookup_isSome :
                        ((ctxAfter bodyCtx result3Shared).memEnv[l]?).isSome = true :=
                      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem'
                    have hlookup_get_none :
                        (ctxAfter bodyCtx result3Shared).memEnv[l]? = none := by
                      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup_body_none
                    simp [hlookup_get_none] at hlookup_isSome
                  have htheta₀_none :
                      θ₀_body.lookup l = none :=
                    theta_not_contains_if_not_in_memEnv
                      (ctx := (ctxAfter bodyCtx result3Shared))
                      (μ := evalCfg₀.memory) (ρ := evalCfg₀.varEnv) (θ := θ₀_body)
                      (l := l) _hric_body_final₀ hnot_contains_body
                  have htheta₁_none :
                      θ₁_body.lookup l = none :=
                    theta_not_contains_if_not_in_memEnv
                      (ctx := (ctxAfter bodyCtx result3Shared))
                      (μ := evalCfg₁.memory) (ρ := evalCfg₁.varEnv) (θ := θ₁_body)
                      (l := l) _hric_body_final₁ hnot_contains_body
                  exact ⟨htheta₀_none, htheta₁_none⟩
                · left
                  rcases Option.ne_none_iff_exists'.1 hlookup_src_none with ⟨qt_src, hlookup_src⟩
                  have hclean_src : qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src :=
                    joinTypeResults_lookup_member_clean_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hclean hlookup_src
                  have hetyp_eq : qt.etyp = qt_src.etyp :=
                    joinTypeResults_lookup_member_etyp_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hlookup_src
                  have hpoison_imp : qt.poison = false → qt_src.poison = false :=
                    joinTypeResults_lookup_member_poison_imp
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hlookup_src
                  exact ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
              have hlookup_back_res_to_src :
                  ∀ k b,
                    (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                    (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b := by
                intro k b hk
                exact
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem k b hk
              exact
                join_transport_agreeOnClean_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ)
                  (first := first)
                  (src := firstShared)
                  (rest := rest)
                  (res := res)
                  (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                  (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                  (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                  h_join hsrc_mem hagree_src h_clean_res_to_src h_mem_from_src_or_unrealized
                  (fun {σcap} {ρcap} h =>
                    memberVarsRegimeEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₀.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberCvcrEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₀.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberVarsRegimeEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₁.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberCvcrEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₁.memory)
                      hlookup_back_res_to_src h)
            -- Phase 10: Pack elements (mirroring arrow case lines 24871-25234)
            have hOutPack_body :
                valueHasETyp θ₀_body o₀ res.qualType.etyp ∧
                valueHasETyp θ₁_body o₁ res.qualType.etyp ∧
                wfTagMeaningCtx tm (ctxAfter ctxᵢ res) ∧
                wfTypeContext (ctxAfter ctxᵢ res) ∧
                TagBoundedCtx (ctxAfter ctxᵢ res) ∧
                wfConfig cf₀ ∧
                wfConfig cf₁ ∧
                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_body ∧
                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_body ∧
                regimeConsistentWithCtx (ctxAfter ctxᵢ res) ∧
                consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body ∧
                consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₁.memory cf₁.varEnv θ₁_body ∧
                agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body ∧
                valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                  res.qualType cf₀.memory θ₀_body o₀ ∧
                valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                  res.qualType cf₁.memory θ₁_body o₁ ∧
                resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                  cf₀.memory cf₁.memory θ₀_body θ₁_body res.qualType o₀ o₁ := by
              have hsrc_mem' : firstShared ∈ first :: rest := by
                rcases applyPFnTClosure_ok_of_mem_mapM
                    (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                    (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                    (result2 := result1) (fuel := fuel')
                    (tcls := tcls) (results := results)
                    (tcl := PFnTClosure.regular x pbody σcap)
                    hmap hmem with
                  ⟨r, hr_mem, happly_r⟩
                have hr_eq : r = firstShared := by
                  have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                    simpa [happly_r] using happly
                  exact Except.ok.inj hEq
                subst hr_eq
                simpa [heq_results] using hr_mem
              have hfirstShared_etyp : firstShared.qualType.etyp = result3Shared.qualType.etyp := by
                rw [hfirstShared, normalizeAppResultByProvenance_etyp]
              have hres1_to_src_mono :
                  Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    (ctxAfter ctxᵢ firstShared).regime := by
                have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                  regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3Shared htcBody'
                simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
              have hlookup_back_res1_to_src :
                  ∀ k b,
                    (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
                intro k b hk_src
                have hRdef_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k ≠ none := by
                  intro hnone
                  rw [hk_src] at hnone
                  contradiction
                have hRdef_res1 :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                  hres1_to_src_mono.2 k hRdef_src
                cases hk_res1 : (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
                | none =>
                    exact False.elim (hRdef_res1 hk_res1)
                | some b1 =>
                    have hcases := hres1_to_src_mono.1 k b1 hk_res1
                    cases hcases with
                    | inl hk_src' =>
                        have hb_eq : b1 = b := by
                          have : some b1 = some b := by
                            calc
                              some b1 = (ctxAfter ctxᵢ firstShared).regime.lookup? k := hk_src'.symm
                              _ = some b := hk_src
                          exact Option.some.inj this
                        simp [hb_eq]
                    | inr hnone_src =>
                        rw [hnone_src] at hk_src
                        cases hk_src
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hAgree_out_body, ?_, ?_, ?_⟩
              · -- shared-member valueHasETyp -> joined valueHasETyp (run 0).
                have hv_src₀ : valueHasETyp θ₀_body o₀ firstShared.qualType.etyp := by
                  rw [hfirstShared_etyp]
                  exact _hv_body₀_typed
                exact
                  joinTypeResults_transport_valueHasETyp_from_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (θ := θ₀_body) (v := o₀)
                    h_join hsrc_mem' hv_src₀
              · -- shared-member valueHasETyp -> joined valueHasETyp (run 1).
                have hv_src₁ : valueHasETyp θ₁_body o₁ firstShared.qualType.etyp := by
                  rw [hfirstShared_etyp]
                  exact _hv_body₁_typed
                exact
                  joinTypeResults_transport_valueHasETyp_from_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (θ := θ₁_body) (v := o₁)
                    h_join hsrc_mem' hv_src₁
              · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
                exact
                  join_transport_wfTagMeaningCtx
                    (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_first_tm
              · -- wfTypeContext (ctxAfter ctxᵢ res)
                exact
                  join_transport_wfTypeContext
                    (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_mem_join
                    (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                (Nat.le_trans
                  (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                    (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                  (mapM_applyPFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel' tcls results hmap first hfirst_in_results)))
                    h_rest_wf
              · -- TagBoundedCtx (ctxAfter ctxᵢ res)
                exact typecheckExpr_preserves_TagBoundedCtx ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res (by simpa [typecheck] using htc) htagBounded
              · -- wfConfig cf₀ (= c₁₀ after subst)
                exact hwfcf₁₀
              · -- wfConfig cf₁ (= c₁₁ after subst)
                exact hwfcf₁₁
              · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hsrc_mem_to_res :
                    ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem'
                constructor
                · intro l a hθ
                  have hloc_src := _hric_body_final₀.1 l a hθ
                  rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                  have hcontains_src : firstShared.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstShared] using hcontains_src_body
                  refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                  simpa [hmem₀_eq] using hmem_contains
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  refine ⟨v, ?_⟩
                  constructor
                  · simpa [hvar₀_eq] using hlookup_v
                  · exact valueHasETyp_extends _hθext₀_body.1 hv_typ
              · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                have hsrc_mem_to_res :
                    ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem'
                constructor
                · intro l a hθ
                  have hloc_src := _hric_body_final₁.1 l a hθ
                  rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                  have hcontains_src : firstShared.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstShared] using hcontains_src_body
                  refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                  simpa [hmem₁_eq] using hmem_contains
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  refine ⟨v, ?_⟩
                  constructor
                  · simpa [hvar₁_eq] using hlookup_v
                  · exact valueHasETyp_extends _hθext₁_body.1 hv_typ
              · -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
                exact
                  join_transport_regimeConsistentWithCtx
                    (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_tag_join h_first_regime
              · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hpred_compat₀ :
                    ∀ (qt' : QTyp) (v' : Value),
                      qtypPredHolds predSat qt' cf₀.memory v' ↔
                        qtypPredHolds predSat qt' cf₀.memory v' :=
                  qtypPredHolds_mem_compat_of_predSatLaws
                    (hpredlaws := hpredlaws) (θ := θ₀1)
                    (μ := cf₀.memory) (μ' := cf₀.memory)
                have hcwr_src₀ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      (ctxAfter ctxᵢ firstShared) cf₀.memory cf₀.varEnv θ₀_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstShared] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstShared] using hRdef
                    have hloc_body :=
                      _hcwr_body_final₀.1 l qt k hlookup_body hguard_body hRdef_body
                    simpa [ctxAfter, hfirstShared, hmem₀_eq] using hloc_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                    | none =>
                        exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_src k b hk_src
                          rw [hk_back] at hnone
                          contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                        have hvar_src :
                            varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstShared).regime)
                            (μ := cf₀.memory) (ρ := cf₀.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                        simpa [hvar₀_eq] using hvar_src
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ _hθext₀_body.1
                      (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                    h_join hsrc_mem' hcwr_src₀
              · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                have hpred_compat₁ :
                    ∀ (qt' : QTyp) (v' : Value),
                      qtypPredHolds predSat qt' cf₁.memory v' ↔
                        qtypPredHolds predSat qt' cf₁.memory v' :=
                  qtypPredHolds_mem_compat_of_predSatLaws
                    (hpredlaws := hpredlaws) (θ := θ₁1)
                    (μ := cf₁.memory) (μ' := cf₁.memory)
                have hcwr_src₁ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      (ctxAfter ctxᵢ firstShared) cf₁.memory cf₁.varEnv θ₁_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstShared] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstShared] using hRdef
                    have hloc_body :=
                      _hcwr_body_final₁.1 l qt k hlookup_body hguard_body hRdef_body
                    simpa [ctxAfter, hfirstShared, hmem₁_eq] using hloc_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                    | none =>
                        exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_src k b hk_src
                          rw [hk_back] at hnone
                          contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                        have hvar_src :
                            varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstShared).regime)
                            (μ := cf₁.memory) (ρ := cf₁.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                        simpa [hvar₁_eq] using hvar_src
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ _hθext₁_body.1
                      (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                    h_join hsrc_mem' hcwr_src₁
              · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hval_src₀ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      firstShared.qualType cf₀.memory θ₀_body o₀ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        evalCfg₀.memory θ₀_body o₀ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) _hvalc_body₀
                  simpa [ctxAfter, hfirstShared, hmem₀_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                    h_join hsrc_mem' hval_src₀
              · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hval_src₁ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      firstShared.qualType cf₁.memory θ₁_body o₁ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        evalCfg₁.memory θ₁_body o₁ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) _hvalc_body₁
                  simpa [ctxAfter, hfirstShared, hmem₁_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                    h_join hsrc_mem' hval_src₁
              · -- shared-member resultAgreesIfClean -> joined result qualType.
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hres_agree_src :
                    resultAgreesIfClean predSat (ctxAfter ctxᵢ firstShared).regime
                      cf₀.memory cf₁.memory θ₀_body θ₁_body firstShared.qualType o₀ o₁ := by
                  have hres_agree_first :
                      resultAgreesIfClean predSat (ctxAfter bodyCtx result3Shared).regime
                        evalCfg₀.memory evalCfg₁.memory θ₀_body θ₁_body
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        o₀ o₁ :=
                    resultAgreesIfClean_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ₀ := evalCfg₀.memory) (μ₁ := evalCfg₁.memory)
                      (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                      _hres_agree_body
                  simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hres_agree_first
                exact
                  joinTypeResults_transport_resultAgreesIfClean_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory) (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                    (o₀ := o₀) (o₁ := o₁)
                    h_join hsrc_mem' hres_agree_src
            have hResTm_res : QTypRespectsTagMeaning tm res.qualType :=
              joinTypeResults_QTypRespectsTagMeaning
                (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join h_first_qtm h_rest_qtm
            exact ⟨hResTm_res, θ₀_body, θ₁_body,
              wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 _hθext₀_body),
              wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 _hθext₁_body),
              hOutPack_body⟩
          · -- dirty-internal fallback branch (¬ internalPoisonClean).
            have hptrue : p = true := by
              have : ¬ p = false := by
                simpa [hetyp1, internalPoisonClean, getInternalPoison] using hdirty
              cases p <;> simp at this
              rfl
            have h_p1p : joinPoison p1 p = true := by
              simp [hptrue, joinPoison]
            exact hOutPack_p1p_true h_p1p
        · -- ===== Fallback: not qtypCleanUnder result1.qualType =====
          -- resultAgreesIfClean is vacuous (parrow => p1=true => res poison/noPred);
          -- rest needs unary member-evidence helper.
          have hpoison1_true : result1.qualType.poison = true := by
            by_contra hfalse
            have hpoison_false : result1.qualType.poison = false := Bool.eq_false_iff.mpr hfalse
            have hclean : qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType :=
              qtypCleanUnder.clean hpoison_false
            exact hclean1_e1 hclean
          have h_p1p : joinPoison p1 p = true := by
            rw [← hp1]
            simp [hpoison1_true, joinPoison]
          exact hOutPack_p1p_true h_p1p
