/-
  StepFRApp.lean - Fault-robustness proof for function application (stepFR_app).

  Contains the stepFR_app lemma and all helper lemmas used exclusively by it,
  including join-transport lemmas, applyFnTClosure/applyPFnTClosure infrastructure,
  and joinTypeResults compatibility lemmas.
-/
import LeanProofs.StepFR
import LeanProofs.ExternBoundary
import LeanProofs.JoinMemberTransport

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

-- Given `terminatesTo e c₀ c'` with `c₀.pureMode = pm`, produces the pair
-- (`c'.pureMode = pm`, `c' = {..c'.., pureMode := pm}`). The record equality is
-- useful for rewriting `ht : terminatesTo _ _ c'` when downstream calls require
-- the config in explicit-record form.
private lemma cfg_pureMode_eq_of_terminatesTo
    {e : Expr} {c₀ c' : Config} {v : Value} {pm : Bool}
    (ht : terminatesTo e c₀ c' v) (hinit : c₀.pureMode = pm)
    (hreg : c₀.registry = emptyExternRegistry) :
    c'.pureMode = pm ∧
    c' = { memory := c'.memory, varEnv := c'.varEnv, nextAddr := c'.nextAddr, pureMode := pm } := by
  have h : c'.pureMode = pm := (terminatesTo_preserves_pureMode e c₀ c' v ht).trans hinit
  refine ⟨h, ?_⟩
  have hreg' : c'.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht).trans hreg
  have := config_eq_of_registry_default c' hreg'
  rw [this]
  rw [h]

/-- From a successful `typecheck` judgement, extract the `BoundaryTagMeaningPost` bundle.

This bridges the probe-shaped tag-meaning post (`BoundaryTagMeaningPost` in `StepFR.lean`)
to the existing canonical-extension predicate used throughout single-run FR lemmas.

Runtime extern `app` witnesses are exposed by `terminatesTo_app_inv_full` in
`LeanProofs.SemanticsProperties` (`externFn` / `externPfn`); current step proofs still
assume an empty runtime registry, so those branches remain vacuous until
`TrustedRegistry` threading lands. -/
theorem boundary_tag_meaning_post_of_typecheck
    (extTyping : ExternTypingAssumptions) (predSat : PredSat) (tm : TagMeaning) (ctx : TypeContext)
    (e : Expr) (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (h_laws : PredSatLaws predSat tm)
    (htc : typecheck ctx e fuel = .ok res) :
    ∃ tm', BoundaryTagMeaningPost ctx res predSat tm tm' :=
  StepFRSingleRunTagMeaningPost.to_boundary
    (StepFRSingleRunTagMeaningPost.of_typecheck_preserves extTyping predSat tm ctx e fuel res
      h_wf h_bounded h_laws htc)

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
      (∀ id y argTyp retSpec eff, body ≠ Expr.externFn id y argTyp retSpec eff) →
      ∃ σcap,
      FnTClosure.regular x body σcap ∈ tcls ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
        ∀ cursor : Tag × Loc,
        let bodyCtx : TypeContext :=
          { ctx with
            pc := joinPoison p (joinPoison p1 ctx.pc)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            nextTag := cursor.1
            nextLoc := cursor.2
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
      Expr.toPExpr? body ≠ none →
      ∃ σcap pbody,
      Expr.toPExpr? body = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
        ∀ cursor : Tag × Loc,
        let bodyCtx : TypeContext :=
          { ctx with
            pc := joinPoison p (joinPoison ctx.pc p1)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            pureCtx := true
            nextTag := cursor.1
            nextLoc := cursor.2
            regime := result1.regime' }
      CtxCons bodyCtx μ (ρcap.update x vArg) θ

private lemma notExternFnAst_ne_externFn {body : Expr}
    (hnot : ¬ Expr.IsExternFnAst body) :
    ∀ id y argTyp retSpec eff, body ≠ Expr.externFn id y argTyp retSpec eff := by
  intro id y argTyp retSpec eff hbody
  apply hnot
  rw [hbody]
  exact Expr.IsExternFnAst.mk

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

/-- Static provenance for a runtime impure extern dispatch from an arrow closure list.

Runtime application dispatches by inspecting the closure body, so a successful
`externFn` call may come either from a static `FnTClosure.extern` member or from a
regular closure member whose body is the extern declaration expression. -/
private inductive ExternCallBoundaryFnStaticSource
    (tcls : List FnTClosure)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (eff : List Effect)
    (tenv : CapturedVarEnv) : Prop where
  | externMember :
      FnTClosure.extern id x retSpec eff tenv ∈ tcls →
      ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec eff tenv
  | regularExternBody :
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec eff) tenv ∈ tcls →
      ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec eff tenv

/-- Static provenance for runtime pure extern dispatch from a parrow closure list.

Unlike impure extern dispatch, the pure closure invariant cannot use a regular
`Expr.externPfn` body: regular pure closures require `Expr.toPExpr? body = some ...`,
while extern declarations are not pure expressions. -/
private inductive ExternCallBoundaryPfnStaticSource
    (tcls : List PFnTClosure)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (retSpec : ExternReturn)
    (tenv : CapturedVarEnv) : Prop where
  | externMember :
      PFnTClosure.extern id x retSpec tenv ∈ tcls →
      ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec tenv

private lemma list_lookup_some_mem_local
    {α β : Type} [BEq α] [LawfulBEq α]
    (x : α) (y : β) (l : List (α × β)) :
    List.lookup x l = some y → (x, y) ∈ l := by
  intro hlookup
  induction l with
  | nil =>
      simp [List.lookup] at hlookup
  | cons hd tl ih =>
      cases hd with
      | mk x' y' =>
          by_cases hEq : x == x'
          · simp [List.lookup, hEq] at hlookup
            have hx : x = x' := LawfulBEq.eq_of_beq hEq
            subst hx
            subst hlookup
            simp
          · simp [List.lookup, hEq] at hlookup
            exact List.mem_cons_of_mem _ (ih hlookup)

private def AppExternClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext) (result2 result1 : TypeResult)
      (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
      (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
      (x y : Name) (id : ExternId) (argTyp : Typ)
      (retSpec : ExternReturn) (effects : List Effect)
      (ρpre ρcap : VarEnv)
    (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value),
    PredSatLaws predSat tm →
    result2.qualType = ⟨etyp2, p2, pred2⟩ →
    result1.qualType.etyp = ETyp.arrow st1 st2 p tcls →
    Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime' →
    wfExtendsMap θ_arg θ →
    CtxCons (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ →
      ValCons (ctxAfter ctx result2).regime result2.qualType μ_arg θ_arg vArg →
      ValCons (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
        (Value.closure x (Expr.externFn id y argTyp retSpec effects) ρcap) →
      ∃ σcap,
      ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
        ∀ cursor : Tag × Loc,
        let bodyCtx : TypeContext :=
          { ctx with
            pc := joinPoison p (joinPoison p1 ctx.pc)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            nextTag := cursor.1
            nextLoc := cursor.2
            regime := result1.regime' }
      CtxCons bodyCtx μ (ρcap.update x vArg) θ

private def AppExternPClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (ctx : TypeContext) (result2 result1 : TypeResult)
      (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
      (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
      (x y : Name) (id : ExternId) (argTyp : Typ)
      (retSpec : ExternReturn)
      (ρpre ρcap : VarEnv)
    (μ_arg μ : Memory) (θ_arg θ : RealizationMap) (vArg : Value),
    PredSatLaws predSat tm →
    result2.qualType = ⟨etyp2, p2, pred2⟩ →
    result1.qualType.etyp = ETyp.parrow st1 st2 p tcls →
    Regime.monotoneStep (ctxAfter ctx result2).regime result1.regime' →
    wfExtendsMap θ_arg θ →
    CtxCons (ctxAfter (ctxAfter ctx result2) result1) μ ρpre θ →
      ValCons (ctxAfter ctx result2).regime result2.qualType μ_arg θ_arg vArg →
      ValCons (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) ρcap) →
      ∃ σcap,
      ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec σcap ∧
      capturedVarsTypingProperty θ σcap ρcap ∧
        ∀ cursor : Tag × Loc,
        let bodyCtx : TypeContext :=
          { ctx with
            pc := joinPoison p (joinPoison ctx.pc p1)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            pureCtx := true
            nextTag := cursor.1
            nextLoc := cursor.2
            regime := result1.regime' }
      CtxCons bodyCtx μ (ρcap.update x vArg) θ

private lemma QTypRespectsTagMeaning_of_arrow_static_source_captured_lookup
  (tm : TagMeaning)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (id : ExternId) (x y z : Name) (argTyp : Typ)
  (retSpec : ExternReturn) (effects : List Effect)
  (σcap : CapturedVarEnv) (qtCap : QTyp)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hsource : ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap)
  (hlookup : σcap.lookup z = some qtCap) :
  QTypRespectsTagMeaning tm qtCap := by
  intro qt k d hinq hqd
  have hcapMem : (z, qtCap) ∈ σcap :=
    list_lookup_some_mem_local z qtCap σcap (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  cases hsource with
  | externMember hmem =>
      have hroot : QTypInQTyp qtCap qtRes :=
        QTypInQTyp.in_arrow qtCap qtRes st1 st2 p tcls
          (FnTClosure.extern id x retSpec effects σcap) z
          hetyp hmem (by simpa [fnCapturedEnv] using hcapMem)
      exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd
  | regularExternBody hmem =>
      have hroot : QTypInQTyp qtCap qtRes :=
        QTypInQTyp.in_arrow qtCap qtRes st1 st2 p tcls
          (FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap) z
          hetyp hmem (by simpa [fnCapturedEnv] using hcapMem)
      exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd

private lemma wfTagMeaningCtx_ofCaptured_from_arrow_static_source
  (tm : TagMeaning) (ctxMem : TypeContext)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (id : ExternId) (x y : Name) (argTyp : Typ)
  (retSpec : ExternReturn) (effects : List Effect)
  (σcap : CapturedVarEnv)
  (hctxTm : wfTagMeaningCtx tm ctxMem)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hsource : ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap) :
  wfTagMeaningCtx tm { ctxMem with varEnv := VarTypeEnv.ofCaptured σcap } := by
  unfold wfTagMeaningCtx at hctxTm ⊢
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hm⟩
  cases hinq with
  | inVar _ _ z _qt qtRoot hlookup hinqRoot =>
      have hlookupCap : σcap.lookup z = some qtRoot :=
        list_lookup_of_ofCaptured_lookup σcap z qtRoot (by simpa using hlookup)
      have hrootTm : QTypRespectsTagMeaning tm qtRoot :=
        QTypRespectsTagMeaning_of_arrow_static_source_captured_lookup
          tm qtRes st1 st2 p tcls id x y z argTyp retSpec effects σcap qtRoot
          hresTm hetyp hsource hlookupCap
      exact hrootTm hinqRoot hm
  | inMem _ _ l _qt qtRoot hlookup hinqRoot =>
      exact hctxTm.1 (GuardDescInEnvsDeep.intro qt k d
        (QTypInEnvs.inMem ctxMem.varEnv ctxMem.memEnv l qt qtRoot hlookup hinqRoot) hm)

private lemma wfTagMeaningCtx_arrow_static_body
  (tm : TagMeaning) (ctx : TypeContext) (result1 : TypeResult)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (id : ExternId) (x y : Name) (argTyp : Typ)
  (retSpec : ExternReturn) (effects : List Effect)
  (σcap : CapturedVarEnv) (argQt : QTyp)
  (hctxTm : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hsource : ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap)
  (hargTm : QTypRespectsTagMeaning tm argQt) :
  wfTagMeaningCtx tm
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } := by
  let ctxCap : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.ofCaptured σcap }
  have hctxCapTm : wfTagMeaningCtx tm ctxCap := by
    have hcapTm :
        wfTagMeaningCtx tm { (ctxAfter ctx result1) with varEnv := VarTypeEnv.ofCaptured σcap } :=
      wfTagMeaningCtx_ofCaptured_from_arrow_static_source
        tm (ctxAfter ctx result1) qtRes st1 st2 p tcls id x y argTyp retSpec effects
        σcap hctxTm hresTm hetyp hsource
    simpa [ctxCap, ctxAfter] using hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap x argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

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

private lemma consistentWithRegimeMasked_app_closure_body_start
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx : TypeContext) (result2 result1 : TypeResult)
  (σcap : CapturedVarEnv) (x : Name) (argQt : QTyp)
  (μ : Memory) (θ : RealizationMap) (ρpre ρcap : VarEnv) (vArg : Value)
  (cursor : Tag × Loc)
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
      nextTag := cursor.1
      nextLoc := cursor.2
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
        result1.qualType μ θ (Value.closure x body ρcap))
    (hnotExtern : ∀ id y argTyp retSpec effects,
      body ≠ Expr.externFn id y argTyp retSpec effects) :
  ∃ σcap,
    FnTClosure.regular x body σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    ∀ cursor : Tag × Loc,
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := result1.regime' }
      consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ
        (ρcap.update x vArg) θ := by
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
      intro cursor
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) (cursor := cursor) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
    | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
        exact absurd hveq (by simp)
    | closure_extern id xp y argTyp retSpec effects rp σ pp tcl hval _hteq _hmem _hP _hrec =>
        rw [Value.closure.injEq] at hval
        obtain ⟨_hxp, hbody, _hrp⟩ := hval
        exact False.elim (hnotExtern id y argTyp retSpec effects hbody)
    | peClosure_extern _ _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
        exact absurd hveq (by simp)

private lemma consistentWithRegimeMasked_app_arrow_extern_body_start
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
  (x y : Name) (id : ExternId) (argTyp : Typ)
  (retSpec : ExternReturn) (effects : List Effect)
  (ρpre ρcap : VarEnv)
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
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
        (Value.closure x (Expr.externFn id y argTyp retSpec effects) ρcap)) :
  ∃ σcap,
    ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    ∀ cursor : Tag × Loc,
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := result1.regime' }
      consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ
        (ρcap.update x vArg) θ := by
  cases valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_fun with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x (Expr.externFn id y argTyp retSpec effects) ρcap)
  | closure xp bp rp σ s1 s2 pp tcl hval hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hval
      obtain ⟨rfl, hbody, rfl⟩ := hval
      cases hbody
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
          ∀ z qt v,
            σ.lookup z = some qt →
            ρcap.lookup z = some v →
            closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v := by
        intro z qt v hz hv
        exact hrec z qt v hz hv
      refine ⟨σ, ExternCallBoundaryFnStaticSource.regularExternBody hmem, hP.2, ?_⟩
      intro cursor
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) (cursor := cursor) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)
  | closure_extern id' xp y' argTyp' retSpec' effects' rp σ pp tcl hval hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hval
      obtain ⟨rfl, hbody, rfl⟩ := hval
      cases hbody
      have htcl_eq :
          ETyp.arrow argTyp (parseReturnType retSpec) pp tcl =
            ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨_harg, _hret, rfl, rfl⟩ := htcl_eq
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
          ∀ z qt v,
            σ.lookup z = some qt →
            ρcap.lookup z = some v →
            closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v := by
        intro z qt v hz hv
        exact hrec z qt v hz hv
      refine ⟨σ, ExternCallBoundaryFnStaticSource.externMember hmem, hP.2, ?_⟩
      intro cursor
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) (cursor := cursor) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
  | peClosure_extern _ _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)

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
        result1.qualType μ θ (Value.peClosure x body ρcap))
    (htoPExpr_body : Expr.toPExpr? body ≠ none) :
  ∃ σcap pbody,
    Expr.toPExpr? body = some pbody ∧
    PFnTClosure.regular x pbody σcap ∈ tcls ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    ∀ cursor : Tag × Loc,
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := result1.regime' }
      consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ
        (ρcap.update x vArg) θ := by
  cases valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_fun with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x body ρcap)
    | closure _ _ _ _ _ _ _ _ _ hteq _ _ _ =>
        exfalso
        have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hteq.symm.trans hetyp1
        simp at this
    | closure_extern _ _ _ _ _ _ _ _ _ _ hveq _ _ _ =>
        exact absurd hveq (by simp)
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
      intro cursor
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) (cursor := cursor) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr
    | peClosure_extern id xp y argTyp retSpec rp σ pp tcl hval _hteq _hmem _hP _hrec =>
        rw [Value.peClosure.injEq] at hval
        obtain ⟨_hxp, hbody, _hrp⟩ := hval
        subst hbody
        exact absurd (by simp [Expr.toPExpr?]) htoPExpr_body

private lemma consistentWithRegimeMasked_app_parrow_extern_body_start
  (masked : Tag → Prop)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
  (x y : Name) (id : ExternId) (argTyp : Typ) (retSpec : ExternReturn)
  (ρpre ρcap : VarEnv)
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
      valueConsistentWithRegimeMasked masked predSat
        (ctxAfter (ctxAfter ctx result2) result1).regime result1.qualType μ θ
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) ρcap)) :
  ∃ σcap,
    ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec σcap ∧
    capturedVarsTypingProperty θ σcap ρcap ∧
    ∀ cursor : Tag × Loc,
      let bodyCtx : TypeContext :=
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := result1.regime' }
      consistentWithRegimeMasked masked predSat bodyCtx.regime bodyCtx μ
        (ρcap.update x vArg) θ := by
  cases valueConsistentWithRegimeMasked_closureCapturedVarsRegime hval_fun with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x (Expr.externPfn id y argTyp retSpec) ρcap)
  | closure _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact Value.noConfusion hveq
  | closure_extern _ _ _ _ _ _ _ _ _ _ hveq _ _ _ =>
      exact Value.noConfusion hveq
  | peClosure xp bp pbody rp σ s1 s2 pp tcl hval _hteq hpure _hmem _hP _hrec =>
      rw [Value.peClosure.injEq] at hval
      obtain ⟨_hx, hbody, _hrp⟩ := hval
      cases hbody
      simp [Expr.toPExpr?] at hpure
  | peClosure_extern id' xp y' argTyp' retSpec' rp σ pp tcl hval hteq hmem hP hrec =>
      rw [Value.peClosure.injEq] at hval
      obtain ⟨rfl, hbody, rfl⟩ := hval
      cases hbody
      have htcl_eq :
          ETyp.parrow argTyp (parseReturnType retSpec) pp tcl =
            ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp1
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨_harg, _hret, rfl, rfl⟩ := htcl_eq
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
          ∀ z qt v,
            σ.lookup z = some qt →
            ρcap.lookup z = some v →
            closureCapturedVarsRegimeMasked masked predSat result1.regime' qt μ θ v := by
        intro z qt v hz hv
        exact hrec z qt v hz hv
      refine ⟨σ, ExternCallBoundaryPfnStaticSource.externMember hmem, hP.2, ?_⟩
      intro cursor
      simpa using
        consistentWithRegimeMasked_app_closure_body_start
          (masked := masked) (predSat := predSat)
          (ctx := ctx) (result2 := result2) (result1 := result1)
          (σcap := σ) (x := x)
          (argQt := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩)
          (μ := μ) (θ := θ) (ρpre := ρpre) (ρcap := ρcap)
          (vArg := vArg) (cursor := cursor) hcwr hP.1 hσcap_rec hvars_arg harg_cvcr

-- Inversion for regular closures: from
-- `applyFnTClosure (FnTClosure.regular x body tenv) ... fuel = .ok first`,
-- extract that the application ran with positive fuel.
--
-- Suggested proof strategy:
-- unfold `applyFnTClosure` and split on fuel.

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
  | extern id x retSpec effects capturedEnv =>
    have htag := applyFnTClosure_extern_tagEnv_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel id x retSpec effects capturedEnv happly
    have hreg := applyFnTClosure_extern_regime_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel id x retSpec effects capturedEnv happly
    simp only [regimeConsistentWithCtx, ctxAfter]
    rw [htag, hreg]
    exact hreg1


private lemma applyFnTClosureAtCursor_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
      ctx result1 cursor fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
  let resultCursor : TypeResult := { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
  have hregCursor : regimeConsistentWithCtx (ctxAfter ctx resultCursor) := by
    simpa [ctxAfter, resultCursor] using hreg1
  have happlyOld :
      applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx resultCursor fuel = .ok r := by
    unfold applyFnTClosure
    unfold applyFnTClosureAtCursor at happly
    simpa [resultCursor] using happly
  exact
    applyFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := resultCursor) (fuel := fuel) (tcl := tcl) (r := r)
      hregCursor happlyOld


private lemma threaded_applyFnTClosure_forall_wfTypeResult
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res')
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result1 : TypeResult) (fuel : Nat)
    (h_call_lt : fuel < fuel_top) (hwf_result1 : wfTypeResult result1)
    (tcls : List FnTClosure) (results : List TypeResult)
    (hcaptLocs : ∀ tcl ∈ tcls, match tcl with
      | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
      | .extern _ _ _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
    (hargLocs : etypRefLocsBounded argEtyp result1.nextLoc')
    (hargClosLocs : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
    (hthread :
      applyClosuresThreaded
        (fun tcl cursor =>
          applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc') = .ok results) :
    ∀ r, r ∈ results → wfTypeResult r := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound
      (applyOne := fun tcl cursor =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (base := result1.nextLoc')
      (hmono := by
        intro tcl cursor result hcursorLoc happly
        exact applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
          argEtyp argPoison argPred result1 result cursor fuel hcursorLoc
          (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
          happly)
      (hbase := Nat.le_refl _) hthread hr with
    ⟨tcl, htcl, cursor, hcursorLoc, happly⟩
  let resultCursor : TypeResult := { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
  have hwfCursor : wfTypeResult resultCursor := by
    intro l hl
    exact Nat.lt_of_lt_of_le (hwf_result1 l (by simpa [resultCursor] using hl)) hcursorLoc
  have happlyOld :
      applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx resultCursor fuel = .ok r := by
    unfold applyFnTClosure
    unfold applyFnTClosureAtCursor at happly
    simpa [resultCursor] using happly
  have hmapSingle :
      List.mapM
          (fun tcl =>
            applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
              ctx resultCursor fuel)
          [tcl] = .ok [r] := by
    simp [List.mapM_cons, List.mapM_nil, happlyOld, bind, Except.bind, pure, Except.pure]
  have hall :=
    mapM_applyFnTClosure_forall_wfTypeResult
      (fuel_top := fuel_top) (IH := IH)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result_fn := resultCursor) (fuel_call := fuel) (h_call_lt := h_call_lt)
      hwfCursor (tcls := [tcl]) (results := [r])
      (by
        intro t ht
        simp at ht
        subst t
        cases tcl <;>
          exact CapturedEnvRefLocsFullBounded_mono (hcaptLocs _ htcl) hcursorLoc)
      (etypRefLocsBounded_mono hargLocs hcursorLoc)
      (etypClosuresCapturedRefLocsBounded_mono hargClosLocs hcursorLoc)
      hmapSingle
  exact hall r (by simp)

private lemma threaded_applyFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hthread :
    applyClosuresThreaded
      (fun tcl cursor =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      tcls (result1.nextTag', result1.nextLoc') = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input
      (applyOne := fun tcl cursor =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (hthread := hthread) (hmem := hr) with
    ⟨tcl, _htcl, cursor, happly⟩
  exact
    applyFnTClosureAtCursor_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (cursor := cursor) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma threaded_applyFnTClosure_member_nextLoc_mono
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result1 : TypeResult) (fuel : Nat)
    (tcls : List FnTClosure) (results : List TypeResult)
    (hthread :
      applyClosuresThreaded
        (fun tcl cursor =>
          applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc') = .ok results) :
    ∀ r, r ∈ results → result1.nextLoc' ≤ r.nextLoc' := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound
      (applyOne := fun tcl cursor =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (base := result1.nextLoc')
      (hmono := by
        intro tcl cursor result hcursorLoc happly
        exact applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
          argEtyp argPoison argPred result1 result cursor fuel hcursorLoc
          (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
          happly)
      (hbase := Nat.le_refl _) hthread hr with
    ⟨tcl, _htcl, cursor, hcursorLoc, happly⟩
  exact applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
    argEtyp argPoison argPred result1 r cursor fuel hcursorLoc
    (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
    happly

private lemma joinTypeResults_tagEnvConsistentWithRegime
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime :=
  joinTypeResults_tagEnvConsistentWithRegime' ctx first rest res h_join h_first h_rest

-- Any deep sub-type of a tag-meaning-respecting type also respects tag meaning.
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

-- Combined extraction for regular pure-closures from a successful application map.
-- Gives the selected closure's successful application together with body-typing inversion.


private lemma applyPFnTClosure_regular_inv_of_threaded_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (hthread :
    applyClosuresThreaded
      (fun tcl' cursor =>
        applyPFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      tcls (bodyState.nextTag', bodyState.nextLoc') = .ok results)
  (hmem : PFnTClosure.regular x pbody tenv ∈ tcls) :
  ∃ cursor fuelBody first result3,
    bodyState.nextTag' ≤ cursor.1 ∧
    bodyState.nextLoc' ≤ cursor.2 ∧
    first ∈ results ∧
    applyPFnTClosureAtCursor (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx bodyState cursor fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := bodyState.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := bodyState.tagEnv'
        pureCtx := true
        nextTag := cursor.1
        nextLoc := cursor.2
        regime := bodyState.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases applyClosuresThreaded_ok_mem_input_exists_output_with_cursor_bounds
      (applyOne := fun tcl' cursor =>
        applyPFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      (baseTag := bodyState.nextTag') (baseLoc := bodyState.nextLoc')
      (hmono := by
        intro tcl cursor result htag hloc happly
        exact ⟨
          Nat.le_trans htag
            (applyPFnTClosureAtCursor_nextTag_mono_normal tcl ctx st1 st2 p p1
              argEtyp argPoison argPred bodyState result cursor fuel
              (fun m hm e c r htc => typecheck_nextTag_mono c e m r htc)
              happly),
          applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
            argEtyp argPoison argPred bodyState result cursor fuel hloc
            (fun m hm e c r htc => typecheck_nextLoc_mono c e m r htc)
            happly⟩)
      (hbaseTag := Nat.le_refl _) (hbaseLoc := Nat.le_refl _) hthread hmem with
    ⟨first, hfirst_mem, cursor, hcursorTag, hcursorLoc, happly⟩
  let cursorState : TypeResult :=
    { bodyState with nextTag' := cursor.1, nextLoc' := cursor.2 }
  have happly_old :
      applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx cursorState fuel = .ok first := by
    unfold applyPFnTClosure
    unfold applyPFnTClosureAtCursor at happly
    simpa [cursorState] using happly
  rcases applyPFnTClosure_regular_structure
      ctx st1 st2 p p1 argEtyp argPoison argPred cursorState fuel x pbody tenv first
      happly_old with
    ⟨fuelBody, hfuel⟩
  have happly_succ :
      applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx cursorState (Nat.succ fuelBody) = .ok first := by
    simpa [hfuel] using happly_old
  rcases applyPFnTClosure_regular_inv
      ctx st1 st2 p p1 argEtyp argPoison argPred cursorState fuelBody x pbody tenv
      first happly_succ with
    ⟨result3, htc_body, hsub, hfirst_eq⟩
  exact ⟨cursor, fuelBody, first, result3, hcursorTag, hcursorLoc, hfirst_mem, happly, hfuel,
    by simpa [cursorState] using htc_body, hsub, hfirst_eq⟩

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
    | .extern _ _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
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
  | extern id x retSpec capturedEnv =>
    have htag := applyPFnTClosure_extern_tagEnv_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel id x retSpec capturedEnv happly
    have hreg := applyPFnTClosure_extern_regime_eq ctx st1 st2 p p1 argEtyp argPoison argPred
      result1 r fuel id x retSpec capturedEnv happly
    simp only [regimeConsistentWithCtx, ctxAfter]
    rw [htag, hreg]
    exact hreg1


private lemma applyPFnTClosureAtCursor_ok_wfTypeResult
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat)
    (hwf_result1 : wfTypeResult result1)
    (tcl : PFnTClosure)
    (hcaptLocs : match tcl with
      | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
      | .extern _ _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
    (hargLocs : etypRefLocsBounded argEtyp result1.nextLoc')
    (hargClosLocs : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
    (r : TypeResult)
    (hcursorLoc : result1.nextLoc' ≤ cursor.2)
    (happly :
      applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx result1 cursor fuel = .ok r) :
    wfTypeResult r := by
  let resultCursor : TypeResult := { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
  have hwfCursor : wfTypeResult resultCursor := by
    intro l hl
    exact Nat.lt_of_lt_of_le (hwf_result1 l (by simpa [resultCursor] using hl)) hcursorLoc
  have happlyOld :
      applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx resultCursor fuel = .ok r := by
    unfold applyPFnTClosure
    unfold applyPFnTClosureAtCursor at happly
    simpa [resultCursor] using happly
  cases tcl <;>
    exact
      applyPFnTClosure_ok_wfTypeResult
        (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
        (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
        (result1 := resultCursor) (fuel := fuel)
        hwfCursor (tcl := _)
        (hcaptLocs := CapturedEnvRefLocsFullBounded_mono hcaptLocs hcursorLoc)
        (hArgRL := etypRefLocsBounded_mono hargLocs hcursorLoc)
        (hArgCRL := etypClosuresCapturedRefLocsBounded_mono hargClosLocs hcursorLoc)
        (r := r) happlyOld


private lemma applyPFnTClosureAtCursor_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
      ctx result1 cursor fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
  let resultCursor : TypeResult := { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
  have hregCursor : regimeConsistentWithCtx (ctxAfter ctx resultCursor) := by
    simpa [ctxAfter, resultCursor] using hreg1
  have happlyOld :
      applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx resultCursor fuel = .ok r := by
    unfold applyPFnTClosure
    unfold applyPFnTClosureAtCursor at happly
    simpa [resultCursor] using happly
  exact
    applyPFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := resultCursor) (fuel := fuel) (tcl := tcl) (r := r)
      hregCursor happlyOld


private lemma threaded_applyPFnTClosure_forall_wfTypeResult
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result1 : TypeResult) (fuel : Nat)
    (hwf_result1 : wfTypeResult result1)
    (tcls : List PFnTClosure) (results : List TypeResult)
    (hcaptLocs : ∀ tcl ∈ tcls, match tcl with
      | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
      | .extern _ _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc')
    (hargLocs : etypRefLocsBounded argEtyp result1.nextLoc')
    (hargClosLocs : etypClosuresCapturedRefLocsBounded argEtyp result1.nextLoc')
    (hthread :
      applyClosuresThreaded
        (fun tcl cursor =>
          applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc') = .ok results) :
    ∀ r, r ∈ results → wfTypeResult r := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound
      (applyOne := fun tcl cursor =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (base := result1.nextLoc')
      (hmono := by
        intro tcl cursor result hcursorLoc happly
        exact applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
          argEtyp argPoison argPred result1 result cursor fuel hcursorLoc
          (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
          happly)
      (hbase := Nat.le_refl _) hthread hr with
    ⟨tcl, htcl, cursor, hcursorLoc, happly⟩
  exact
    applyPFnTClosureAtCursor_ok_wfTypeResult
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (cursor := cursor) (fuel := fuel)
      hwf_result1 (tcl := tcl) (hcaptLocs := hcaptLocs tcl htcl)
      (hargLocs := hargLocs) (hargClosLocs := hargClosLocs) (r := r)
      hcursorLoc happly

private lemma threaded_applyPFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hthread :
    applyClosuresThreaded
      (fun tcl cursor =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      tcls (result1.nextTag', result1.nextLoc') = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input
      (applyOne := fun tcl cursor =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (hthread := hthread) (hmem := hr) with
    ⟨tcl, _htcl, cursor, happly⟩
  exact
    applyPFnTClosureAtCursor_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (cursor := cursor) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma threaded_applyPFnTClosure_member_nextLoc_mono
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result1 : TypeResult) (fuel : Nat)
    (tcls : List PFnTClosure) (results : List TypeResult)
    (hthread :
      applyClosuresThreaded
        (fun tcl cursor =>
          applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor fuel)
        tcls (result1.nextTag', result1.nextLoc') = .ok results) :
    ∀ r, r ∈ results → result1.nextLoc' ≤ r.nextLoc' := by
  intro r hr
  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound
      (applyOne := fun tcl cursor =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor fuel)
      (base := result1.nextLoc')
      (hmono := by
        intro tcl cursor result hcursorLoc happly
        exact applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
          argEtyp argPoison argPred result1 result cursor fuel hcursorLoc
          (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
          happly)
      (hbase := Nat.le_refl _) hthread hr with
    ⟨tcl, _htcl, cursor, hcursorLoc, happly⟩
  exact applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
    argEtyp argPoison argPred result1 r cursor fuel hcursorLoc
    (fun m hm e c res htc => typecheck_nextLoc_mono c e m res htc)
    happly

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
private lemma closureCapturedVarsRegime_closure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (hnotExtern : ∀ id y argTyp retSpec effects,
      body ≠ Expr.externFn id y argTyp retSpec effects)
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
  | closure_extern id xp y argTyp retSpec effects rp σ pp tcl hveq _hteq _hmem _hP _hrec =>
      rw [Value.closure.injEq] at hveq
      obtain ⟨_hxp, hbody, _hrp⟩ := hveq
      exact False.elim (hnotExtern id y argTyp retSpec effects hbody)
  | peClosure_extern _ _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma closureCapturedVarsRegime_closure_extern_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x y : Name} {id : ExternId} {argTyp : Typ} {retSpec : ExternReturn}
    {effects : List Effect} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (h :
      closureCapturedVarsRegime predSat R qt μ θ
        (Value.closure x (Expr.externFn id y argTyp retSpec effects) env)) :
    (∃ σcap,
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z))
    ∨
    (∃ σcap,
      FnTClosure.extern id x retSpec effects σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z)) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x (Expr.externFn id y argTyp retSpec effects) env)
  | closure xp body rp σ s1 s2 pp tcl hveq _hteq _hmem _hP _hrec =>
      rw [Value.closure.injEq] at hveq
      obtain ⟨_hx, hbody, _hrp⟩ := hveq
      subst xp
      subst rp
      cases hbody
      have htcl_eq :
          ETyp.arrow s1 s2 pp tcl =
            ETyp.arrow st1 st2 p tcls :=
        _hteq.symm.trans hetyp
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨_hs1, _hs2, _hp, rfl⟩ := htcl_eq
      left
      exact ⟨σ, _hmem, _hP.1, _hP.2, fun z qt_z v_z hz hv =>
        closureCapturedVarsRegime.intro (_hrec z qt_z v_z hz hv)⟩
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)
  | closure_extern id' xp y' argTyp' retSpec' effects' rp σ pp tcl hveq hteq hmem hP hrec =>
      cases hveq
      have htcl_eq :
          ETyp.arrow argTyp (parseReturnType retSpec) pp tcl =
            ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨_harg, _hret, _hp, rfl⟩ := htcl_eq
      right
      exact ⟨σ, hmem, hP.1, hP.2, fun z qt_z v_z hz hv =>
        closureCapturedVarsRegime.intro (hrec z qt_z v_z hz hv)⟩
  | peClosure_extern _ _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma closureCapturedVarsRegime_peClosure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
    (htoPExpr_body : Expr.toPExpr? body ≠ none)
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
  | closure_extern _ _ _ _ _ _ _ _ _ _ hveq _ _ _ =>
      exact absurd hveq (by simp)
  | peClosure_extern id xp y argTyp retSpec ρ σ pp tcl hveq _hteq _hmem _hP _hrec =>
      rw [Value.peClosure.injEq] at hveq
      obtain ⟨_hxp, hbody, _hrp⟩ := hveq
      subst hbody
      exact absurd (by simp [Expr.toPExpr?]) htoPExpr_body

private lemma closureCapturedVarsRegime_peClosure_extern_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x y : Name} {id : ExternId} {argTyp : Typ} {retSpec : ExternReturn}
    {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
    (h :
      closureCapturedVarsRegime predSat R qt μ θ
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env)) :
    ∃ σcap,
      PFnTClosure.extern id x retSpec σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x (Expr.externPfn id y argTyp retSpec) env)
  | closure _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)
  | peClosure xp body pbody ρ σ s1 s2 pp tcl hveq _hteq hpure _hmem _hP _hrec =>
      rw [Value.peClosure.injEq] at hveq
      obtain ⟨_hx, hbody, _hrp⟩ := hveq
      cases hbody
      simp [Expr.toPExpr?] at hpure
  | closure_extern _ _ _ _ _ _ _ _ _ _ hveq _ _ _ =>
      exact absurd hveq (by simp)
  | peClosure_extern id' xp y' argTyp' retSpec' ρ σ pp tcl hveq hteq hmem hP hrec =>
      cases hveq
      have htcl_eq :
          ETyp.parrow argTyp (parseReturnType retSpec) pp tcl =
            ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨_harg, _hret, _hp, rfl⟩ := htcl_eq
      exact ⟨σ, hmem, hP.1, hP.2, fun z qt_z v_z hz hv =>
        closureCapturedVarsRegime.intro (hrec z qt_z v_z hz hv)⟩

private lemma valueConsistentWithRegime_closure_extern_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x y : Name} {id : ExternId} {argTyp : Typ} {retSpec : ExternReturn}
    {effects : List Effect} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (h :
      valueConsistentWithRegime predSat R qt μ θ
        (Value.closure x (Expr.externFn id y argTyp retSpec effects) env)) :
    (∃ σcap,
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z))
    ∨
    (∃ σcap,
      FnTClosure.extern id x retSpec effects σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z)) :=
  closureCapturedVarsRegime_closure_extern_extract hetyp
    (valueConsistentWithRegime_closureCapturedVarsRegime h)

private lemma valueConsistentWithRegime_peClosure_extern_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x y : Name} {id : ExternId} {argTyp : Typ} {retSpec : ExternReturn}
    {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
    (h :
      valueConsistentWithRegime predSat R qt μ θ
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env)) :
    ∃ σcap,
      PFnTClosure.extern id x retSpec σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z) :=
  closureCapturedVarsRegime_peClosure_extern_extract hetyp
    (valueConsistentWithRegime_closureCapturedVarsRegime h)


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
    have hcap_src : closureCapturedVarsRegime predSat R qt μ θ v :=
      valueConsistentWithRegime_closureCapturedVarsRegime h
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
  (hnotExtern₀ : ∀ id y argTyp retSpec effects,
    body₀ ≠ Expr.externFn id y argTyp retSpec effects)
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
  | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ hv₁ _ =>
    rw [Value.closure.injEq] at hv₁
    obtain ⟨_hx, hbody, _henv⟩ := hv₁
    exact False.elim (hnotExtern₀ _ _ _ _ _ hbody)
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
  | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ hv₁ _ =>
    cases hv₁
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
  (htoPExpr₀ : Expr.toPExpr? body₀ ≠ none)
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
  | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ hv₁ _ =>
    cases hv₁
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
  | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ hv₁ _ =>
    rw [Value.peClosure.injEq] at hv₁
    obtain ⟨_hx, hbody, _henv⟩ := hv₁
    subst hbody
    exact False.elim (htoPExpr₀ (by simp [Expr.toPExpr?]))
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

private lemma stepFR_app_arrow_sync_from_clean_with_extern
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
  ((∃ σcap,
      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
      x₀ = x₁ ∧
      body₀ = body₁ ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁)
    ∨
    (∃ id x y argTyp retSpec effects σcap,
      FnTClosure.extern id x retSpec effects σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = Expr.externFn id y argTyp retSpec effects ∧
      body₁ = Expr.externFn id y argTyp retSpec effects ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁))
  ∨ (¬ internalPoisonClean res1.qualType) := by
  have h := hagree hclean
  cases h with
  | clean_internal_arrow _ hetyp' htcl hmatch hcap hmv₀ hmc₀ hmv₁ hmc₁ hv₀ hv₁ =>
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.arrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    cases hv₀
    cases hv₁
    subst hmatch
    left
    left
    exact ⟨_, htcl, rfl, rfl, hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
  | clean_internal_arrow_extern _ hetyp' htcl hmatch hcap hmv₀ hmc₀ hmv₁ hmc₁ hv₀ hv₁ =>
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.arrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    cases hv₀
    cases hv₁
    subst hmatch
    left
    right
    exact ⟨_, _, _, _, _, _, _, htcl, rfl, rfl, rfl, rfl,
      hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
  | dirty_internal_arrow hdirty _ _ _ =>
    right
    exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    exfalso
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_parrow _ hetyp' _ _ _ _ _ _ _ =>
    exfalso
    have : ETyp.parrow _ _ _ _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | clean_internal_parrow_extern _ hetyp' _ _ _ _ _ _ _ _ _ =>
    exfalso
    have : ETyp.parrow _ _ _ _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_parrow _ hisParrow _ _ =>
    exfalso
    simp [ETyp.isParrow, hetyp] at hisParrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    exfalso
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this

private lemma stepFR_app_parrow_sync_from_clean_with_extern
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
  ((∃ x pbody σcap,
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
    ∨
    (∃ id x y argTyp retSpec σcap,
      PFnTClosure.extern id x retSpec σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = Expr.externPfn id y argTyp retSpec ∧
      body₁ = Expr.externPfn id y argTyp retSpec ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁))
  ∨ (¬ internalPoisonClean res1.qualType) := by
  have h := hagree hclean
  cases h with
  | clean_internal_parrow _ hetyp' htcl hmatch hcap hmv₀ hmc₀ hmv₁ hmc₁ hv₀ hv₁ =>
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.parrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    cases hv₀
    cases hv₁
    obtain ⟨htoP, rfl⟩ := hmatch
    left
    left
    exact ⟨_, _, _, htoP, htcl, rfl, rfl, rfl, hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
  | clean_internal_parrow_extern _ hetyp' htcl hmatch hcap hmv₀ hmc₀ hmv₁ hmc₁ hv₀ hv₁ =>
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.parrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    cases hv₀
    cases hv₁
    subst hmatch
    left
    right
    exact ⟨_, _, _, _, _, _, htcl, rfl, rfl, rfl, rfl,
      hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
  | dirty_internal_parrow hdirty _ _ _ =>
    right
    exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    exfalso
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_arrow _ hetyp' _ _ _ _ _ _ _ =>
    exfalso
    have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | clean_internal_arrow_extern _ hetyp' _ _ _ _ _ _ _ _ _ =>
    exfalso
    have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_arrow _ hisArrow _ _ =>
    exfalso
    simp [ETyp.isArrow, hetyp] at hisArrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    exfalso
    simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this


-- Pure-arrow analog of shared-member extraction.

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

private def StepFRAppExternClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  AppExternClosureBodyStart CtxCons ValCons predSat tm

private def StepFRAppExternPClosureBodyStart
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (predSat : PredSat) (tm : TagMeaning) : Prop :=
  AppExternPClosureBodyStart CtxCons ValCons predSat tm

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
    hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure hnotExtern
  rcases
    consistentWithRegimeMasked_app_arrow_body_start masked ctx predSat tm result2 result1 etyp2 p2 pred2
      st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure hnotExtern
    with ⟨σcap, hmem, htyping, hbodyCtx⟩
  refine ⟨σcap, hmem, htyping, ?_⟩
  intro cursor
  simpa [consistentWithRegimeMasked] using hbodyCtx cursor

private theorem stepFRApp_externClosureBodyStart_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRAppExternClosureBodyStart
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    predSat tm := by
  intro ctx result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls x y id argTyp retSpec effects
    ρpre ρcap μ_arg μ θ_arg θ vArg hpredlaws hqt2 hetyp1 hmono hθext hctxCons
    hvalArg hvalClosure
  rcases
    consistentWithRegimeMasked_app_arrow_extern_body_start
      masked ctx predSat tm result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls
      x y id argTyp retSpec effects ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure with
    ⟨σcap, hsource, htyping, hbodyCtx⟩
  refine ⟨σcap, hsource, htyping, ?_⟩
  intro cursor
  simpa [consistentWithRegimeMasked] using hbodyCtx cursor

private theorem stepFRApp_pClosureBodyStart_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRAppPClosureBodyStart
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    predSat tm := by
  intro ctx result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
    hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure htoPExpr_body
  rcases
    consistentWithRegimeMasked_app_parrow_body_start masked ctx predSat tm result2 result1 etyp2 p2 pred2
      st1 st2 p p1 tcls x body ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure htoPExpr_body
    with ⟨σcap, pbody, htoPExpr, hmem, htyping, hbodyCtx⟩
  refine ⟨σcap, pbody, htoPExpr, hmem, htyping, ?_⟩
  intro cursor
  simpa [consistentWithRegimeMasked] using hbodyCtx cursor

private theorem stepFRApp_externPClosureBodyStart_masked
  (masked : Tag → Prop) (predSat : PredSat) (tm : TagMeaning) :
  StepFRAppExternPClosureBodyStart
    (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
    predSat tm := by
  intro ctx result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls x y id argTyp retSpec
    ρpre ρcap μ_arg μ θ_arg θ vArg hpredlaws hqt2 hetyp1 hmono hθext hctxCons
    hvalArg hvalClosure
  rcases
    consistentWithRegimeMasked_app_parrow_extern_body_start
      masked ctx predSat tm result2 result1 etyp2 p2 pred2 st1 st2 p p1 tcls
      x y id argTyp retSpec ρpre ρcap μ_arg μ θ_arg θ vArg
      hpredlaws hqt2 hetyp1 hmono hθext hctxCons hvalArg hvalClosure with
    ⟨σcap, hsource, htyping, hbodyCtx⟩
  refine ⟨σcap, hsource, htyping, ?_⟩
  intro cursor
  simpa [consistentWithRegimeMasked] using hbodyCtx cursor

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

private lemma externFnStaticSource_of_valueConsistentWithRegime
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x y : Name} {id : ExternId} {argTyp : Typ} {retSpec : ExternReturn}
    {effects : List Effect} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (h :
      valueConsistentWithRegime predSat R qt μ θ
        (Value.closure x (Expr.externFn id y argTyp retSpec effects) env)) :
    ∃ σcap,
      ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects σcap ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (z : Name) (qt_z : QTyp) (v_z : Value),
        σcap.lookup z = some qt_z →
        env.lookup z = some v_z →
        closureCapturedVarsRegime predSat R qt_z μ θ v_z) := by
  rcases valueConsistentWithRegime_closure_extern_extract hetyp h with hregular | hextern
  · rcases hregular with ⟨σcap, hmem, hregime, htyping, hrec⟩
    exact
      ⟨σcap, ExternCallBoundaryFnStaticSource.regularExternBody hmem,
        hregime, htyping, hrec⟩
  · rcases hextern with ⟨σcap, hmem, hregime, htyping, hrec⟩
    exact
      ⟨σcap, ExternCallBoundaryFnStaticSource.externMember hmem,
        hregime, htyping, hrec⟩

private theorem ExternCallBoundaryFnStaticSource.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List FnTClosure}
    (hagreesExtern : TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    (hregularExternBody :
      ∀ {id x y retSpec effects capturedEnv},
        FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
        ∃ entry,
          TrustedRegistry.lookup? tr id = some entry ∧
          TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv}
    (hstatic :
      ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects capturedEnv)
    {implFn : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address)}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value} {mem' : Memory} {addr' : Address}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hpure : callEntry.callConfig.pureMode = false)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.fn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw, mem', addr'))
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = { callEntry.callConfig with memory := mem', nextAddr := addr' }) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  cases hstatic with
  | externMember hmem =>
      exact
        TrustedRegistryAgreesWithFnTClosures.callBoundaryRun
          hagreesExtern hmem hargName hregistry hpure hunified hGet hArg hImpl hValRet hcfg
  | regularExternBody hmem =>
      rcases hregularExternBody hmem with ⟨entry, hlookup, hmatch⟩
      have hmatch' :
          TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects := by
        simpa [hargName] using hmatch
      have hlookupRuntime :
          (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl :=
        TrustedRegistry.lookup_toRuntimeRegistry hlookup
      have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
        rw [hregistry]
        simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hlookupRuntime
      have hGetDecl :
          callEntry.callConfig.registry.get? entry.decl.id =
            some (ExternImpl.fn implFn) := by
        simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hGet
      have himpl : entry.impl = ExternImpl.fn implFn :=
        Option.some.inj (hlookupCall.symm.trans hGetDecl)
      exact
        ⟨entry, hlookup,
          ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
            hArg hImpl hValRet hcfg⟩

private theorem ExternCallBoundaryPfnStaticSource.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List PFnTClosure}
    (hagreesExtern : TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv}
    (hstatic :
      ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec capturedEnv)
    {implFn : VarEnv → Value → Memory → Except ExternError Value}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.pfn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw)
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = callEntry.callConfig) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  cases hstatic with
  | externMember hmem =>
      exact
        TrustedRegistryAgreesWithPFnTClosures.callBoundaryRun
          hagreesExtern hmem hargName hregistry hunified hGet hArg hImpl hValRet hcfg

/-- Body-local single-run contract for successful impure extern app dispatch.

    The contract deliberately returns an `ExternBoundarySinglePost` for the
    selected body/member result instead of the final surrounding `Expr.app`
    post.  App-specific transport from this body post to the outer app post is
    owned by the shared app helpers. -/
private def ExternCallBoundarySingleFnContract
    (masked : Tag → Prop)
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (_ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (ctxᵢ : TypeContext) (_res : TypeResult)
    (e1 e2 : Expr)
    (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value)
    (_hθwf : wfRealizationMap θ)
    (_hwf : wfTypeContext ctxᵢ)
    (_hric : runtimeInstantiatesCtx ctxᵢ μ ρ θ)
    (_hreg : regimeConsistentWithCtxMasked masked ctxᵢ)
    (_hmasked_none : ∀ k, masked k → ctxᵢ.regime.lookup? k = none)
    (_hctxCons : CtxCons ctxᵢ μ ρ θ)
    (a : Address) (pm : Bool)
    (_hwfcfg :
      wfConfig
        ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
           registry := registry } : Config))
    (bodyCtx : TypeContext) (result3 : TypeResult)
    (predSatBody : PredSat) (tmBody : TagMeaning)
    (θBody : RealizationMap) (callEntry : ExternCallEntry)
    (_hpredlawsBody : PredSatLaws predSatBody tmBody)
    (_hwfTmBody : wfTagMeaningCtx tmBody bodyCtx)
    (_hTmBoundedBody : TagMeaningBounded tmBody bodyCtx.nextTag)
    (_hθBodyWf : wfRealizationMap θBody)
    (_hwfBody : wfTypeContext bodyCtx)
    (_hricBody :
      runtimeInstantiatesCtx bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (_htagRBody : regimeConsistentWithCtx bodyCtx)
    (_hcwrBody :
      consistentWithRegime predSatBody bodyCtx.regime bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (_hwfcfgBody : wfConfig callEntry.bodyConfig)
    (_hpcBody : bodyCtx.pc = true)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ) (retSpec : ExternReturn)
    (eff : List Effect) (tenv : CapturedVarEnv)
    (env : VarEnv)
    (impl : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address))
    (vRaw : Value) (mem' : Memory) (addr' : Address),
    ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec eff tenv →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.closure x (Expr.externFn id y argTyp retSpec eff) env) →
    c₁.pureMode = false →
    c₁.registry.get? id = some (ExternImpl.fn impl) →
    valueMatchesTyp v₂ argTyp = true →
    impl (VarEnv.update env x v₂) v₂ c₁.memory c₁.nextAddr =
      Except.ok (vRaw, mem', addr') →
    validateExternReturn id retSpec vRaw = Except.ok o →
    cf = { c₁ with memory := mem', nextAddr := addr', pureMode := c₁.pureMode } →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁ →
    callEntry.argName = x →
    callEntry.argValue = v₂ →
    callEntry.capturedEnv = env →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ExternBoundarySinglePost bodyCtx result3 predSatBody tmBody
      θBody callEntry.bodyConfig.memory (callEntry.bodyOutputConfig cf) o

/-- Empty-registry discharge for the body-local impure extern single-run
    contract.  Successful extern dispatch is impossible from the default
    initial registry. -/
private theorem ExternCallBoundarySingleFnContract.of_emptyExternRegistry
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure} :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls := by
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        _hpredlawsBody _hwfTmBody _hTmBoundedBody _hθBodyWf _hwfBody _hricBody
        _htagRBody _hcwrBody _hwfcfgBody _hpcBody
        c₂' v₂ c₁ id x y argTyp retSpec eff _tenv _env
        _impl _vRaw _mem' _addr' _hstatic ht_e2 ht_e1 _hpure hGet _hArg _hImpl
        _hValRet _hcf _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured
        _hunified
  exfalso
  -- Trace registry preservation from the default initial config (which has
  -- `registry = emptyExternRegistry` by `Config.mk` default) through `e2` and
  -- `e1` to `c₁`, then contradict the successful runtime registry lookup.
  have hreg2' : c₂'.registry = emptyExternRegistry :=
    terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht_e1).trans hreg2'
  rw [hreg_c₁] at hGet
  simp [emptyExternRegistry] at hGet

private theorem ExternCallBoundarySingleFnContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    (hregularExternBody :
      ∀ {argTyp : Typ} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv},
        FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
        ∃ entry,
          TrustedRegistry.lookup? tr id = some entry ∧
          TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hpcBody
        c₂' v₂ c₁ id x y argTyp retSpec eff tenv env impl vRaw mem' addr'
        hstatic ht_e2 ht_e1 hpure hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
        hargName hargValue hcaptured hunified
  have hreg_c₂' : c₂'.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht_e1).trans hreg_c₂'
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁
  have hpureCall : callEntry.callConfig.pureMode = false := by
    rw [hcallCfg]
    exact hpure
  have hGetCall :
      callEntry.callConfig.registry.get? id = some (ExternImpl.fn impl) := by
    rw [hcallCfg]
    exact hGet
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp = true := by
    rw [hargValue]
    exact hArg
  have hImplCall :
      impl callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw, mem', addr') := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl
  have hcfgCall :
      cf = { callEntry.callConfig with memory := mem', nextAddr := addr' } := by
    simpa [hcallCfg] using hcf
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp))
      (hregularExternBody (argTyp := argTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (effects := eff) (capturedEnv := tenv)
      hstatic hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  have hrun' :
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o := hrun
  have hwfTmCall : wfTagMeaningCtx tmBody callEntry.bodyCtx := by
    simpa [hbodyCtx] using hwfTmBody
  have hTmBoundedCall : TagMeaningBounded tmBody callEntry.bodyCtx.nextTag := by
    simpa [hbodyCtx] using hTmBoundedBody
  have hwfCall : wfTypeContext callEntry.bodyCtx := by
    simpa [hbodyCtx] using hwfBody
  have htagRCall : regimeConsistentWithCtx callEntry.bodyCtx := by
    simpa [hbodyCtx] using htagRBody
  have hricCall :
      runtimeInstantiatesCtx callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody := by
    simpa [hbodyCtx] using hricBody
  have hcwrCall :
      consistentWithRegime predSatBody callEntry.bodyCtx.regime callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody := by
    simpa [hbodyCtx] using hcwrBody
  have hpcCall : callEntry.bodyCtx.pc = true := by
    simpa [hbodyCtx] using hpcBody
  simpa [hbodyCtx] using
    entry.spec.callSingle result3 predSatBody tmBody callEntry
      hpredlawsBody hwfTmCall hTmBoundedCall θBody cf o
      hθBodyWf hwfCall hricCall htagRCall hcwrCall hwfcfgBody hrun' hpcCall

/-- Body-local single-run contract for successful pure extern app dispatch. -/
private def ExternCallBoundarySinglePfnContract
    (masked : Tag → Prop)
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (_ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (ctxᵢ : TypeContext) (_res : TypeResult)
    (e1 e2 : Expr)
    (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value)
    (_hθwf : wfRealizationMap θ)
    (_hwf : wfTypeContext ctxᵢ)
    (_hric : runtimeInstantiatesCtx ctxᵢ μ ρ θ)
    (_hreg : regimeConsistentWithCtxMasked masked ctxᵢ)
    (_hmasked_none : ∀ k, masked k → ctxᵢ.regime.lookup? k = none)
    (_hctxCons : CtxCons ctxᵢ μ ρ θ)
    (a : Address) (pm : Bool)
    (_hwfcfg :
      wfConfig
        ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
           registry := registry } : Config))
    (bodyCtx : TypeContext) (result3 : TypeResult)
    (predSatBody : PredSat) (tmBody : TagMeaning)
    (θBody : RealizationMap) (callEntry : ExternCallEntry)
    (_hpredlawsBody : PredSatLaws predSatBody tmBody)
    (_hwfTmBody : wfTagMeaningCtx tmBody bodyCtx)
    (_hTmBoundedBody : TagMeaningBounded tmBody bodyCtx.nextTag)
    (_hθBodyWf : wfRealizationMap θBody)
    (_hwfBody : wfTypeContext bodyCtx)
    (_hricBody :
      runtimeInstantiatesCtx bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (_htagRBody : regimeConsistentWithCtx bodyCtx)
    (_hcwrBody :
      consistentWithRegime predSatBody bodyCtx.regime bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (_hwfcfgBody : wfConfig callEntry.bodyConfig)
    (_hpcBody : bodyCtx.pc = true)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ) (retSpec : ExternReturn)
    (tenv : CapturedVarEnv) (env : VarEnv)
    (impl : VarEnv → Value → Memory → Except ExternError Value)
    (vRaw : Value),
    ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec tenv →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env) →
    c₁.registry.get? id = some (ExternImpl.pfn impl) →
    valueMatchesTyp v₂ argTyp = true →
    impl (VarEnv.update env x v₂) v₂ c₁.memory = Except.ok vRaw →
    validateExternReturn id retSpec vRaw = Except.ok o →
    cf = c₁ →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁ →
    callEntry.argName = x →
    callEntry.argValue = v₂ →
    callEntry.capturedEnv = env →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ExternBoundarySinglePost bodyCtx result3 predSatBody tmBody
      θBody callEntry.bodyConfig.memory (callEntry.bodyOutputConfig cf) o

private theorem ExternCallBoundarySinglePfnContract.of_emptyExternRegistry
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure} :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls := by
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        _hpredlawsBody _hwfTmBody _hTmBoundedBody _hθBodyWf _hwfBody _hricBody
        _htagRBody _hcwrBody _hwfcfgBody _hpcBody
        c₂' v₂ c₁ id x y argTyp retSpec _tenv _env _impl _vRaw
        _hstatic ht_e2 ht_e1 hGet _hArg _hImpl _hValRet _hcf
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg2' : c₂'.registry = emptyExternRegistry :=
    terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht_e1).trans hreg2'
  rw [hreg_c₁] at hGet
  simp [emptyExternRegistry] at hGet

private theorem ExternCallBoundarySinglePfnContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hpcBody
        c₂' v₂ c₁ id x y argTyp retSpec tenv env impl vRaw
        hstatic ht_e2 ht_e1 hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
        hargName hargValue hcaptured hunified
  have hreg_c₂' : c₂'.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht_e1).trans hreg_c₂'
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁
  have hGetCall :
      callEntry.callConfig.registry.get? id = some (ExternImpl.pfn impl) := by
    rw [hcallCfg]
    exact hGet
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp = true := by
    rw [hargValue]
    exact hArg
  have hImplCall :
      impl callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl
  have hcfgCall : cf = callEntry.callConfig := by
    simpa [hcallCfg] using hcf
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (capturedEnv := tenv)
      hstatic hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  have hrun' :
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o := hrun
  have hwfTmCall : wfTagMeaningCtx tmBody callEntry.bodyCtx := by
    simpa [hbodyCtx] using hwfTmBody
  have hTmBoundedCall : TagMeaningBounded tmBody callEntry.bodyCtx.nextTag := by
    simpa [hbodyCtx] using hTmBoundedBody
  have hwfCall : wfTypeContext callEntry.bodyCtx := by
    simpa [hbodyCtx] using hwfBody
  have htagRCall : regimeConsistentWithCtx callEntry.bodyCtx := by
    simpa [hbodyCtx] using htagRBody
  have hricCall :
      runtimeInstantiatesCtx callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody := by
    simpa [hbodyCtx] using hricBody
  have hcwrCall :
      consistentWithRegime predSatBody callEntry.bodyCtx.regime callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody := by
    simpa [hbodyCtx] using hcwrBody
  have hpcCall : callEntry.bodyCtx.pc = true := by
    simpa [hbodyCtx] using hpcBody
  simpa [hbodyCtx] using
    entry.spec.callSingle result3 predSatBody tmBody callEntry
      hpredlawsBody hwfTmCall hTmBoundedCall θBody cf o
      hθBodyWf hwfCall hricCall htagRCall hcwrCall hwfcfgBody hrun' hpcCall

private lemma cfg_pureMode_registry_eq_of_terminatesTo
    {e : Expr} {c₀ c' : Config} {v : Value} {pm : Bool}
    {registry : ExternRegistry}
    (ht : terminatesTo e c₀ c' v) (hinit : c₀.pureMode = pm)
    (hreg : c₀.registry = registry) :
    c'.pureMode = pm ∧
    c' =
      { memory := c'.memory, varEnv := c'.varEnv, nextAddr := c'.nextAddr,
        pureMode := pm, registry := registry } := by
  have h : c'.pureMode = pm := (terminatesTo_preserves_pureMode e c₀ c' v ht).trans hinit
  refine ⟨h, ?_⟩
  have hreg' : c'.registry = registry :=
    (terminatesTo_preserves_registry ht).trans hreg
  rw [← h]
  exact config_eq_of_registry c' registry hreg'

private def AppTwoRunOutPack
    (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (θ₀_out θ₁_out : RealizationMap) : Prop :=
  valueHasETyp θ₀_out o₀ res.qualType.etyp ∧
  valueHasETyp θ₁_out o₁ res.qualType.etyp ∧
  runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀_out ∧
  runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁_out ∧
  consistentWithRegime predSat (ctxAfter ctx res).regime
    (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀_out ∧
  consistentWithRegime predSat (ctxAfter ctx res).regime
    (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁_out ∧
  agreeOnClean predSat (ctxAfter ctx res).regime
    (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀_out
    cf₁.memory cf₁.varEnv θ₁_out ∧
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime
    res.qualType cf₀.memory θ₀_out o₀ ∧
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime
    res.qualType cf₁.memory θ₁_out o₁ ∧
  resultAgreesIfClean predSat (ctxAfter ctx res).regime
    cf₀.memory cf₁.memory θ₀_out θ₁_out res.qualType o₀ o₁

private def AppTwoRunOutChoice
    (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
    (θ₀ θ₁ : RealizationMap) (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop :=
  ∃ (θ₀_out θ₁_out : RealizationMap),
    wfExtendsMap θ₀ θ₀_out ∧
    wfExtendsMap θ₁ θ₁_out ∧
    AppTwoRunOutPack predSat ctx res cf₀ cf₁ o₀ o₁ θ₀_out θ₁_out

private lemma appTwoRunOutChoice_of_pack
    {predSat : PredSat} {ctx : TypeContext} {res : TypeResult}
    {θ₀ θ₁ θ₀_out θ₁_out : RealizationMap}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hθ₀ : wfExtendsMap θ₀ θ₀_out)
    (hθ₁ : wfExtendsMap θ₁ θ₁_out)
    (hpack : AppTwoRunOutPack predSat ctx res cf₀ cf₁ o₀ o₁ θ₀_out θ₁_out) :
    AppTwoRunOutChoice predSat ctx res θ₀ θ₁ cf₀ cf₁ o₀ o₁ :=
  ⟨θ₀_out, θ₁_out, hθ₀, hθ₁, hpack⟩

private lemma regime_lookup_back_of_monotone
    {src dst : Regime}
    (hmono : Regime.monotoneStep src dst) :
    ∀ k b, dst.lookup? k = some b → src.lookup? k = some b := by
  intro k b hk_dst
  have hdef_dst : dst.lookup? k ≠ none := by
    intro hnone
    rw [hk_dst] at hnone
    contradiction
  have hdef_src : src.lookup? k ≠ none :=
    hmono.2 k hdef_dst
  cases hk_src : src.lookup? k with
  | none =>
      exact False.elim (hdef_src hk_src)
  | some b_src =>
      have hcases := hmono.1 k b_src hk_src
      cases hcases with
      | inl hk_dst' =>
          have hb_eq : b_src = b := by
            have : some b_src = some b := hk_dst'.symm.trans hk_dst
            exact Option.some.inj this
          simp [hb_eq]
      | inr hnone_dst =>
          rw [hnone_dst] at hk_dst
          cases hk_dst

private lemma locsRegime_transport_lookup
    {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
    {entry : Loc × QTyp}
    (hlookup : ∀ k b, R.lookup? k = some b → R'.lookup? k = some b)
    (h : locsRegime predSat R μ θ entry) :
    locsRegime predSat R' μ θ entry := by
  cases h with
  | noPred_ok hpred =>
      exact locsRegime.noPred_ok entry hpred
  | guardOnly_ok k hgo =>
      exact locsRegime.guardOnly_ok entry k hgo
  | withPred_ok k arg_name pred_body var_env a n b hclos hregime hreal hmem hconsist =>
      exact locsRegime.withPred_ok entry k arg_name pred_body var_env a n b hclos
        (hlookup k b hregime) hreal hmem hconsist

private lemma appMember_runtimeInstantiatesCtx_from_body
    {ctx preCtx bodyFinalCtx : TypeContext}
    {first src res : TypeResult} {rest : List TypeResult}
    {cf evalCfg preCfg : Config} {θpre θbody : RealizationMap}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hbody_ric : runtimeInstantiatesCtx bodyFinalCtx evalCfg.memory evalCfg.varEnv θbody)
    (hpre_ric : runtimeInstantiatesCtx preCtx preCfg.memory preCfg.varEnv θpre)
    (hcontains_body_to_src : ∀ l, bodyFinalCtx.memEnv.contains l → src.memEnv'.contains l)
    (hlookup_to_pre :
      ∀ x qt, (ctxAfter ctx res).varEnv.lookup x = some qt → preCtx.varEnv.lookup x = some qt)
    (hmem_eq : cf.memory = evalCfg.memory)
    (hvar_eq : cf.varEnv = preCfg.varEnv)
    (hθext : wfExtendsMap θpre θbody) :
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θbody := by
  have hsrc_mem_to_res :
      ∀ l, src.memEnv'.contains l → res.memEnv'.contains l :=
    joinTypeResults_mem_contains_of_member
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      h_join hsrc_mem
  constructor
  · intro l a hθ
    rcases hbody_ric.1 l a hθ with ⟨hcontains_body, hmem_contains⟩
    exact ⟨hsrc_mem_to_res l (hcontains_body_to_src l hcontains_body),
      by simpa [hmem_eq] using hmem_contains⟩
  · intro x qt hlookup
    rcases hpre_ric.2 (hlookup_to_pre x qt hlookup) with ⟨v, hlookup_v, hv_typ⟩
    exact ⟨v, by simpa [hvar_eq] using hlookup_v,
      valueHasETyp_extends hθext.1 hv_typ⟩

private lemma appMember_consistentWithRegime_from_body
    {predSat : PredSat} {ctx preCtx bodyFinalCtx : TypeContext}
    {first src res : TypeResult} {rest : List TypeResult}
    {cf evalCfg preCfg : Config} {θpre θbody : RealizationMap}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hbody_cwr :
      consistentWithRegime predSat bodyFinalCtx.regime bodyFinalCtx
        evalCfg.memory evalCfg.varEnv θbody)
    (hpre_cwr :
      consistentWithRegime predSat preCtx.regime preCtx preCfg.memory preCfg.varEnv θpre)
    (hmem_lookup_src_to_body :
      ∀ l qt, (ctxAfter ctx src).memEnv.lookup l = some qt →
        bodyFinalCtx.memEnv.lookup l = some qt)
    (hregime_lookup_src_to_body :
      ∀ k b, (ctxAfter ctx src).regime.lookup? k = some b →
        bodyFinalCtx.regime.lookup? k = some b)
    (hregime_lookup_body_to_src :
      ∀ k b, bodyFinalCtx.regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        preCtx.varEnv.lookup x = some qt)
    (hlookup_back_pre_to_src :
      ∀ k b, (ctxAfter ctx src).regime.lookup? k = some b → preCtx.regime.lookup? k = some b)
    (hpred_compat :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg.memory v' ↔
          qtypPredHolds predSat qt' cf.memory v')
    (hmem_eq : cf.memory = evalCfg.memory)
    (hvar_eq : cf.varEnv = preCfg.varEnv)
    (hθext : wfExtendsMap θpre θbody) :
    consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
      cf.memory cf.varEnv θbody := by
  have hcwr_src :
      consistentWithRegime predSat (ctxAfter ctx src).regime (ctxAfter ctx src)
        cf.memory cf.varEnv θbody := by
    refine ⟨?_, ?_, ?_⟩
    · intro l qt k hlookup hguard hRdef
      cases hk_src : (ctxAfter ctx src).regime.lookup? k with
      | none =>
          exact False.elim (hRdef hk_src)
      | some b =>
          have hRdef_body : bodyFinalCtx.regime.lookup? k ≠ none := by
            intro hnone
            have hk_body := hregime_lookup_src_to_body k b hk_src
            rw [hnone] at hk_body
            cases hk_body
          have hloc_body :=
            hbody_cwr.1 l qt k (hmem_lookup_src_to_body l qt hlookup) hguard
              hRdef_body
          have hloc_body_cf :
              locsRegime predSat bodyFinalCtx.regime cf.memory θbody (l, qt) := by
            simpa [hmem_eq] using hloc_body
          exact locsRegime_transport_lookup hregime_lookup_body_to_src hloc_body_cf
    · intro x qt k hlookup hguard hRdef
      cases hk_src : (ctxAfter ctx src).regime.lookup? k with
      | none =>
          exact False.elim (hRdef hk_src)
      | some b =>
          have hRdef_pre : preCtx.regime.lookup? k ≠ none := by
            intro hnone
            have hk_back := hlookup_back_pre_to_src k b hk_src
            rw [hk_back] at hnone
            contradiction
          have hvar_pre :=
            hpre_cwr.2.1 x qt k (hvar_lookup_src_to_pre x qt hlookup) hguard hRdef_pre
          have hvar_pre_mem :=
            varsRegime_transport_predHolds hpred_compat hvar_pre
          have hvar_src :
              varsRegime predSat (ctxAfter ctx src).regime cf.memory preCfg.varEnv
                (x, qt) :=
            varsRegime_transport_active_lookup_back
              (predSat := predSat)
              (R := preCtx.regime)
              (R' := (ctxAfter ctx src).regime)
              (μ := cf.memory) (ρ := preCfg.varEnv) (entry := (x, qt))
              hlookup_back_pre_to_src hguard hk_src hvar_pre_mem
          simpa [hvar_eq] using hvar_src
    · intro x qt v hlookup hlookup_v
      have hlookup_pre : preCfg.varEnv.lookup x = some v := by
        rw [← hvar_eq]
        exact hlookup_v
      have hcvcr :=
        hpre_cwr.2.2 x qt v (hvar_lookup_src_to_pre x qt hlookup) hlookup_pre
      exact closureCapturedVarsRegime_transport_μ_θ hpred_compat hθext.1
        (closureCapturedVarsRegime_transport_lookup_back hlookup_back_pre_to_src hcvcr)
  exact
    joinTypeResults_transport_consistentWithRegime_from_member
      (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (μ := cf.memory) (ρ := cf.varEnv) (θ := θbody)
      h_join hsrc_mem hcwr_src

private lemma appMember_valueConsistentWithRegime_from_body
    {predSat : PredSat} {ctx bodyCtx : TypeContext}
    {first src result3 res : TypeResult} {rest : List TypeResult}
    {cf evalCfg : Config} {θ : RealizationMap} {o : Value} {p p1 : Poison}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hmem_eq : cf.memory = evalCfg.memory)
    (hbody_val :
      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
        result3.qualType evalCfg.memory θ o) :
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime
      res.qualType cf.memory θ o := by
  have hval_src :
      valueConsistentWithRegime predSat (ctxAfter ctx src).regime
        src.qualType cf.memory θ o := by
    have hval_norm :
        valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
          (normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
          evalCfg.memory θ o :=
      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
        (predSat := predSat) (R := (ctxAfter bodyCtx result3).regime)
        (p := p) (p1 := p1) (qt := result3.qualType)
        (μ := evalCfg.memory) (θ := θ) (v := o) hbody_val
    simpa [ctxAfter, hsrc_eq, hmem_eq] using hval_norm
  exact
    joinTypeResults_transport_valueConsistentWithRegime_from_member
      (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (μ := cf.memory) (θ := θ) (v := o)
      h_join hsrc_mem hval_src

private lemma appMember_resultAgreesIfClean_from_body
    {predSat : PredSat} {ctx bodyCtx : TypeContext}
    {first src result3 res : TypeResult} {rest : List TypeResult}
    {cf₀ cf₁ evalCfg₀ evalCfg₁ : Config}
    {θ₀ θ₁ : RealizationMap} {o₀ o₁ : Value} {p p1 : Poison}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hmem₀_eq : cf₀.memory = evalCfg₀.memory)
    (hmem₁_eq : cf₁.memory = evalCfg₁.memory)
    (hbody_agree :
      resultAgreesIfClean predSat (ctxAfter bodyCtx result3).regime
        evalCfg₀.memory evalCfg₁.memory θ₀ θ₁ result3.qualType o₀ o₁) :
    resultAgreesIfClean predSat (ctxAfter ctx res).regime
      cf₀.memory cf₁.memory θ₀ θ₁ res.qualType o₀ o₁ := by
  have hres_agree_src :
      resultAgreesIfClean predSat (ctxAfter ctx src).regime
        cf₀.memory cf₁.memory θ₀ θ₁ src.qualType o₀ o₁ := by
    have hres_agree_norm :
        resultAgreesIfClean predSat (ctxAfter bodyCtx result3).regime
          evalCfg₀.memory evalCfg₁.memory θ₀ θ₁
          (normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
          o₀ o₁ :=
      resultAgreesIfClean_transport_normalizeAppResultByProvenance
        (predSat := predSat) (R := (ctxAfter bodyCtx result3).regime)
        (p := p) (p1 := p1) (qt := result3.qualType)
        (μ₀ := evalCfg₀.memory) (μ₁ := evalCfg₁.memory)
        (θ₀ := θ₀) (θ₁ := θ₁) (o₀ := o₀) (o₁ := o₁)
        hbody_agree
    simpa [ctxAfter, hsrc_eq, hmem₀_eq, hmem₁_eq] using hres_agree_norm
  exact
    joinTypeResults_transport_resultAgreesIfClean_from_member
      (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (μ₀ := cf₀.memory) (μ₁ := cf₁.memory) (θ₀ := θ₀) (θ₁ := θ₁)
      (o₀ := o₀) (o₁ := o₁)
      h_join hsrc_mem hres_agree_src

private lemma appTwoRunOutPack_from_body_post
    {predSat : PredSat} {ctx preCtx bodyCtx : TypeContext}
    {first src result3 res : TypeResult} {rest : List TypeResult}
    {cf₀ cf₁ evalCfg₀ evalCfg₁ preCfg₀ preCfg₁ : Config}
    {θpre₀ θpre₁ θbody₀ θbody₁ : RealizationMap}
    {o₀ o₁ : Value} {p p1 : Poison}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hlookup_back_pre_to_src :
      ∀ k b, (ctxAfter ctx src).regime.lookup? k = some b → preCtx.regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        preCtx.varEnv.lookup x = some qt)
    (hpred_compat₀ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₀.memory v' ↔
          qtypPredHolds predSat qt' cf₀.memory v')
    (hpred_compat₁ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₁.memory v' ↔
          qtypPredHolds predSat qt' cf₁.memory v')
    (hmem₀_eq : cf₀.memory = evalCfg₀.memory)
    (hmem₁_eq : cf₁.memory = evalCfg₁.memory)
    (hvar₀_eq : cf₀.varEnv = preCfg₀.varEnv)
    (hvar₁_eq : cf₁.varEnv = preCfg₁.varEnv)
    (hθext₀ : wfExtendsMap θpre₀ θbody₀)
    (hθext₁ : wfExtendsMap θpre₁ θbody₁)
    (hv_body₀ : valueHasETyp θbody₀ o₀ result3.qualType.etyp)
    (hv_body₁ : valueHasETyp θbody₁ o₁ result3.qualType.etyp)
    (hric_body₀ : runtimeInstantiatesCtx (ctxAfter bodyCtx result3)
      evalCfg₀.memory evalCfg₀.varEnv θbody₀)
    (hric_body₁ : runtimeInstantiatesCtx (ctxAfter bodyCtx result3)
      evalCfg₁.memory evalCfg₁.varEnv θbody₁)
    (hric_pre₀ : runtimeInstantiatesCtx preCtx preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hric_pre₁ : runtimeInstantiatesCtx preCtx preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hcwr_body₀ : consistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      (ctxAfter bodyCtx result3) evalCfg₀.memory evalCfg₀.varEnv θbody₀)
    (hcwr_body₁ : consistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      (ctxAfter bodyCtx result3) evalCfg₁.memory evalCfg₁.varEnv θbody₁)
    (hcwr_pre₀ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hcwr_pre₁ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hagree :
      agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
        cf₀.memory cf₀.varEnv θbody₀ cf₁.memory cf₁.varEnv θbody₁)
    (hval_body₀ : valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      result3.qualType evalCfg₀.memory θbody₀ o₀)
    (hval_body₁ : valueConsistentWithRegime predSat (ctxAfter bodyCtx result3).regime
      result3.qualType evalCfg₁.memory θbody₁ o₁)
    (hres_agree_body :
      resultAgreesIfClean predSat (ctxAfter bodyCtx result3).regime
        evalCfg₀.memory evalCfg₁.memory θbody₀ θbody₁ result3.qualType o₀ o₁) :
    AppTwoRunOutPack predSat ctx res cf₀ cf₁ o₀ o₁ θbody₀ θbody₁ := by
  have hsrc_etyp : src.qualType.etyp = result3.qualType.etyp := by
    rw [hsrc_eq]
    unfold normalizeAppResultByProvenance
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hagree, ?_, ?_, ?_⟩
  · have hv_src₀ : valueHasETyp θbody₀ o₀ src.qualType.etyp := by
      rw [hsrc_etyp]
      exact hv_body₀
    exact
      joinTypeResults_transport_valueHasETyp_from_member
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        (θ := θbody₀) (v := o₀)
        h_join hsrc_mem hv_src₀
  · have hv_src₁ : valueHasETyp θbody₁ o₁ src.qualType.etyp := by
      rw [hsrc_etyp]
      exact hv_body₁
    exact
      joinTypeResults_transport_valueHasETyp_from_member
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        (θ := θbody₁) (v := o₁)
        h_join hsrc_mem hv_src₁
  · exact
      appMember_runtimeInstantiatesCtx_from_body
        (ctx := ctx) (preCtx := preCtx) (bodyFinalCtx := ctxAfter bodyCtx result3)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := preCfg₀)
        (θpre := θpre₀) (θbody := θbody₀)
        h_join hsrc_mem hric_body₀ hric_pre₀
        (fun l hcontains_body => by
          simpa [ctxAfter, hsrc_eq] using hcontains_body)
        hvar_lookup_src_to_pre hmem₀_eq hvar₀_eq hθext₀
  · exact
      appMember_runtimeInstantiatesCtx_from_body
        (ctx := ctx) (preCtx := preCtx) (bodyFinalCtx := ctxAfter bodyCtx result3)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := preCfg₁)
        (θpre := θpre₁) (θbody := θbody₁)
        h_join hsrc_mem hric_body₁ hric_pre₁
        (fun l hcontains_body => by
          simpa [ctxAfter, hsrc_eq] using hcontains_body)
        hvar_lookup_src_to_pre hmem₁_eq hvar₁_eq hθext₁
  · exact
      appMember_consistentWithRegime_from_body
        (predSat := predSat)
        (ctx := ctx) (preCtx := preCtx) (bodyFinalCtx := ctxAfter bodyCtx result3)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := preCfg₀)
        (θpre := θpre₀) (θbody := θbody₀)
        h_join hsrc_mem hcwr_body₀ hcwr_pre₀
        (fun l qt hlookup => by
          simpa [ctxAfter, hsrc_eq] using hlookup)
        (fun k b hk_src => by
          simpa [ctxAfter, hsrc_eq] using hk_src)
        (fun k b hk_body => by
          simpa [ctxAfter, hsrc_eq] using hk_body)
        hvar_lookup_src_to_pre hlookup_back_pre_to_src hpred_compat₀
        hmem₀_eq hvar₀_eq hθext₀
  · exact
      appMember_consistentWithRegime_from_body
        (predSat := predSat)
        (ctx := ctx) (preCtx := preCtx) (bodyFinalCtx := ctxAfter bodyCtx result3)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := preCfg₁)
        (θpre := θpre₁) (θbody := θbody₁)
        h_join hsrc_mem hcwr_body₁ hcwr_pre₁
        (fun l qt hlookup => by
          simpa [ctxAfter, hsrc_eq] using hlookup)
        (fun k b hk_src => by
          simpa [ctxAfter, hsrc_eq] using hk_src)
        (fun k b hk_body => by
          simpa [ctxAfter, hsrc_eq] using hk_body)
        hvar_lookup_src_to_pre hlookup_back_pre_to_src hpred_compat₁
        hmem₁_eq hvar₁_eq hθext₁
  · exact
      appMember_valueConsistentWithRegime_from_body
        (predSat := predSat)
        (ctx := ctx) (bodyCtx := bodyCtx)
        (first := first) (src := src) (result3 := result3) (rest := rest) (res := res)
        (cf := cf₀) (evalCfg := evalCfg₀) (θ := θbody₀) (o := o₀)
        (p := p) (p1 := p1)
        h_join hsrc_mem hsrc_eq hmem₀_eq hval_body₀
  · exact
      appMember_valueConsistentWithRegime_from_body
        (predSat := predSat)
        (ctx := ctx) (bodyCtx := bodyCtx)
        (first := first) (src := src) (result3 := result3) (rest := rest) (res := res)
        (cf := cf₁) (evalCfg := evalCfg₁) (θ := θbody₁) (o := o₁)
        (p := p) (p1 := p1)
        h_join hsrc_mem hsrc_eq hmem₁_eq hval_body₁
  · exact
      appMember_resultAgreesIfClean_from_body
        (predSat := predSat)
        (ctx := ctx) (bodyCtx := bodyCtx)
        (first := first) (src := src) (result3 := result3) (rest := rest) (res := res)
        (cf₀ := cf₀) (cf₁ := cf₁) (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
        (θ₀ := θbody₀) (θ₁ := θbody₁) (o₀ := o₀) (o₁ := o₁)
        (p := p) (p1 := p1)
        h_join hsrc_mem hsrc_eq hmem₀_eq hmem₁_eq hres_agree_body

private lemma appTwoRunOutChoice_from_body_stepFRPost
    {predSat : PredSat} {tmBody : TagMeaning} {ctx preCtx bodyCtx : TypeContext}
    {postExpr : Expr}
    {first src result3 res : TypeResult} {rest : List TypeResult}
    {cf₀ cf₁ evalCfg₀ evalCfg₁ preCfg₀ preCfg₁ : Config}
    {θpre₀ θpre₁ : RealizationMap}
    {o₀ o₁ : Value} {p p1 : Poison}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hlookup_back_pre_to_src :
      ∀ k b, (ctxAfter ctx src).regime.lookup? k = some b → preCtx.regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        preCtx.varEnv.lookup x = some qt)
    (hpred_compat₀ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₀.memory v' ↔
          qtypPredHolds predSat qt' cf₀.memory v')
    (hpred_compat₁ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₁.memory v' ↔
          qtypPredHolds predSat qt' cf₁.memory v')
    (hmem₀_eq : cf₀.memory = evalCfg₀.memory)
    (hmem₁_eq : cf₁.memory = evalCfg₁.memory)
    (hvar₀_eq : cf₀.varEnv = preCfg₀.varEnv)
    (hvar₁_eq : cf₁.varEnv = preCfg₁.varEnv)
    (hric_pre₀ : runtimeInstantiatesCtx preCtx preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hric_pre₁ : runtimeInstantiatesCtx preCtx preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hcwr_pre₀ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hcwr_pre₁ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hagree_out :
      ∀ θbody₀ θbody₁,
        wfExtendsMap θpre₀ θbody₀ →
        wfExtendsMap θpre₁ θbody₁ →
        runtimeInstantiatesCtx (ctxAfter bodyCtx result3)
          evalCfg₀.memory evalCfg₀.varEnv θbody₀ →
        runtimeInstantiatesCtx (ctxAfter bodyCtx result3)
          evalCfg₁.memory evalCfg₁.varEnv θbody₁ →
        agreeOnClean predSat (ctxAfter bodyCtx result3).regime (ctxAfter bodyCtx result3)
          evalCfg₀.memory evalCfg₀.varEnv θbody₀
          evalCfg₁.memory evalCfg₁.varEnv θbody₁ →
        agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
          cf₀.memory cf₀.varEnv θbody₀ cf₁.memory cf₁.varEnv θbody₁)
    (hbody_post :
      StepFRPost bodyCtx postExpr result3 predSat tmBody
        θpre₀ θpre₁ evalCfg₀ evalCfg₁ o₀ o₁) :
    AppTwoRunOutChoice predSat ctx res θpre₀ θpre₁ cf₀ cf₁ o₀ o₁ := by
  rcases hbody_post with
    ⟨_tmOut, _hboundary, _hpredlawsOut, _hresTmOut,
      θbody₀, θbody₁, hθext₀, hθext₁, hv₀, hv₁, _hwfTmOut, _hwfOut,
      _htagOut, _hwfcfg₀, _hwfcfg₁, hric_body₀, hric_body₁, _htagR,
      hcwr_body₀, hcwr_body₁, _hagree_body, hval_body₀, hval_body₁,
      hres_agree_body⟩
  have hpack :
      AppTwoRunOutPack predSat ctx res cf₀ cf₁ o₀ o₁ θbody₀ θbody₁ := by
    exact
      appTwoRunOutPack_from_body_post
        (predSat := predSat)
        (ctx := ctx) (preCtx := preCtx) (bodyCtx := bodyCtx)
        (first := first) (src := src) (result3 := result3)
        (rest := rest) (res := res)
        (cf₀ := cf₀) (cf₁ := cf₁)
        (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
        (preCfg₀ := preCfg₀) (preCfg₁ := preCfg₁)
        (θpre₀ := θpre₀) (θpre₁ := θpre₁)
        (θbody₀ := θbody₀) (θbody₁ := θbody₁)
        (o₀ := o₀) (o₁ := o₁) (p := p) (p1 := p1)
        h_join hsrc_mem hsrc_eq hlookup_back_pre_to_src hvar_lookup_src_to_pre
        hpred_compat₀ hpred_compat₁ hmem₀_eq hmem₁_eq hvar₀_eq hvar₁_eq
        hθext₀ hθext₁ hv₀ hv₁ hric_body₀ hric_body₁ hric_pre₀ hric_pre₁
        hcwr_body₀ hcwr_body₁ hcwr_pre₀ hcwr_pre₁
        (hagree_out θbody₀ θbody₁ hθext₀ hθext₁ hric_body₀ hric_body₁ _hagree_body)
        hval_body₀ hval_body₁ hres_agree_body
  exact appTwoRunOutChoice_of_pack hθext₀ hθext₁ hpack

private lemma appTwoRunOutChoice_from_call_boundaryFR
    {d : ExternDeclaration} {impl : ExternImpl}
    {predSat : PredSat} {tmBody : TagMeaning} {ctx preCtx : TypeContext}
    {postExpr : Expr}
    {first src result3 res : TypeResult} {rest : List TypeResult}
    {cf₀ cf₁ evalCfg₀ evalCfg₁ preCfg₀ preCfg₁ : Config}
    {θpre₀ θpre₁ : RealizationMap}
    {o₀ o₁ : Value} {p p1 : Poison}
    {entry₀ entry₁ : ExternCallEntry}
    (hcallFR : ExternCallBoundaryFR d impl)
    (hctx₁ : entry₁.bodyCtx = entry₀.bodyCtx)
    (hpredlaws : PredSatLaws predSat tmBody)
    (hTmBody : wfTagMeaningCtx tmBody entry₀.bodyCtx)
    (hTmBoundedBody : TagMeaningBounded tmBody entry₀.bodyCtx.nextTag)
    (hinputs : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θpre₀ θpre₁)
    (hrun₀ : ExternCallBoundaryRun d impl entry₀ result3 cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun d impl entry₁ result3 cf₁ o₁)
    (hevalCfg₀ : evalCfg₀ = entry₀.bodyOutputConfig cf₀)
    (hevalCfg₁ : evalCfg₁ = entry₁.bodyOutputConfig cf₁)
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hlookup_back_pre_to_src :
      ∀ k b, (ctxAfter ctx src).regime.lookup? k = some b → preCtx.regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        preCtx.varEnv.lookup x = some qt)
    (hpred_compat₀ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₀.memory v' ↔
          qtypPredHolds predSat qt' cf₀.memory v')
    (hpred_compat₁ :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg₁.memory v' ↔
          qtypPredHolds predSat qt' cf₁.memory v')
    (hmem₀_eq : cf₀.memory = evalCfg₀.memory)
    (hmem₁_eq : cf₁.memory = evalCfg₁.memory)
    (hvar₀_eq : cf₀.varEnv = preCfg₀.varEnv)
    (hvar₁_eq : cf₁.varEnv = preCfg₁.varEnv)
    (hric_pre₀ : runtimeInstantiatesCtx preCtx preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hric_pre₁ : runtimeInstantiatesCtx preCtx preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hcwr_pre₀ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₀.memory preCfg₀.varEnv θpre₀)
    (hcwr_pre₁ : consistentWithRegime predSat preCtx.regime preCtx
      preCfg₁.memory preCfg₁.varEnv θpre₁)
    (hagree_out :
      ∀ θbody₀ θbody₁,
        wfExtendsMap θpre₀ θbody₀ →
        wfExtendsMap θpre₁ θbody₁ →
        runtimeInstantiatesCtx (ctxAfter entry₀.bodyCtx result3)
          evalCfg₀.memory evalCfg₀.varEnv θbody₀ →
        runtimeInstantiatesCtx (ctxAfter entry₀.bodyCtx result3)
          evalCfg₁.memory evalCfg₁.varEnv θbody₁ →
        agreeOnClean predSat (ctxAfter entry₀.bodyCtx result3).regime
          (ctxAfter entry₀.bodyCtx result3)
          evalCfg₀.memory evalCfg₀.varEnv θbody₀
          evalCfg₁.memory evalCfg₁.varEnv θbody₁ →
        agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
          cf₀.memory cf₀.varEnv θbody₀ cf₁.memory cf₁.varEnv θbody₁) :
    AppTwoRunOutChoice predSat ctx res θpre₀ θpre₁ cf₀ cf₁ o₀ o₁ := by
  have hbody_post :
      StepFRPost entry₀.bodyCtx postExpr result3 predSat tmBody
        θpre₀ θpre₁ evalCfg₀ evalCfg₁ o₀ o₁ := by
    simpa [hevalCfg₀, hevalCfg₁] using
      hcallFR postExpr result3 predSat tmBody entry₀ entry₁ hctx₁
        hpredlaws hTmBody hTmBoundedBody θpre₀ θpre₁ hinputs
        cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  exact
    appTwoRunOutChoice_from_body_stepFRPost
      (predSat := predSat) (tmBody := tmBody)
      (ctx := ctx) (preCtx := preCtx) (bodyCtx := entry₀.bodyCtx)
      (postExpr := postExpr)
      (first := first) (src := src) (result3 := result3)
      (rest := rest) (res := res)
      (cf₀ := cf₀) (cf₁ := cf₁)
      (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
      (preCfg₀ := preCfg₀) (preCfg₁ := preCfg₁)
      (θpre₀ := θpre₀) (θpre₁ := θpre₁)
      (o₀ := o₀) (o₁ := o₁) (p := p) (p1 := p1)
      h_join hsrc_mem hsrc_eq hlookup_back_pre_to_src hvar_lookup_src_to_pre
      hpred_compat₀ hpred_compat₁ hmem₀_eq hmem₁_eq hvar₀_eq hvar₁_eq
      hric_pre₀ hric_pre₁ hcwr_pre₀ hcwr_pre₁ hagree_out hbody_post

private lemma appSingleRunMaskedPost_from_body_fields
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    (ctxMember : AppMemberCtxCons CtxCons predSat)
    (ctxJoinMember : AppJoinCtxConsFromMember CtxCons)
    (valBodyResult : AppBodyResultValCons ValCons)
    (valJoinMember : AppJoinValConsFromMember ValCons)
    {ctx bodyCtx : TypeContext}
    {result2 result1 first src result3 res : TypeResult} {rest : List TypeResult}
    {μ : Memory} {ρ : VarEnv} {θ θpre θbody : RealizationMap}
    {cf evalCfg preCfg : Config} {o : Value} {p p1 : Poison}
    {registry : ExternRegistry}
    {hθwf : wfRealizationMap θ}
    {hwf : wfTypeContext ctx}
    {hric_start : runtimeInstantiatesCtx ctx μ ρ θ}
    {hreg : regimeConsistentWithCtxMasked masked ctx}
    {hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none}
    {hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx}
    {hctx_start : CtxCons ctx μ ρ θ}
    {a : Address} {pm : Bool}
    {hwfcfg : wfConfig
      ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } : Config)}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hsrc_eq :
      src =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } })
    (hlookup_back_pre_to_src :
      ∀ k b,
        (ctxAfter ctx src).regime.lookup? k = some b →
        (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        (ctxAfter (ctxAfter ctx result2) result1).varEnv.lookup x = some qt)
    (hpred_compat :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg.memory v' ↔
          qtypPredHolds predSat qt' cf.memory v')
    (hmem_eq : cf.memory = evalCfg.memory)
    (hvar_eq : cf.varEnv = preCfg.varEnv)
    (hθ_start_pre : wfExtendsMap θ θpre)
    (hθ_pre_body : wfExtendsMap θpre θbody)
    (hv_body : valueHasETyp θbody o result3.qualType.etyp)
    (hric_body :
      runtimeInstantiatesCtx (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θbody)
    (hric_pre :
      runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hctx_body : CtxCons (ctxAfter bodyCtx result3) evalCfg.memory evalCfg.varEnv θbody)
    (hctx_pre :
      CtxCons (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hval_body : ValCons (ctxAfter bodyCtx result3).regime result3.qualType
      evalCfg.memory θbody o)
    (hpres_final : PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θbody)
    (hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θbody) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked CtxCons ValCons ctx res (registry := registry) μ ρ θ cf o
      hθwf hwf hric_start hreg hmasked_none hmasked_absent hctx_start a pm hwfcfg := by
  refine ⟨θbody, wfExtendsMap_trans hθ_start_pre hθ_pre_body, ?_, ?_, ?_, ?_,
    hpres_final, hfresh_final⟩
  · have hsrc_etyp : src.qualType.etyp = result3.qualType.etyp := by
      rw [hsrc_eq]
      unfold normalizeAppResultByProvenance
      split_ifs <;> rfl
    have hv_src : valueHasETyp θbody o src.qualType.etyp := by
      rw [hsrc_etyp]
      exact hv_body
    exact
      joinTypeResults_transport_valueHasETyp_from_member
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        (θ := θbody) (v := o)
        h_join hsrc_mem hv_src
  · exact
      appMember_runtimeInstantiatesCtx_from_body
        (ctx := ctx) (preCtx := ctxAfter (ctxAfter ctx result2) result1)
        (bodyFinalCtx := ctxAfter bodyCtx result3)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf) (evalCfg := evalCfg) (preCfg := preCfg)
        (θpre := θpre) (θbody := θbody)
        h_join hsrc_mem hric_body hric_pre
        (fun l hcontains_body => by
          simpa [ctxAfter, hsrc_eq] using hcontains_body)
        hvar_lookup_src_to_pre hmem_eq hvar_eq hθ_pre_body
  · have hctx_src : CtxCons (ctxAfter ctx src) cf.memory cf.varEnv θbody :=
      ctxMember ctx bodyCtx result2 result1 src result3
        (normalizeAppResultByProvenance (joinPoison p1 p)
          { result3.qualType with
            poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
        preCfg evalCfg cf θpre θbody
        hpred_compat hsrc_eq hmem_eq hvar_eq
        hlookup_back_pre_to_src hθ_pre_body hctx_pre hctx_body
    exact ctxJoinMember ctx first src rest res cf.memory cf.varEnv θbody
      h_join hsrc_mem hctx_src
  · have hval_src :
        ValCons (ctxAfter ctx src).regime src.qualType cf.memory θbody o :=
      valBodyResult ctx bodyCtx src result3 p p1 cf.memory evalCfg.memory θbody o
        hsrc_eq hmem_eq hval_body
    exact valJoinMember ctx first src rest res cf.memory θbody o
      h_join hsrc_mem hval_src

private lemma appSingleRunMaskedPost_from_direct_body_fields
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    (ctxMember : AppMemberCtxCons CtxCons predSat)
    (ctxJoinMember : AppJoinCtxConsFromMember CtxCons)
    (valJoinMember : AppJoinValConsFromMember ValCons)
    {ctx bodyCtx : TypeContext}
    {result2 result1 first src res : TypeResult} {rest : List TypeResult}
    {μ : Memory} {ρ : VarEnv} {θ θpre θbody : RealizationMap}
    {cf evalCfg preCfg : Config} {o : Value}
    {registry : ExternRegistry}
    {hθwf : wfRealizationMap θ}
    {hwf : wfTypeContext ctx}
    {hric_start : runtimeInstantiatesCtx ctx μ ρ θ}
    {hreg : regimeConsistentWithCtxMasked masked ctx}
    {hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none}
    {hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx}
    {hctx_start : CtxCons ctx μ ρ θ}
    {a : Address} {pm : Bool}
    {hwfcfg : wfConfig
      ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } : Config)}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hlookup_back_pre_to_src :
      ∀ k b,
        (ctxAfter ctx src).regime.lookup? k = some b →
        (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        (ctxAfter (ctxAfter ctx result2) result1).varEnv.lookup x = some qt)
    (hpred_compat :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg.memory v' ↔
          qtypPredHolds predSat qt' cf.memory v')
    (hmem_eq : cf.memory = evalCfg.memory)
    (hvar_eq : cf.varEnv = preCfg.varEnv)
    (hθ_start_pre : wfExtendsMap θ θpre)
    (hθ_pre_body : wfExtendsMap θpre θbody)
    (hv_body : valueHasETyp θbody o src.qualType.etyp)
    (hric_body :
      runtimeInstantiatesCtx (ctxAfter bodyCtx src) evalCfg.memory evalCfg.varEnv θbody)
    (hric_pre :
      runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hctx_body : CtxCons (ctxAfter bodyCtx src) evalCfg.memory evalCfg.varEnv θbody)
    (hctx_pre :
      CtxCons (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hval_body : ValCons (ctxAfter bodyCtx src).regime src.qualType
      evalCfg.memory θbody o)
    (hpres_final : PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θbody)
    (hfresh_final : FreshCleanLocsUnrealizedOneRun ctx res θbody) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked CtxCons ValCons ctx res (registry := registry) μ ρ θ cf o
      hθwf hwf hric_start hreg hmasked_none hmasked_absent hctx_start a pm hwfcfg := by
  refine ⟨θbody, wfExtendsMap_trans hθ_start_pre hθ_pre_body, ?_, ?_, ?_, ?_,
    hpres_final, hfresh_final⟩
  · exact
      joinTypeResults_transport_valueHasETyp_from_member
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        (θ := θbody) (v := o)
        h_join hsrc_mem hv_body
  · exact
      appMember_runtimeInstantiatesCtx_from_body
        (ctx := ctx) (preCtx := ctxAfter (ctxAfter ctx result2) result1)
        (bodyFinalCtx := ctxAfter bodyCtx src)
        (first := first) (src := src) (rest := rest) (res := res)
        (cf := cf) (evalCfg := evalCfg) (preCfg := preCfg)
        (θpre := θpre) (θbody := θbody)
        h_join hsrc_mem hric_body hric_pre
        (fun l hcontains_body => by
          simpa [ctxAfter] using hcontains_body)
        hvar_lookup_src_to_pre hmem_eq hvar_eq hθ_pre_body
  · have hsrc_eq : src = { src with qualType := src.qualType } := by
      cases src
      rfl
    have hctx_src : CtxCons (ctxAfter ctx src) cf.memory cf.varEnv θbody :=
      ctxMember ctx bodyCtx result2 result1 src src src.qualType
        preCfg evalCfg cf θpre θbody
        hpred_compat hsrc_eq hmem_eq hvar_eq
        hlookup_back_pre_to_src hθ_pre_body hctx_pre hctx_body
    exact ctxJoinMember ctx first src rest res cf.memory cf.varEnv θbody
      h_join hsrc_mem hctx_src
  · have hval_src :
        ValCons (ctxAfter ctx src).regime src.qualType cf.memory θbody o := by
      simpa [ctxAfter, hmem_eq] using hval_body
    exact valJoinMember ctx first src rest res cf.memory θbody o
      h_join hsrc_mem hval_src

private lemma appSingleRunMaskedPost_from_direct_boundary
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    (ctxMember : AppMemberCtxCons CtxCons predSat)
    (ctxJoinMember : AppJoinCtxConsFromMember CtxCons)
    (valJoinMember : AppJoinValConsFromMember ValCons)
    (ctxConsOfRegular :
      ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
        consistentWithRegime predSat ctx.regime ctx μ ρ θ →
        CtxCons ctx μ ρ θ)
    (valConsOfRegular :
      ∀ {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value},
        valueConsistentWithRegime predSat R qt μ θ v →
        ValCons R qt μ θ v)
    {ctx bodyCtx : TypeContext}
    {result2 result1 first src res : TypeResult} {rest : List TypeResult}
    {μ : Memory} {ρ : VarEnv} {θ θpre : RealizationMap}
    {cf evalCfg preCfg : Config} {o : Value} {tmBody : TagMeaning}
    {registry : ExternRegistry}
    {hθwf : wfRealizationMap θ}
    {hwf : wfTypeContext ctx}
    {hric_start : runtimeInstantiatesCtx ctx μ ρ θ}
    {hreg : regimeConsistentWithCtxMasked masked ctx}
    {hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none}
    {hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx}
    {hctx_start : CtxCons ctx μ ρ θ}
    {a : Address} {pm : Bool}
    {hwfcfg : wfConfig
      ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } : Config)}
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hsrc_mem : src ∈ first :: rest)
    (hlookup_back_pre_to_src :
      ∀ k b,
        (ctxAfter ctx src).regime.lookup? k = some b →
        (ctxAfter (ctxAfter ctx result2) result1).regime.lookup? k = some b)
    (hvar_lookup_src_to_pre :
      ∀ x qt, (ctxAfter ctx src).varEnv.lookup x = some qt →
        (ctxAfter (ctxAfter ctx result2) result1).varEnv.lookup x = some qt)
    (hpred_compat :
      ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' preCfg.memory v' ↔
          qtypPredHolds predSat qt' cf.memory v')
    (hmem_eq : cf.memory = evalCfg.memory)
    (hvar_eq : cf.varEnv = preCfg.varEnv)
    (hθ_start_pre : wfExtendsMap θ θpre)
    (hric_pre :
      runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hctx_pre :
      CtxCons (ctxAfter (ctxAfter ctx result2) result1)
        preCfg.memory preCfg.varEnv θpre)
    (hpres_final_of_boundary :
      ∀ {θbody : RealizationMap},
        wfExtendsMap θpre θbody →
        PreservesInheritedFinalCleanLocsOneRun bodyCtx src
          preCfg.memory evalCfg.memory θpre θbody →
        PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θbody)
    (hfresh_final_of_boundary :
      ∀ {θbody : RealizationMap},
        FreshCleanLocsUnrealizedOneRun bodyCtx src θbody →
        FreshCleanLocsUnrealizedOneRun ctx res θbody)
    (hboundary :
      ExternBoundarySinglePost bodyCtx src predSat tmBody θpre preCfg.memory evalCfg o) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked CtxCons ValCons ctx res (registry := registry) μ ρ θ cf o
      hθwf hwf hric_start hreg hmasked_none hmasked_absent hctx_start a pm hwfcfg := by
  rcases hboundary with
    ⟨_tm', _htag, θbody, hθ_pre_body, hv_body, hric_body, hcwr_body,
      hval_body, hpres_body, hfresh_body⟩
  exact
    appSingleRunMaskedPost_from_direct_body_fields
      (predSat := predSat)
      ctxMember ctxJoinMember valJoinMember
      (ctx := ctx) (bodyCtx := bodyCtx)
      (result2 := result2) (result1 := result1)
      (first := first) (src := src) (rest := rest) (res := res)
      (μ := μ) (ρ := ρ) (θ := θ) (θpre := θpre) (θbody := θbody)
      (cf := cf) (evalCfg := evalCfg) (preCfg := preCfg)
      (o := o)
      h_join hsrc_mem hlookup_back_pre_to_src hvar_lookup_src_to_pre
      hpred_compat hmem_eq hvar_eq hθ_start_pre hθ_pre_body
      hv_body hric_body hric_pre
      (ctxConsOfRegular hcwr_body) hctx_pre (valConsOfRegular hval_body)
      (hpres_final_of_boundary hθ_pre_body hpres_body)
      (hfresh_final_of_boundary hfresh_body)

private lemma applyFnTClosure_extern_of_threaded_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (id : ExternId) (x : Name) (retSpec : ExternReturn)
  (effects : List Effect) (tenv : CapturedVarEnv)
  (hthread :
    applyClosuresThreaded
      (fun tcl' cursor =>
        applyFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      tcls (bodyState.nextTag', bodyState.nextLoc') = .ok results)
  (hmem : FnTClosure.extern id x retSpec effects tenv ∈ tcls) :
  ∃ (cursor : Tag × Loc) (first : TypeResult),
    bodyState.nextTag' ≤ cursor.1 ∧
    bodyState.nextLoc' ≤ cursor.2 ∧
    first ∈ results ∧
    applyFnTClosureAtCursor (FnTClosure.extern id x retSpec effects tenv)
      st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor fuel = .ok first := by
  rcases applyClosuresThreaded_ok_mem_input_exists_output_with_cursor_bounds
      (applyOne := fun tcl' cursor =>
        applyFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      (baseTag := bodyState.nextTag') (baseLoc := bodyState.nextLoc')
      (hmono := by
        intro tcl cursor result htag hloc happly
        exact ⟨
          Nat.le_trans htag
            (applyFnTClosureAtCursor_nextTag_mono_normal tcl ctx st1 st2 p p1
              argEtyp argPoison argPred bodyState result cursor fuel
              (fun m hm e c r htc => typecheck_nextTag_mono c e m r htc)
              happly),
          applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
            argEtyp argPoison argPred bodyState result cursor fuel hloc
            (fun m hm e c r htc => typecheck_nextLoc_mono c e m r htc)
            happly⟩)
      (hbaseTag := Nat.le_refl _) (hbaseLoc := Nat.le_refl _) hthread hmem with
    ⟨first, hfirst_mem, cursor, hcursorTag, hcursorLoc, happly⟩
  exact ⟨cursor, first, hcursorTag, hcursorLoc, hfirst_mem, happly⟩

private lemma applyPFnTClosure_extern_of_threaded_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (id : ExternId) (x : Name) (retSpec : ExternReturn)
  (tenv : CapturedVarEnv)
  (hthread :
    applyClosuresThreaded
      (fun tcl' cursor =>
        applyPFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      tcls (bodyState.nextTag', bodyState.nextLoc') = .ok results)
  (hmem : PFnTClosure.extern id x retSpec tenv ∈ tcls) :
  ∃ (cursor : Tag × Loc) (first : TypeResult),
    bodyState.nextTag' ≤ cursor.1 ∧
    bodyState.nextLoc' ≤ cursor.2 ∧
    first ∈ results ∧
    applyPFnTClosureAtCursor (PFnTClosure.extern id x retSpec tenv)
      st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor fuel = .ok first := by
  rcases applyClosuresThreaded_ok_mem_input_exists_output_with_cursor_bounds
      (applyOne := fun tcl' cursor =>
        applyPFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      (baseTag := bodyState.nextTag') (baseLoc := bodyState.nextLoc')
      (hmono := by
        intro tcl cursor result htag hloc happly
        exact ⟨
          Nat.le_trans htag
            (applyPFnTClosureAtCursor_nextTag_mono_normal tcl ctx st1 st2 p p1
              argEtyp argPoison argPred bodyState result cursor fuel
              (fun m hm e c r htc => typecheck_nextTag_mono c e m r htc)
              happly),
          applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
            argEtyp argPoison argPred bodyState result cursor fuel hloc
            (fun m hm e c r htc => typecheck_nextLoc_mono c e m r htc)
            happly⟩)
      (hbaseTag := Nat.le_refl _) (hbaseLoc := Nat.le_refl _) hthread hmem with
    ⟨first, hfirst_mem, cursor, hcursorTag, hcursorLoc, happly⟩
  exact ⟨cursor, first, hcursorTag, hcursorLoc, hfirst_mem, happly⟩

private lemma updateMemEnv_contains_of_contains_local
    (env : MemoryTypeEnv) (l l' : Loc) (qt : QTyp)
    (h : env.contains l' = true) :
    (updateMemEnv env l qt).contains l' = true := by
  by_cases hEq : l' = l
  · subst hEq
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert]
  · have hCmp : compare l l' ≠ Ordering.eq := by
      intro hce
      have : l = l' := (Nat.compare_eq_eq).1 hce
      exact hEq this.symm
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert, h]

private lemma list_fold_updateMemEnv_contains_of_contains_local
    (xs : List Loc) (env : MemoryTypeEnv) (l' : Loc) (qt : QTyp)
    (h : env.contains l' = true) :
    (xs.foldl (fun acc l => updateMemEnv acc l qt) env).contains l' = true := by
  induction xs generalizing env with
  | nil => simpa using h
  | cons x xs ih =>
      have h1 : (updateMemEnv env x qt).contains l' = true :=
        updateMemEnv_contains_of_contains_local env x l' qt h
      exact ih (env := updateMemEnv env x qt) h1

private lemma applyFnTClosureAtCursor_extern_mem_contains_preserved
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (cursor : Tag × Loc) (fuel : Nat)
  (id : ExternId) (x : Name) (retSpec : ExternReturn)
  (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult)
  (happly :
    applyFnTClosureAtCursor (FnTClosure.extern id x retSpec effects capturedEnv)
      st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor fuel = .ok r) :
  ∀ l, result2.memEnv'.contains l → r.memEnv'.contains l := by
  cases fuel with
  | zero =>
      unfold applyFnTClosureAtCursor at happly
      simp at happly
  | succ fuel =>
      intro l hl
      unfold applyFnTClosureAtCursor at happly
      simp only [applyExternEffect, bind, Except.bind, pure, Except.pure] at happly
      split at happly
      · simp at happly
      · rename_i tagInfo _
        rw [List.forIn_eq_foldlM] at happly
        simp only [Functor.map, Except.map] at happly
        split at happly
        · simp at happly
        · rename_i foldResult hfoldOuter
          split at hfoldOuter
          · simp at hfoldOuter
          · rename_i foldStep hfoldStep
            simp only [Except.ok.injEq] at hfoldOuter
            have hContains : foldResult.contains l = true := by
              rw [← hfoldOuter]
              apply List.foldlM_Except_preserves_property effects (ForInStep.yield result2.memEnv') _
                (fun s => (ForInStep.value s).contains l = true) hl ?_ foldStep hfoldStep
              intro acc effect hP
              cases acc with
              | done b =>
                  intro acc' hg
                  simp only [pure, Except.pure, Except.ok.injEq] at hg
                  exact hg ▸ hP
              | yield b =>
                  intro acc' hg
                  simp only [] at hg
                  split at hg
                  · simp at hg
                  · rename_i v happlyEffect
                    simp only [Except.ok.injEq] at hg
                    subst hg
                    simp only [ForInStep.value]
                    split at happlyEffect
                    · rename_i qt _hlookup
                      split at happlyEffect
                      · rename_i ls _hls
                        split at happlyEffect
                        · exact absurd happlyEffect (by simp)
                        · rename_i v' _hresolve
                          simp only [Except.ok.injEq] at happlyEffect
                          subst happlyEffect
                          unfold LocSet.fold
                          rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                          exact list_fold_updateMemEnv_contains_of_contains_local _ b l _ hP
                      · exact absurd happlyEffect (by simp)
                    · exact absurd happlyEffect (by simp)
            split at happly
            · split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · simp only [Except.ok.injEq] at happly
                  cases happly
                  exact hContains
            · simp only [Except.ok.injEq] at happly
              cases happly
              exact hContains
            · simp only [Except.ok.injEq] at happly
              cases happly
              exact hContains

private lemma applyFnTClosure_staticSource_of_threaded_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (id : ExternId) (x y : Name) (argTyp : Typ)
  (retSpec : ExternReturn) (effects : List Effect) (tenv : CapturedVarEnv)
  (hthread :
    applyClosuresThreaded
      (fun tcl' cursor =>
        applyFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      tcls (bodyState.nextTag', bodyState.nextLoc') = .ok results)
  (hsource :
    ExternCallBoundaryFnStaticSource tcls id x y argTyp retSpec effects tenv) :
  ∃ (cursor : Tag × Loc) (first : TypeResult),
    bodyState.nextTag' ≤ cursor.1 ∧
    bodyState.nextLoc' ≤ cursor.2 ∧
    first ∈ results := by
  cases hsource with
  | externMember hmem =>
      rcases applyFnTClosure_extern_of_threaded_mem
          ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel
          tcls results id x retSpec effects tenv hthread hmem with
        ⟨cursor, first, htag, hloc, hfirst, _happly⟩
      exact ⟨cursor, first, htag, hloc, hfirst⟩
  | regularExternBody hmem =>
      rcases applyFnTClosure_regular_inv_of_threaded_mem
          ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel
          tcls results x (Expr.externFn id y argTyp retSpec effects) tenv
          hthread hmem with
        ⟨cursor, _fuelBody, first, _result3, htag, hloc, hfirst, _happly,
          _hfuel, _htcBody, _hsub, _hfirstEq⟩
      exact ⟨cursor, first, htag, hloc, hfirst⟩

private lemma applyPFnTClosure_staticSource_of_threaded_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (id : ExternId) (x y : Name) (argTyp : Typ)
  (retSpec : ExternReturn) (tenv : CapturedVarEnv)
  (hthread :
    applyClosuresThreaded
      (fun tcl' cursor =>
        applyPFnTClosureAtCursor tcl' st1 st2 p p1 argEtyp argPoison argPred
          ctx bodyState cursor fuel)
      tcls (bodyState.nextTag', bodyState.nextLoc') = .ok results)
  (hsource :
    ExternCallBoundaryPfnStaticSource tcls id x y argTyp retSpec tenv) :
  ∃ (cursor : Tag × Loc) (first : TypeResult),
    bodyState.nextTag' ≤ cursor.1 ∧
    bodyState.nextLoc' ≤ cursor.2 ∧
    first ∈ results := by
  cases hsource with
  | externMember hmem =>
      rcases applyPFnTClosure_extern_of_threaded_mem
          ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel
          tcls results id x retSpec tenv hthread hmem with
        ⟨cursor, first, htag, hloc, hfirst, _happly⟩
      exact ⟨cursor, first, htag, hloc, hfirst⟩

private def AppUserOnlyShape
    (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) : Prop :=
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr)
        (env : VarEnv) (evalConfig : Config),
        terminatesTo e₂ c₀ c₂' v₂ ∧
        terminatesTo e₁ c₂' c₁ (Value.closure x body env) ∧
        (∀ id y argTyp retSpec eff, body ≠ Expr.externFn id y argTyp retSpec eff) ∧
        c₁.pureMode = false ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := false }
        evalConfig v ∧
      c₂ = ({ c₁ with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := c₁.pureMode } : Config) ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode) ∨
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr)
        (env : VarEnv) (evalConfig : Config),
      terminatesTo e₂ c₀ c₂' v₂ ∧
      terminatesTo e₁ c₂' c₁ (Value.peClosure x body env) ∧
      Expr.toPExpr? body ≠ none ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := true }
        evalConfig v ∧
      c₂ = c₁ ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode)

/-- Body-local boundary-run contract for the side-0 impure extern arm. -/
private def ExternCallBoundaryFRFnSide0Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (_hpredlaws : PredSatLaws predSat tm)
    (_hExtTyping : ExternTypingAssumptions)
    (_hwfTm : wfTagMeaningCtx tm ctxᵢ)
    (_hTmBounded : TagMeaningBounded tm ctxᵢ.nextTag)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (_hθ₀ : wfRealizationMap θ₀)
    (_hθ₁ : wfRealizationMap θ₁)
    (_hwf : wfTypeContext ctxᵢ)
    (_htagBounded : TagBoundedCtx ctxᵢ)
    (_hric₀ : runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ θ₀)
    (_hric₁ : runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ θ₁)
    (_htagR : regimeConsistentWithCtx ctxᵢ)
    (_hcwr₀ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀)
    (_hcwr₁ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₁ ρ₁ θ₁)
    (_hagree : agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
    (a₀ a₁ : Address) (pm : Bool)
    (_hwfcfg₀ :
      wfConfig
        ({ memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
           registry := registry } : Config))
    (_hwfcfg₁ :
      wfConfig
        ({ memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
           registry := registry } : Config))
    (_ht₀ : terminatesTo (Expr.app e1 e2)
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } cf₀ o₀)
    (_ht₁ : terminatesTo (Expr.app e1 e2)
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } cf₁ o₁)
    (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂'₀ : Config) (v₂₀ : Value) (c₁₀ : Config)
    (id₀ : ExternId) (x₀ y₀ : Name) (argTyp₀ : Typ) (retSpec₀ : ExternReturn)
    (eff₀ : List Effect) (tenv₀ : CapturedVarEnv)
    (env₀ : VarEnv)
    (impl₀ : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address))
    (vRaw₀ : Value) (mem'₀ : Memory) (addr'₀ : Address),
    ExternCallBoundaryFnStaticSource tcls id₀ x₀ y₀ argTyp₀ retSpec₀ eff₀ tenv₀ →
    terminatesTo e2
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } c₂'₀ v₂₀ →
    terminatesTo e1 c₂'₀ c₁₀
      (Value.closure x₀ (Expr.externFn id₀ y₀ argTyp₀ retSpec₀ eff₀) env₀) →
    c₁₀.pureMode = false →
    c₁₀.registry.get? id₀ = some (ExternImpl.fn impl₀) →
    valueMatchesTyp v₂₀ argTyp₀ = true →
    impl₀ (VarEnv.update env₀ x₀ v₂₀) v₂₀ c₁₀.memory c₁₀.nextAddr =
      Except.ok (vRaw₀, mem'₀, addr'₀) →
    validateExternReturn id₀ retSpec₀ vRaw₀ = Except.ok o₀ →
    (cf₀ =
      { memory := mem'₀, varEnv := c₁₀.varEnv, nextAddr := addr'₀,
        pureMode := c₁₀.pureMode, registry := c₁₀.registry }) →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁₀ →
    callEntry.argName = x₀ →
    callEntry.argValue = v₂₀ →
    callEntry.capturedEnv = env₀ →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ∃ entry : TrustedExternEntry,
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf₀ o₀

/-- Empty-registry discharge for the side-0 two-run extern-call contract. -/
private theorem ExternCallBoundaryFRFnSide0Contract.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure} :
    ExternCallBoundaryFRFnSide0Contract ctxᵢ predSat tm e1 e2 res tcls := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded
        μ₀ _μ₁ ρ₀ _ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree a₀ _a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx _result3 _callEntry
        c₂'₀ v₂₀ c₁₀ id₀ x₀ y₀ argTyp₀ retSpec₀ eff₀
        _tenv₀ _env₀ _impl₀ _vRaw₀ _mem'₀ _addr'₀ _hstatic₀
        ht₀_e2 ht₀_e1 _hpure₀ hGet₀ _hArg₀ _hImpl₀ _hValRet₀ _heq_cfg₀
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂'₀ : c₂'₀.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht₀_e2
  have hreg_c₁₀ : c₁₀.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
  rw [hreg_c₁₀] at hGet₀
  simp [emptyExternRegistry] at hGet₀

/-- Provider-shaped adapter for the future registry lookup: a static
    static source of the arrow closure list produces the side-0 boundary
    contract.  The empty-registry instance below ignores the key, but populated
    instances should use `FnTClosure.extern` membership or regular extern-body
    program membership to look up the matching per-id boundary spec. -/
private def ExternCallBoundaryFRFnSide0Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₀ : ExternId} {x₀ y₀ : Name} {argTyp₀ : Typ}
    {retSpec₀ : ExternReturn} {eff₀ : List Effect}
    {tenv₀ : CapturedVarEnv},
    ExternCallBoundaryFnStaticSource tcls id₀ x₀ y₀ argTyp₀ retSpec₀ eff₀ tenv₀ →
    ExternCallBoundaryFRFnSide0Contract ctxᵢ predSat tm e1 e2 res tcls
      (registry := registry)

/-- Empty-registry provider: any static extern member maps to the vacuous
    side-0 boundary contract. -/
private theorem ExternCallBoundaryFRFnSide0Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure} :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _retSpec₀ _eff₀ _tenv₀ _hstatic
  exact ExternCallBoundaryFRFnSide0Contract.of_emptyExternRegistry

private theorem ExternCallBoundaryFRFnSide0Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    (hregularExternBody :
      ∀ {argTyp : Typ} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv},
        FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
        ∃ entry,
          TrustedRegistry.lookup? tr id = some entry ∧
          TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _retSpec₀ _eff₀ _tenv₀ _hstaticProvider
        _hpredlaws _hExtTyping _hwfTm _hTmBounded
        μ₀ _μ₁ ρ₀ _ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree a₀ _a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx result3 callEntry
        c₂'₀ v₂₀ c₁₀ id₀ x₀ y₀ argTyp₀ retSpec₀ eff₀
        tenv₀ env₀ impl₀ vRaw₀ mem'₀ addr'₀ hstatic₀
        ht₀_e2 ht₀_e1 hpure₀ hGet₀ hArg₀ hImpl₀ hValRet₀ heq_cfg₀
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
  have hreg_c₂'₀ : c₂'₀.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht₀_e2
  have hreg_c₁₀ : c₁₀.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁₀
  have hpureCall : callEntry.callConfig.pureMode = false := by
    rw [hcallCfg]
    exact hpure₀
  have hGetCall :
      callEntry.callConfig.registry.get? id₀ = some (ExternImpl.fn impl₀) := by
    rw [hcallCfg]
    exact hGet₀
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp₀ = true := by
    rw [hargValue]
    exact hArg₀
  have hImplCall :
      impl₀ callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw₀, mem'₀, addr'₀) := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl₀
  have hcfgCall :
      _cf₀ = { callEntry.callConfig with memory := mem'₀, nextAddr := addr'₀ } := by
    simpa [hcallCfg] using heq_cfg₀
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp₀) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp₀))
      (hregularExternBody (argTyp := argTyp₀))
      (id := id₀) (x := x₀) (y := y₀) (retSpec := retSpec₀)
      (effects := eff₀) (capturedEnv := tenv₀)
      hstatic₀ hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet₀ hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  exact ⟨entry, hrun⟩

/-- Body-local boundary-run contract for the side-1 impure extern arm. -/
private def ExternCallBoundaryFRFnSide1Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (_hpredlaws : PredSatLaws predSat tm)
    (_hExtTyping : ExternTypingAssumptions)
    (_hwfTm : wfTagMeaningCtx tm ctxᵢ)
    (_hTmBounded : TagMeaningBounded tm ctxᵢ.nextTag)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (_hθ₀ : wfRealizationMap θ₀)
    (_hθ₁ : wfRealizationMap θ₁)
    (_hwf : wfTypeContext ctxᵢ)
    (_htagBounded : TagBoundedCtx ctxᵢ)
    (_hric₀ : runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ θ₀)
    (_hric₁ : runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ θ₁)
    (_htagR : regimeConsistentWithCtx ctxᵢ)
    (_hcwr₀ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀)
    (_hcwr₁ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₁ ρ₁ θ₁)
    (_hagree : agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
    (a₀ a₁ : Address) (pm : Bool)
    (_hwfcfg₀ :
      wfConfig
        ({ memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
           registry := registry } : Config))
    (_hwfcfg₁ :
      wfConfig
        ({ memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
           registry := registry } : Config))
    (_ht₀ : terminatesTo (Expr.app e1 e2)
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } cf₀ o₀)
    (_ht₁ : terminatesTo (Expr.app e1 e2)
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } cf₁ o₁)
    (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂'₁ : Config) (v₂₁ : Value) (c₁₁ : Config)
    (id₁ : ExternId) (x₁ y₁ : Name) (argTyp₁ : Typ) (retSpec₁ : ExternReturn)
    (eff₁ : List Effect) (tenv₁ : CapturedVarEnv)
    (env₁ : VarEnv)
    (impl₁ : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address))
    (vRaw₁ : Value) (mem'₁ : Memory) (addr'₁ : Address),
    ExternCallBoundaryFnStaticSource tcls id₁ x₁ y₁ argTyp₁ retSpec₁ eff₁ tenv₁ →
    terminatesTo e2
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } c₂'₁ v₂₁ →
    terminatesTo e1 c₂'₁ c₁₁
      (Value.closure x₁ (Expr.externFn id₁ y₁ argTyp₁ retSpec₁ eff₁) env₁) →
    c₁₁.pureMode = false →
    c₁₁.registry.get? id₁ = some (ExternImpl.fn impl₁) →
    valueMatchesTyp v₂₁ argTyp₁ = true →
    impl₁ (VarEnv.update env₁ x₁ v₂₁) v₂₁ c₁₁.memory c₁₁.nextAddr =
      Except.ok (vRaw₁, mem'₁, addr'₁) →
    validateExternReturn id₁ retSpec₁ vRaw₁ = Except.ok o₁ →
    (cf₁ =
      { memory := mem'₁, varEnv := c₁₁.varEnv, nextAddr := addr'₁,
        pureMode := c₁₁.pureMode, registry := c₁₁.registry }) →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁₁ →
    callEntry.argName = x₁ →
    callEntry.argValue = v₂₁ →
    callEntry.capturedEnv = env₁ →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ∃ entry : TrustedExternEntry,
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf₁ o₁

/-- Empty-registry discharge for the side-1 two-run extern-call contract. -/
private theorem ExternCallBoundaryFRFnSide1Contract.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure} :
    ExternCallBoundaryFRFnSide1Contract ctxᵢ predSat tm e1 e2 res tcls := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded
        _μ₀ μ₁ _ρ₀ ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree _a₀ a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx _result3 _callEntry
        c₂'₁ v₂₁ c₁₁ id₁ x₁ y₁ argTyp₁ retSpec₁ eff₁
        _tenv₁ _env₁ _impl₁ _vRaw₁ _mem'₁ _addr'₁ _hstatic₁
        ht₁_e2 ht₁_e1 _hpure₁ hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _heq_cfg₁
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂'₁ : c₂'₁.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht₁_e2
  have hreg_c₁₁ : c₁₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
  rw [hreg_c₁₁] at hGet₁
  simp [emptyExternRegistry] at hGet₁

/-- Provider-shaped adapter for side 1, mirroring
    `ExternCallBoundaryFRFnSide0Provider`. -/
private def ExternCallBoundaryFRFnSide1Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₁ : ExternId} {x₁ y₁ : Name} {argTyp₁ : Typ}
    {retSpec₁ : ExternReturn} {eff₁ : List Effect}
    {tenv₁ : CapturedVarEnv},
    ExternCallBoundaryFnStaticSource tcls id₁ x₁ y₁ argTyp₁ retSpec₁ eff₁ tenv₁ →
    ExternCallBoundaryFRFnSide1Contract ctxᵢ predSat tm e1 e2 res tcls
      (registry := registry)

/-- Empty-registry provider: any static extern member maps to the vacuous
    side-1 boundary contract. -/
private theorem ExternCallBoundaryFRFnSide1Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure} :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _retSpec₁ _eff₁ _tenv₁ _hstatic
  exact ExternCallBoundaryFRFnSide1Contract.of_emptyExternRegistry

private theorem ExternCallBoundaryFRFnSide1Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    (hregularExternBody :
      ∀ {argTyp : Typ} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv},
        FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
        ∃ entry,
          TrustedRegistry.lookup? tr id = some entry ∧
          TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _retSpec₁ _eff₁ _tenv₁ _hstaticProvider
        _hpredlaws _hExtTyping _hwfTm _hTmBounded
        _μ₀ μ₁ _ρ₀ ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree _a₀ a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx result3 callEntry
        c₂'₁ v₂₁ c₁₁ id₁ x₁ y₁ argTyp₁ retSpec₁ eff₁
        tenv₁ env₁ impl₁ vRaw₁ mem'₁ addr'₁ hstatic₁
        ht₁_e2 ht₁_e1 hpure₁ hGet₁ hArg₁ hImpl₁ hValRet₁ heq_cfg₁
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
  have hreg_c₂'₁ : c₂'₁.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht₁_e2
  have hreg_c₁₁ : c₁₁.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁₁
  have hpureCall : callEntry.callConfig.pureMode = false := by
    rw [hcallCfg]
    exact hpure₁
  have hGetCall :
      callEntry.callConfig.registry.get? id₁ = some (ExternImpl.fn impl₁) := by
    rw [hcallCfg]
    exact hGet₁
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp₁ = true := by
    rw [hargValue]
    exact hArg₁
  have hImplCall :
      impl₁ callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw₁, mem'₁, addr'₁) := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl₁
  have hcfgCall :
      _cf₁ = { callEntry.callConfig with memory := mem'₁, nextAddr := addr'₁ } := by
    simpa [hcallCfg] using heq_cfg₁
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp₁) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp₁))
      (hregularExternBody (argTyp := argTyp₁))
      (id := id₁) (x := x₁) (y := y₁) (retSpec := retSpec₁)
      (effects := eff₁) (capturedEnv := tenv₁)
      hstatic₁ hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet₁ hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  exact ⟨entry, hrun⟩

/-- Body-local boundary-run contract for the side-0 pure extern arm. -/
private def ExternCallBoundaryFRPfnSide0Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (_hpredlaws : PredSatLaws predSat tm)
    (_hExtTyping : ExternTypingAssumptions)
    (_hwfTm : wfTagMeaningCtx tm ctxᵢ)
    (_hTmBounded : TagMeaningBounded tm ctxᵢ.nextTag)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (_hθ₀ : wfRealizationMap θ₀)
    (_hθ₁ : wfRealizationMap θ₁)
    (_hwf : wfTypeContext ctxᵢ)
    (_htagBounded : TagBoundedCtx ctxᵢ)
    (_hric₀ : runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ θ₀)
    (_hric₁ : runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ θ₁)
    (_htagR : regimeConsistentWithCtx ctxᵢ)
    (_hcwr₀ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀)
    (_hcwr₁ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₁ ρ₁ θ₁)
    (_hagree : agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
    (a₀ a₁ : Address) (pm : Bool)
    (_hwfcfg₀ :
      wfConfig
        ({ memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
           registry := registry } : Config))
    (_hwfcfg₁ :
      wfConfig
        ({ memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
           registry := registry } : Config))
    (_ht₀ : terminatesTo (Expr.app e1 e2)
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } cf₀ o₀)
    (_ht₁ : terminatesTo (Expr.app e1 e2)
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } cf₁ o₁)
    (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂'₀ : Config) (v₂₀ : Value) (c₁₀ : Config)
    (id₀ : ExternId) (x₀ y₀ : Name) (argTyp₀ : Typ) (retSpec₀ : ExternReturn)
    (tenv₀ : CapturedVarEnv) (env₀ : VarEnv)
    (impl₀ : VarEnv → Value → Memory → Except ExternError Value)
    (vRaw₀ : Value),
    ExternCallBoundaryPfnStaticSource tcls id₀ x₀ y₀ argTyp₀ retSpec₀ tenv₀ →
    terminatesTo e2
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } c₂'₀ v₂₀ →
    terminatesTo e1 c₂'₀ c₁₀
      (Value.peClosure x₀ (Expr.externPfn id₀ y₀ argTyp₀ retSpec₀) env₀) →
    c₁₀.registry.get? id₀ = some (ExternImpl.pfn impl₀) →
    valueMatchesTyp v₂₀ argTyp₀ = true →
    impl₀ (VarEnv.update env₀ x₀ v₂₀) v₂₀ c₁₀.memory = Except.ok vRaw₀ →
    validateExternReturn id₀ retSpec₀ vRaw₀ = Except.ok o₀ →
    cf₀ = c₁₀ →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁₀ →
    callEntry.argName = x₀ →
    callEntry.argValue = v₂₀ →
    callEntry.capturedEnv = env₀ →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ∃ entry : TrustedExternEntry,
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf₀ o₀

private theorem ExternCallBoundaryFRPfnSide0Contract.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure} :
    ExternCallBoundaryFRPfnSide0Contract ctxᵢ predSat tm e1 e2 res tcls := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded
        μ₀ _μ₁ ρ₀ _ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree a₀ _a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx _result3 _callEntry
        c₂'₀ v₂₀ c₁₀ id₀ x₀ y₀ argTyp₀ retSpec₀
        _tenv₀ _env₀ _impl₀ _vRaw₀ _hstatic₀ ht₀_e2 ht₀_e1
        hGet₀ _hArg₀ _hImpl₀ _hValRet₀ _heq_cfg₀
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂'₀ : c₂'₀.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht₀_e2
  have hreg_c₁₀ : c₁₀.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
  rw [hreg_c₁₀] at hGet₀
  simp [emptyExternRegistry] at hGet₀

private def ExternCallBoundaryFRPfnSide0Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₀ : ExternId} {x₀ y₀ : Name} {argTyp₀ : Typ}
    {retSpec₀ : ExternReturn} {tenv₀ : CapturedVarEnv},
    ExternCallBoundaryPfnStaticSource tcls id₀ x₀ y₀ argTyp₀ retSpec₀ tenv₀ →
    ExternCallBoundaryFRPfnSide0Contract ctxᵢ predSat tm e1 e2 res tcls
      (registry := registry)

private theorem ExternCallBoundaryFRPfnSide0Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure} :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _retSpec₀ _tenv₀ _hstatic
  exact ExternCallBoundaryFRPfnSide0Contract.of_emptyExternRegistry

private theorem ExternCallBoundaryFRPfnSide0Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _retSpec₀ _tenv₀ _hstaticProvider
        _hpredlaws _hExtTyping _hwfTm _hTmBounded
        μ₀ _μ₁ ρ₀ _ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree a₀ _a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx result3 callEntry
        c₂'₀ v₂₀ c₁₀ id₀ x₀ y₀ argTyp₀ retSpec₀
        tenv₀ env₀ impl₀ vRaw₀ hstatic₀ ht₀_e2 ht₀_e1
        hGet₀ hArg₀ hImpl₀ hValRet₀ heq_cfg₀
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
  have hreg_c₂'₀ : c₂'₀.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht₀_e2
  have hreg_c₁₀ : c₁₀.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁₀
  have hGetCall :
      callEntry.callConfig.registry.get? id₀ = some (ExternImpl.pfn impl₀) := by
    rw [hcallCfg]
    exact hGet₀
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp₀ = true := by
    rw [hargValue]
    exact hArg₀
  have hImplCall :
      impl₀ callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw₀ := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl₀
  have hcfgCall : _cf₀ = callEntry.callConfig := by
    simpa [hcallCfg] using heq_cfg₀
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp₀) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp₀))
      (id := id₀) (x := x₀) (y := y₀) (retSpec := retSpec₀)
      (capturedEnv := tenv₀)
      hstatic₀ hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet₀ hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  exact ⟨entry, hrun⟩

/-- Body-local boundary-run contract for the side-1 pure extern arm. -/
private def ExternCallBoundaryFRPfnSide1Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (_hpredlaws : PredSatLaws predSat tm)
    (_hExtTyping : ExternTypingAssumptions)
    (_hwfTm : wfTagMeaningCtx tm ctxᵢ)
    (_hTmBounded : TagMeaningBounded tm ctxᵢ.nextTag)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (_hθ₀ : wfRealizationMap θ₀)
    (_hθ₁ : wfRealizationMap θ₁)
    (_hwf : wfTypeContext ctxᵢ)
    (_htagBounded : TagBoundedCtx ctxᵢ)
    (_hric₀ : runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ θ₀)
    (_hric₁ : runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ θ₁)
    (_htagR : regimeConsistentWithCtx ctxᵢ)
    (_hcwr₀ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀)
    (_hcwr₁ : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ₁ ρ₁ θ₁)
    (_hagree : agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
    (a₀ a₁ : Address) (pm : Bool)
    (_hwfcfg₀ :
      wfConfig
        ({ memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
           registry := registry } : Config))
    (_hwfcfg₁ :
      wfConfig
        ({ memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
           registry := registry } : Config))
    (_ht₀ : terminatesTo (Expr.app e1 e2)
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
        registry := registry } cf₀ o₀)
    (_ht₁ : terminatesTo (Expr.app e1 e2)
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } cf₁ o₁)
    (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂'₁ : Config) (v₂₁ : Value) (c₁₁ : Config)
    (id₁ : ExternId) (x₁ y₁ : Name) (argTyp₁ : Typ) (retSpec₁ : ExternReturn)
    (tenv₁ : CapturedVarEnv) (env₁ : VarEnv)
    (impl₁ : VarEnv → Value → Memory → Except ExternError Value)
    (vRaw₁ : Value),
    ExternCallBoundaryPfnStaticSource tcls id₁ x₁ y₁ argTyp₁ retSpec₁ tenv₁ →
    terminatesTo e2
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
        registry := registry } c₂'₁ v₂₁ →
    terminatesTo e1 c₂'₁ c₁₁
      (Value.peClosure x₁ (Expr.externPfn id₁ y₁ argTyp₁ retSpec₁) env₁) →
    c₁₁.registry.get? id₁ = some (ExternImpl.pfn impl₁) →
    valueMatchesTyp v₂₁ argTyp₁ = true →
    impl₁ (VarEnv.update env₁ x₁ v₂₁) v₂₁ c₁₁.memory = Except.ok vRaw₁ →
    validateExternReturn id₁ retSpec₁ vRaw₁ = Except.ok o₁ →
    cf₁ = c₁₁ →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁₁ →
    callEntry.argName = x₁ →
    callEntry.argValue = v₂₁ →
    callEntry.capturedEnv = env₁ →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ∃ entry : TrustedExternEntry,
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf₁ o₁

private theorem ExternCallBoundaryFRPfnSide1Contract.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure} :
    ExternCallBoundaryFRPfnSide1Contract ctxᵢ predSat tm e1 e2 res tcls := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded
        _μ₀ μ₁ _ρ₀ ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree _a₀ a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx _result3 _callEntry
        c₂'₁ v₂₁ c₁₁ id₁ x₁ y₁ argTyp₁ retSpec₁
        _tenv₁ _env₁ _impl₁ _vRaw₁ _hstatic₁ ht₁_e2 ht₁_e1
        hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _heq_cfg₁
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂'₁ : c₂'₁.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht₁_e2
  have hreg_c₁₁ : c₁₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
  rw [hreg_c₁₁] at hGet₁
  simp [emptyExternRegistry] at hGet₁

private def ExternCallBoundaryFRPfnSide1Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₁ : ExternId} {x₁ y₁ : Name} {argTyp₁ : Typ}
    {retSpec₁ : ExternReturn} {tenv₁ : CapturedVarEnv},
    ExternCallBoundaryPfnStaticSource tcls id₁ x₁ y₁ argTyp₁ retSpec₁ tenv₁ →
    ExternCallBoundaryFRPfnSide1Contract ctxᵢ predSat tm e1 e2 res tcls
      (registry := registry)

private theorem ExternCallBoundaryFRPfnSide1Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure} :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _retSpec₁ _tenv₁ _hstatic
  exact ExternCallBoundaryFRPfnSide1Contract.of_emptyExternRegistry

private theorem ExternCallBoundaryFRPfnSide1Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _retSpec₁ _tenv₁ _hstaticProvider
        _hpredlaws _hExtTyping _hwfTm _hTmBounded
        _μ₀ μ₁ _ρ₀ ρ₁ _θ₀ _θ₁ _cf₀ _cf₁ _o₀ _o₁
        _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _htagR
        _hcwr₀ _hcwr₁ _hagree _a₀ a₁ pm _hwfcfg₀ _hwfcfg₁
        _ht₀ _ht₁ _bodyCtx result3 callEntry
        c₂'₁ v₂₁ c₁₁ id₁ x₁ y₁ argTyp₁ retSpec₁
        tenv₁ env₁ impl₁ vRaw₁ hstatic₁ ht₁_e2 ht₁_e1
        hGet₁ hArg₁ hImpl₁ hValRet₁ heq_cfg₁
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
  have hreg_c₂'₁ : c₂'₁.registry = TrustedRegistry.toRuntimeRegistry tr := by
    simpa using terminatesTo_preserves_registry ht₁_e2
  have hreg_c₁₁ : c₁₁.registry = TrustedRegistry.toRuntimeRegistry tr :=
    (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
  have hregistryCall :
      callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr := by
    rw [hcallCfg]
    exact hreg_c₁₁
  have hGetCall :
      callEntry.callConfig.registry.get? id₁ = some (ExternImpl.pfn impl₁) := by
    rw [hcallCfg]
    exact hGet₁
  have hArgCall : valueMatchesTyp callEntry.argValue argTyp₁ = true := by
    rw [hargValue]
    exact hArg₁
  have hImplCall :
      impl₁ callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw₁ := by
    rw [hunified, hcaptured, hargName, hargValue, hcallCfg]
    exact hImpl₁
  have hcfgCall : _cf₁ = callEntry.callConfig := by
    simpa [hcallCfg] using heq_cfg₁
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun
      (tr := tr) (argTyp := argTyp₁) (tcls := tcls)
      (hagreesExtern (argTyp := argTyp₁))
      (id := id₁) (x := x₁) (y := y₁) (retSpec := retSpec₁)
      (capturedEnv := tenv₁)
      hstatic₁ hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet₁ hcfgCall with
    ⟨entry, _hlookup, hrun⟩
  exact ⟨entry, hrun⟩

/-- Local registry-agreement-shaped adapter for the two impure arrow sides.

    This is intentionally local to the empty-registry proof.  It keeps the same
    indexed-provider shape that a future trusted-registry lookup should provide,
    but the providers now produce body-local boundary-run evidence rather than
    the final app post. -/
private def TrustedRegistryAgreesWithProgramLocal
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls
    (registry := registry) ∧
  ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls
    (registry := registry)

/-- Empty-registry local agreement: every static extern member maps to the
    corresponding vacuous body-local side contract. -/
private theorem TrustedRegistryAgreesWithProgramLocal.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure} :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_emptyExternRegistry,
   ExternCallBoundaryFRFnSide1Provider.of_emptyExternRegistry⟩

private theorem TrustedRegistryAgreesWithProgramLocal.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    (hregularExternBody :
      ∀ {argTyp : Typ} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv},
        FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
        ∃ entry,
          TrustedRegistry.lookup? tr id = some entry ∧
          TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_trustedRegistry
      hagreesExtern hregularExternBody,
   ExternCallBoundaryFRFnSide1Provider.of_trustedRegistry
      hagreesExtern hregularExternBody⟩

/-- Local trusted-registry adapter for the two pure extern parrow sides. -/
private def TrustedRegistryAgreesWithPfnProgramLocal
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List PFnTClosure)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls
    (registry := registry) ∧
  ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls
    (registry := registry)

private theorem TrustedRegistryAgreesWithPfnProgramLocal.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure} :
    TrustedRegistryAgreesWithPfnProgramLocal ctxᵢ predSat tm e1 e2 res tcls :=
  ⟨ExternCallBoundaryFRPfnSide0Provider.of_emptyExternRegistry,
   ExternCallBoundaryFRPfnSide1Provider.of_emptyExternRegistry⟩

private theorem TrustedRegistryAgreesWithPfnProgramLocal.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    TrustedRegistryAgreesWithPfnProgramLocal ctxᵢ predSat tm e1 e2 res tcls
      (registry := TrustedRegistry.toRuntimeRegistry tr) :=
  ⟨ExternCallBoundaryFRPfnSide0Provider.of_trustedRegistry hagreesExtern,
   ExternCallBoundaryFRPfnSide1Provider.of_trustedRegistry hagreesExtern⟩

private lemma stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (_ctxExternBodyStart :
    AppExternClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (_ctxConsOfRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      consistentWithRegime predSat ctx.regime ctx μ ρ θ →
      CtxCons ctx μ ρ θ)
  (_valConsOfRegular :
    ∀ {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value},
      valueConsistentWithRegime predSat R qt μ θ v →
      ValCons R qt μ θ v)
  (_ctxConsToRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      (∀ k, masked k → ctx.regime.lookup? k = none) →
      CtxCons ctx μ ρ θ →
      consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  -- Probe 2 spike: contract-shaped hypothesis for the `closure_extern` arm.
  -- See `doc/probe2-plan.md`.  Discharged at the caller via the empty-registry
  -- vacuity argument bundled in `ExternCallBoundarySingleFnContract.of_emptyExternRegistry`.
  (_extCallSpec :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel')) masked CtxCons ValCons)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmap :
    applyClosuresThreaded
      (fun tcl cursor =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
          ctxᵢ result1 cursor fuel')
      tcls (result1.nextTag', result1.nextLoc') = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res)
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves hExtTyping predSat tm ctxᵢ
        (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm hTmBounded result2 htc2'
  have hIH_e2_inst := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
  rcases hIH_e2_inst.1 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hTm2⟩
  have hstruct := terminatesTo_app_inv_full e1 e2 cinit cf o ht
  cases hstruct with
  | @userFn c₂' v₂ c₁ x body env evalCfg ht_e2 ht_e1 _hNotExtern _hpm1
      ht_body heq_cfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have hreg2' : c₂'.registry = emptyExternRegistry := by
      simpa [cinit] using terminatesTo_preserves_registry ht_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [← hpm2]; exact config_eq_of_registry_default c₂' hreg2'
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    have hIH_e1_inst := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
    rcases
      hIH_e1_inst.2
        c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        ((wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1) (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    rcases hIH_e1_inst.1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hTm1⟩
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
    have hmasked_absent1 :
        MaskedTagsAbsentFromTrueTagEnv masked
          (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked (ctxAfter ctxᵢ result2) e1 fuel' result1
        hmasked_absent2 hmasked_none2 htc1'
    have hv₁_arrow : valueHasETyp θ1 (Value.closure x body env) (ETyp.arrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_arrow with
    | closure_extern htcl _henv _hcover =>
        exact False.elim ((notExternFnAst_ne_externFn _hNotExtern) _ _ _ _ _ rfl)
    | closure _ _ _ =>
        obtain ⟨σcap, hσcap_mem, hσcap_typing, hcwr_body_for⟩ :=
          ctxBodyStart
            ctxᵢ result2 result1 etyp2 p2 pred2
            st1 st2 p p1 tcls
            x body c₁.varEnv env
            c₂'.memory c₁.memory θ2 θ1 v₂
              hpredlaws hqt2 hetyp1 hmono1 hθext1
              hcwr1 hvalc2 hvalc1 (notExternFnAst_ne_externFn _hNotExtern)
        rcases applyFnTClosure_regular_inv_of_threaded_mem
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            x body σcap hmap hσcap_mem with
          ⟨cursorA, fuelBody, firstA, result3, hcursorTagA, hcursorLocA, hfirstA_mem,
            happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
        have hfirstA_mem' : firstA ∈ first :: rest := by
          simpa [heq_results] using hfirstA_mem
        let bodyCtx : TypeContext :=
          { ctxᵢ with
            pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            nextTag := cursorA.1
            nextLoc := cursorA.2
            regime := result1.regime' }
        have hcwr_body : CtxCons bodyCtx c₁.memory (env.update x v₂) θ1 := by
          simpa [bodyCtx] using hcwr_body_for cursorA
        have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
          QTypRespectsTagMeaning_transport_etyp_pred
            (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
            (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (hqt2 ▸ QTypRespectsTagMeaning_mono
              (IsCanonicalExtension.extends_tm hcanon1) hresTm2) rfl rfl
        have hTmBody : wfTagMeaningCtx tm1 bodyCtx := by
          simpa [bodyCtx, ctxAfter] using
            wfTagMeaningCtx_closure_body
              (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
              (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
              (p := p) (tcls := tcls)
              (xFun := x) (body := body) (σcap := σcap)
              (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
              hTm1 hresTm1 hetyp1 hσcap_mem hargTm
        have htcBody' : typecheck bodyCtx body fuelBody = .ok result3 := by
          simpa [bodyCtx, typecheck] using htc_bodyA
        have hwfBody : wfTypeContext bodyCtx := by
          simp only [bodyCtx, wfTypeContext]
          have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
            (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
          have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
          exact ⟨(fun l hl =>
              Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA),
              varEnvRefLocsBounded_update
                (varEnvRefLocsBounded_ofCaptured
                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                    (CapturedEnvRefLocsFullBounded_mono
                      (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)
                      hcursorLocA)))
                (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypRefLocsBounded_mono h
                      (Nat.le_trans hmono_e1 hcursorLocA)),
              varEnvClosuresCapturedRefLocsBounded_update
                (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                  (CapturedEnvRefLocsFullBounded_mono
                    (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)
                    hcursorLocA))
                (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                      (Nat.le_trans hmono_e1 hcursorLocA))⟩
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
        have hmasked_absent_body : MaskedTagsAbsentFromTrueTagEnv masked bodyCtx := by
          simpa [bodyCtx, ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent1
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
        have hTmBounded1 : TagMeaningBounded tm1 result1.nextTag' := by
          simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon1
        have hTmBoundedBody : TagMeaningBounded tm1 bodyCtx.nextTag := by
          simpa [bodyCtx] using hTmBounded1.mono hcursorTagA
        have hSingle_body :=
          singleIH fuelBody hfuel_lt body bodyCtx hTmBody hTmBoundedBody result3 htcBody'
        have hpc_body : bodyCtx.pc = true := by
          simp [bodyCtx, hpc, joinPoison]
        -- Thread extern registry: c₂' inherits default from cinit, c₁ from c₂'.
        have hreg_c₁ : c₁.registry = emptyExternRegistry := by
          have h2 : c₂'.registry = emptyExternRegistry := by
            simpa [cinit] using terminatesTo_preserves_registry ht_e2
          exact (terminatesTo_preserves_registry ht_e1).trans h2
        rw [hreg_c₁] at ht_body
        rcases
          (hSingle_body hpredlaws1 hExtTyping hTmBody hTmBoundedBody).2
            c₁.memory (env.update x v₂) θ1 evalCfg o
            hθ1wf hwfBody hric_body htagR_body hmasked_none_body
            hmasked_absent_body hcwr_body
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
              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
          regime_lookup_back_of_monotone hres1_to_firstA_mono
        have hric_final :
            runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
          exact
            appMember_runtimeInstantiatesCtx_from_body
              (ctx := ctxᵢ)
              (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
              (bodyFinalCtx := ctxAfter bodyCtx result3)
              (first := first) (src := firstA) (rest := rest) (res := res)
              (cf := cf) (evalCfg := evalCfg) (preCfg := c₁)
              (θpre := θ1) (θbody := θ_body)
              h_join hfirstA_mem' hric_body_final hric1
              (fun l hcontains_body => by
                simpa [ctxAfter, hfirstA_eq] using hcontains_body)
              (fun y qt hlookup => by
                simpa [ctxAfter] using hlookup)
              hmem_eq hvar_eq hθext_body
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
              typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
                (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                htc_bodyA hwfBody hpc_body l qt1 qt3
                (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
          have hclean2 : qtypCleanUnder result2.regime' qt2 := by
            exact
              typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
                    (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                    htc_bodyA hwfBody hpc_body l qt1 qt3
                    (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
                have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
        have hpred_compat_final :
            ∀ (qt' : QTyp) (v' : Value),
              qtypPredHolds predSat qt' c₁.memory v' ↔ qtypPredHolds predSat qt' cf.memory v' :=
          qtypPredHolds_mem_compat_of_predSatLaws
            (hpredlaws := hpredlaws) (θ := θ1) (μ := c₁.memory) (μ' := cf.memory)
        exact
          appSingleRunMaskedPost_from_body_fields
            (predSat := predSat)
            ctxMember ctxJoinMember valBodyResult valJoinMember
            (ctx := ctxᵢ) (bodyCtx := bodyCtx)
            (result2 := result2) (result1 := result1)
            (first := first) (src := firstA) (result3 := result3)
            (rest := rest) (res := res)
            (μ := μ) (ρ := ρ) (θ := θ) (θpre := θ1) (θbody := θ_body)
            (cf := cf) (evalCfg := evalCfg) (preCfg := c₁)
            (o := o) (p := p) (p1 := p1)
            h_join hfirstA_mem' hfirstA_eq hlookup_back_res1_to_A
            (fun y qt hlookup => by
              simpa [ctxAfter] using hlookup)
            hpred_compat_final hmem_eq hvar_eq
            (wfExtendsMap_trans hθext2 hθext1) hθext_body hv_body_typed
            hric_body_final hric1 hcwr_body_final hcwr1 hvalc_body
            hpres_final hfresh_final
  | @externFn c₂' v₂ c₁ x y id argTyp retSpec eff env impl vRaw mem' addr'
      ht_e2 ht_e1 hpure hGet hArg hImpl hValRet hcfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have hreg2' : c₂'.registry = emptyExternRegistry := by
      simpa [cinit] using terminatesTo_preserves_registry ht_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      rw [← hpm2]
      exact config_eq_of_registry_default c₂' hreg2'
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    have hIH_e1_inst := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
    rcases
      hIH_e1_inst.2
        c₂'.memory c₂'.varEnv θ2 c₁
        (Value.closure x (Expr.externFn id y argTyp retSpec eff) env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        ((wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1) (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _hfresh1⟩
    have hv₁_arrow :
        valueHasETyp _θ1
          (Value.closure x (Expr.externFn id y argTyp retSpec eff) env)
          (ETyp.arrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    exfalso
    have hreg_c₁ : c₁.registry = emptyExternRegistry :=
      (terminatesTo_preserves_registry ht_e1).trans hreg2'
    rw [hreg_c₁] at hGet
    simp [emptyExternRegistry] at hGet
  | @userPfn c₂' v₂ c₁ x body env _evalCfg ht_e2 ht_e1 _hNotExtern _htoPExpr
      _ht_body _hcf hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]; exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    rcases
      (hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2).2
        c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_peClosure_etyp_parrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _ptcls, hparr⟩
    rw [hetyp1] at hparr
    cases hparr
  | @externPfn c₂' v₂ c₁ x y id argTyp retSpec env _impl _vRaw
      ht_e2 ht_e1 _hGet _hArg _hImpl _hValRet _hcfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]
      exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    rcases
      (hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2).2
        c₂'.memory c₂'.varEnv θ2 c₁
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
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
  (_ctxExternBodyStart :
    AppExternPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (_ctxConsOfRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      consistentWithRegime predSat ctx.regime ctx μ ρ θ →
      CtxCons ctx μ ρ θ)
  (_valConsOfRegular :
    ∀ {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value},
      valueConsistentWithRegime predSat R qt μ θ v →
      ValCons R qt μ θ v)
  (_ctxConsToRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      (∀ k, masked k → ctx.regime.lookup? k = none) →
      CtxCons ctx μ ρ θ →
      consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (e1 e2 : Expr) (fuel' : Nat) (res result2 result1 : TypeResult)
  (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate)
  (_extPfnSpec :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls)
  (singleIH :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH
      predSat tm (Nat.succ (Nat.succ fuel')) masked CtxCons ValCons)
  (hqt2 : result2.qualType = ⟨etyp2, p2, pred2⟩)
  (htc2' : typecheck ctxᵢ e2 fuel' = .ok result2)
  (htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1)
  (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure) (results : List TypeResult)
  (first : TypeResult) (rest : List TypeResult)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmap :
    applyClosuresThreaded
      (fun tcl cursor =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
          ctxᵢ result1 cursor fuel')
      tcls (result1.nextTag', result1.nextLoc') = .ok results)
  (heq_results : results = first :: rest)
  (h_join : joinTypeResults ctxᵢ first rest = .ok res)
  (htc : typecheck ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrueMaskedRegParam
    masked CtxCons ValCons ctxᵢ (Expr.app e1 e2) res predSat tm := by
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves hExtTyping predSat tm ctxᵢ
        (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
        hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht hpc
  let cinit : Config := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
  have hIH_e2 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    e2 ctxᵢ hwfTm hTmBounded result2 htc2'
  have hIH_e2_inst := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
  rcases hIH_e2_inst.1 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hTm2⟩
  have hstruct := terminatesTo_app_inv_full e1 e2 cinit cf o ht
  cases hstruct with
  | @userFn c₂' v₂ c₁ x body env _evalCfg ht_e2 ht_e1 _hNotExtern _hpm1
      _ht_body _heq_cfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]; exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    rcases
      (hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2).2
        c₂'.memory c₂'.varEnv θ2 c₁ (Value.closure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_closure_etyp_arrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _tcls, harrow⟩
    rw [hetyp1] at harrow
    cases harrow
  | @externFn c₂' v₂ c₁ x y id argTyp retSpec eff env _impl _vRaw _mem' _addr'
      ht_e2 ht_e1 _hpure _hGet _hArg _hImpl _hValRet _hcfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]
      exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    rcases
      (hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2).2
        c₂'.memory c₂'.varEnv θ2 c₁
        (Value.closure x (Expr.externFn id y argTyp retSpec eff) env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    rcases valueHasETyp_closure_etyp_arrow_inv hv₁_typed with
      ⟨_st1, _st2, _p, _tcls, harrow⟩
    rw [hetyp1] at harrow
    cases harrow
  | @userPfn c₂' v₂ c₁ x body env evalCfg ht_e2 ht_e1 _hNotExtern _htoPExpr_body
      ht_body hcf hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, hv₂_typed, hric2, hcwr2, hvalc2, hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]; exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    have hIH_e1_inst := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
    rcases
      hIH_e1_inst.2
        c₂'.memory c₂'.varEnv θ2 c₁ (Value.peClosure x body env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨θ1, hθext1, hv₁_typed, hric1, hcwr1, hvalc1, hpres1, _hfresh1⟩
    have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθ2wf
    rcases hIH_e1_inst.1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hTm1⟩
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
    have hmasked_absent1 :
        MaskedTagsAbsentFromTrueTagEnv masked
          (ctxAfter (ctxAfter ctxᵢ result2) result1) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked (ctxAfter ctxᵢ result2) e1 fuel' result1
        hmasked_absent2 hmasked_none2 htc1'
    have hv₁_parrow : valueHasETyp θ1 (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    cases hv₁_parrow with
    | peClosure_extern _ _ _ =>
        -- Probe 2 vertical-slice discharge.  The peClosure_extern constructor
        -- forces `body = Expr.externPfn id y argTyp retSpec` for some implicits,
        -- but the user pure-closure branch of full app inversion provides
        -- `_htoPExpr_body : Expr.toPExpr? body ≠ none`.  For extern bodies
        -- `Expr.toPExpr?` returns `none` (`Expr.toPExpr?` falls through to `_ => none`
        -- for `externPfn`), so the precondition is contradictory.
        exact absurd (by simp [Expr.toPExpr?]) _htoPExpr_body
    | peClosure _ _ _ _ =>
        obtain ⟨σcap, pbody, htoPExpr, hσcap_mem, hσcap_typing, hcwr_body_for⟩ :=
          ctxBodyStart
          ctxᵢ result2 result1 etyp2 p2 pred2
          st1 st2 p p1 tcls
            x body cf.varEnv env
            c₂'.memory cf.memory θ2 θ1 v₂
            hpredlaws hqt2 hetyp1 hmono1 hθext1
            (by simpa [hcf] using hcwr1) hvalc2 (by simpa [hcf] using hvalc1)
            _htoPExpr_body
        have hbody_eq : PExpr.toExpr pbody = body :=
          PExpr_toExpr_of_toPExpr?_some body pbody htoPExpr
        rcases applyPFnTClosure_regular_inv_of_threaded_mem
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            x pbody σcap hmap hσcap_mem with
          ⟨cursorA, fuelBody, firstA, result3, hcursorTagA, hcursorLocA, hfirstA_mem,
            happlyA, hfuelA, htc_bodyA, _hsubA, hfirstA_eq⟩
        have hfirstA_mem' : firstA ∈ first :: rest := by
          simpa [heq_results] using hfirstA_mem
        let bodyCtx : TypeContext :=
          { ctxᵢ with
            pc := joinPoison p (joinPoison ctxᵢ.pc p1)
            memEnv := result1.memEnv'
            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
              ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
            tagEnv := result1.tagEnv'
            pureCtx := true
            nextTag := cursorA.1
            nextLoc := cursorA.2
            regime := result1.regime' }
        have hcwr_body : CtxCons bodyCtx cf.memory (env.update x v₂) θ1 := by
          simpa [bodyCtx] using hcwr_body_for cursorA
        have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
          QTypRespectsTagMeaning_transport_etyp_pred
            (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
            (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            (hqt2 ▸ QTypRespectsTagMeaning_mono
              (IsCanonicalExtension.extends_tm hcanon1) hresTm2) rfl rfl
        have hTmBody : wfTagMeaningCtx tm1 bodyCtx := by
          simpa [bodyCtx, ctxAfter] using
            wfTagMeaningCtx_pclosure_body
              (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
              (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
              (p := p) (tcls := tcls)
              (xFun := x) (pbody := pbody) (σcap := σcap)
              (xArg := x) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
              hTm1 hresTm1 hetyp1 hσcap_mem hargTm
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
          exact ⟨(fun l hl =>
              Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA),
              varEnvRefLocsBounded_update
                (varEnvRefLocsBounded_ofCaptured
                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                    (CapturedEnvRefLocsFullBounded_mono
                      (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)
                      hcursorLocA)))
                (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypRefLocsBounded_mono h
                      (Nat.le_trans hmono_e1 hcursorLocA)),
              varEnvClosuresCapturedRefLocsBounded_update
                (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                  (CapturedEnvRefLocsFullBounded_mono
                    (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcap_mem)
                    hcursorLocA))
                (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                    rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                      (Nat.le_trans hmono_e1 hcursorLocA))⟩
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
        have hmasked_absent_body : MaskedTagsAbsentFromTrueTagEnv masked bodyCtx := by
          simpa [bodyCtx, ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using hmasked_absent1
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
        -- Thread extern registry: c₁ inherits default registry.
        have hreg_c₁_p : c₁.registry = emptyExternRegistry := by
          have h2 : c₂'.registry = emptyExternRegistry := by
            simpa [cinit] using terminatesTo_preserves_registry ht_e2
          exact (terminatesTo_preserves_registry ht_e1).trans h2
        rw [hreg_c₁_p] at ht_body
        have ht_body' : terminatesTo body
            { memory := cf.memory, varEnv := env.update x v₂,
              nextAddr := cf.nextAddr, pureMode := true } evalCfg o := by
          simpa [hcf] using ht_body
        have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
          have : fuelBody < fuel' := by rw [hfuelA]; exact Nat.lt_succ_self _
          exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
        have hTmBounded1 : TagMeaningBounded tm1 result1.nextTag' := by
          simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon1
        have hTmBoundedBody : TagMeaningBounded tm1 bodyCtx.nextTag := by
          simpa [bodyCtx] using hTmBounded1.mono hcursorTagA
        have hSingle_body :=
          singleIH fuelBody hfuel_lt body bodyCtx hTmBody hTmBoundedBody result3 htcBody_body
        have hpc_body : bodyCtx.pc = true := by
          simp [bodyCtx, hpc, joinPoison]
        rcases
          (hSingle_body hpredlaws1 hExtTyping hTmBody hTmBoundedBody).2
            cf.memory (env.update x v₂) θ1 evalCfg o
            hθ1wf hwfBody hric_body htagR_body hmasked_none_body
            hmasked_absent_body hcwr_body
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
              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
          regime_lookup_back_of_monotone hres1_to_firstA_mono
        have hmem_eq : cf.memory = evalCfg.memory := by
          obtain ⟨fuel_b, verbose_b, hbeval_b⟩ := ht_body'
          exact (beval_pure_memory_eq body fuel_b _ evalCfg o verbose_b
            pbody
            htoPExpr rfl hbeval_b).symm
        have hric_final :
            runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ_body := by
          have hric1_cf :
              runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1)
                cf.memory cf.varEnv θ1 := by
            simpa [hcf] using hric1
          exact
            appMember_runtimeInstantiatesCtx_from_body
              (ctx := ctxᵢ)
              (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
              (bodyFinalCtx := ctxAfter bodyCtx result3)
              (first := first) (src := firstA) (rest := rest) (res := res)
              (cf := cf) (evalCfg := evalCfg) (preCfg := cf)
              (θpre := θ1) (θbody := θ_body)
              h_join hfirstA_mem' hric_body_final hric1_cf
              (fun l hcontains_body => by
                simpa [ctxAfter, hfirstA_eq] using hcontains_body)
              (fun y qt hlookup => by
                simpa [ctxAfter] using hlookup)
              hmem_eq rfl hθext_body
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
              typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
                (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
          have hclean2 : qtypCleanUnder result2.regime' qt2 := by
            exact
              typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
                    (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
                    (by simpa [typecheck] using htcBody_body) hwfBody hpc_body l qt1 qt3
                    (by simpa [bodyCtx] using hlookup1) hlookup3 hclean3
                have hclean2 : qtypCleanUnder result2.regime' qt2 :=
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
                  typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
        have hric1_cf :
            runtimeInstantiatesCtx (ctxAfter (ctxAfter ctxᵢ result2) result1)
              cf.memory cf.varEnv θ1 := by
          simpa [hcf] using hric1
        have hcwr1_cf :
            CtxCons (ctxAfter (ctxAfter ctxᵢ result2) result1)
              cf.memory cf.varEnv θ1 := by
          simpa [hcf] using hcwr1
        exact
          appSingleRunMaskedPost_from_body_fields
            (predSat := predSat)
            ctxMember ctxJoinMember valBodyResult valJoinMember
            (ctx := ctxᵢ) (bodyCtx := bodyCtx)
            (result2 := result2) (result1 := result1)
            (first := first) (src := firstA) (result3 := result3)
            (rest := rest) (res := res)
            (μ := μ) (ρ := ρ) (θ := θ) (θpre := θ1) (θbody := θ_body)
            (cf := cf) (evalCfg := evalCfg) (preCfg := cf)
            (o := o) (p := p) (p1 := p1)
            h_join hfirstA_mem' hfirstA_eq hlookup_back_res1_to_A
            (fun y qt hlookup => by
              simpa [ctxAfter] using hlookup)
            (fun _ _ => Iff.rfl) hmem_eq rfl
            (wfExtendsMap_trans hθext2 hθext1) hθext_body hv_body_typed
            hric_body_final hric1_cf hcwr_body_final hcwr1_cf hvalc_body
            hpres_final hfresh_final
  | @externPfn c₂' v₂ c₁ x y id argTyp retSpec env impl vRaw
      ht_e2 ht_e1 hGet hArg hImpl hValRet hcfg hpm_e2 _ =>
    rcases
      hIH_e2_inst.2 μ ρ θ c₂' v₂
        hθwf hwf hric htagR hmasked_none hmasked_absent hcwr a pm hwfcfg ht_e2 hpc
      with ⟨θ2, hθext2, _hv₂_typed, hric2, hcwr2, _hvalc2, _hpres2, _hfresh2⟩
    have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθwf
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
    have hmasked_absent2 : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctxᵢ result2) :=
      typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
        masked ctxᵢ e2 fuel' result2 hmasked_absent hmasked_none htc2'
    have hpc2 : (ctxAfter ctxᵢ result2).pc = true := by
      simp [ctxAfter, hpc]
    have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
      simpa [ctxAfter] using IsCanonicalExtension.bounded hcanon2
    have hpm2 : c₂'.pureMode = pm := by
      simpa [cinit] using hpm_e2
    have heq_cfg2' :
        c₂' = { memory := c₂'.memory, varEnv := c₂'.varEnv, nextAddr := c₂'.nextAddr, pureMode := pm } := by
      have hreg2' : c₂'.registry = emptyExternRegistry := by
        simpa [cinit] using terminatesTo_preserves_registry ht_e2
      rw [← hpm2]
      exact config_eq_of_registry_default c₂' hreg2'
    have hwfcfg2 : wfConfig c₂' := by
      exact (wfConfig_preserved e2 _ c₂' _ ht_e2 hwfcfg).1
    have hIH_e1 := singleIH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      e1 (ctxAfter ctxᵢ result2) hTm2 hTmBounded2 result1 htc1'
    rcases
      (hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2).2
        c₂'.memory c₂'.varEnv θ2 c₁
        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env)
        hθ2wf hwf2 hric2 htagR2 hmasked_none2 hmasked_absent2 hcwr2 c₂'.nextAddr pm
        hwfcfg2 (heq_cfg2' ▸ ht_e1) hpc2
      with ⟨_θ1, _hθext1, hv₁_typed, _hric1, _hcwr1, _hvalc1, _hpres1, _⟩
    have hv₁_parrow :
        valueHasETyp _θ1
          (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env)
          (ETyp.parrow st1 st2 p tcls) := by
      simpa [hetyp1] using hv₁_typed
    exfalso
    have hreg_c₂' : c₂'.registry = emptyExternRegistry := by
      simpa [cinit] using terminatesTo_preserves_registry ht_e2
    have hreg_c₁ : c₁.registry = emptyExternRegistry :=
      (terminatesTo_preserves_registry ht_e1).trans hreg_c₂'
    rw [hreg_c₁] at hGet
    simp [emptyExternRegistry] at hGet

private lemma stepFRSingleRunFinalCleanPcTrue_app_parametric_maskedReg
  (masked : Tag → Prop)
  (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
  (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (ctxClosureBodyStart :
    AppClosureBodyStart CtxCons ValCons predSat tm)
  (ctxPClosureBodyStart :
    AppPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxExternClosureBodyStart :
    AppExternClosureBodyStart CtxCons ValCons predSat tm)
  (ctxExternPClosureBodyStart :
    AppExternPClosureBodyStart CtxCons ValCons predSat tm)
  (ctxMember :
    AppMemberCtxCons CtxCons predSat)
  (ctxJoinMember :
    AppJoinCtxConsFromMember CtxCons)
  (valBodyResult :
    AppBodyResultValCons ValCons)
  (valJoinMember :
    AppJoinValConsFromMember ValCons)
  (ctxConsOfRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      consistentWithRegime predSat ctx.regime ctx μ ρ θ →
      CtxCons ctx μ ρ θ)
  (valConsOfRegular :
    ∀ {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value},
      valueConsistentWithRegime predSat R qt μ θ v →
      ValCons R qt μ θ v)
  (ctxConsToRegular :
    ∀ {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap},
      (∀ k, masked k → ctx.regime.lookup? k = none) →
      CtxCons ctx μ ρ θ →
      consistentWithRegime predSat ctx.regime ctx μ ρ θ)
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
          ctxClosureBodyStart ctxExternClosureBodyStart
          ctxMember ctxJoinMember valBodyResult valJoinMember
          ctxConsOfRegular valConsOfRegular ctxConsToRegular
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          (ExternCallBoundarySingleFnContract.of_emptyExternRegistry (tcls := tcls))
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join htc
  | inr h_parrow =>
      obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, _hp1,
        _hnempty, _hsub, hmap, heq_results, h_join⟩ := h_parrow
      exact
        stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric_maskedReg
          masked CtxCons ValCons ctxᵢ predSat tm
          ctxPClosureBodyStart ctxExternPClosureBodyStart
          ctxMember ctxJoinMember valBodyResult valJoinMember
          ctxConsOfRegular valConsOfRegular ctxConsToRegular
          e1 e2 fuel' res result2 result1 etyp2 p2 pred2
          (ExternCallBoundarySinglePfnContract.of_emptyExternRegistry (tcls := tcls))
          singleIH hqt2 htc2' htc1'
          st1 st2 p p1 tcls results first rest hetyp1 hmap heq_results h_join htc

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
      (stepFRApp_externClosureBodyStart_masked masked predSat tm)
      (stepFRApp_externPClosureBodyStart_masked masked predSat tm)
      (stepFRApp_memberCtxCons_masked masked predSat)
      (stepFRApp_joinCtxConsFromMember_masked masked predSat)
      (stepFRApp_bodyResultValCons_masked masked predSat)
      (stepFRApp_joinValConsFromMember_masked masked predSat)
      (fun {ctx} {μ} {ρ} {θ} h =>
        consistentWithRegime_to_masked (masked := masked) h)
      (fun {R} {qt} {μ} {θ} {v} h =>
        valueConsistentWithRegime_to_masked (masked := masked) h)
      (fun {ctx} {_μ} {_ρ} {_θ} hnone hctx =>
        consistentWithRegimeMasked_unmask
          (masked := masked) (predSat := predSat) (R := ctx.regime)
          hnone hctx)
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
    intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
      o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2 (e1 IH defined after we have hTm2 from e2)
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm htagBounded result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    -- Local helper capturing the shared IH_e2 → IH_e1 ritual. Used by the
    -- "impossible" mixed-constructor branches below to derive valueHasETyp of
    -- each run's output value at `result1.qualType.etyp`, which is then
    -- `cases`d to close the goal via type-constructor mismatch.
    have mkValueHasETyp_pair :
        ∀ {c₂'₀ c₂'₁ c₁₀ c₁₁ : Config} {v₂₀ v₂₁ o₀ o₁ : Value},
          terminatesTo e2 cinit₀ c₂'₀ v₂₀ →
          terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
          terminatesTo e1 c₂'₀ c₁₀ o₀ →
          terminatesTo e1 c₂'₁ c₁₁ o₁ →
          ∃ θ₀1 θ₁1, valueHasETyp θ₀1 o₀ result1.qualType.etyp ∧
                      valueHasETyp θ₁1 o₁ result1.qualType.etyp := by
      intro c₂'₀ c₂'₁ c₁₀ c₁₁ v₂₀ v₂₁ o₀ o₁ ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
      have hstep_e2 := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
        μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
        hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, _hresTm2, hstep_e2⟩
      rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _, _, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
        hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _, _, _⟩
      have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
        simpa [ctxAfter] using BoundaryTagMeaningPost.bounded hcanon2
      have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      obtain ⟨_, heq_cfg₀'⟩ := cfg_pureMode_eq_of_terminatesTo ht₀_e2 rfl rfl
      obtain ⟨_, heq_cfg₁'⟩ := cfg_pureMode_eq_of_terminatesTo ht₁_e2 rfl rfl
      have hstep_e1 := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
        c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
        c₁₀ c₁₁ o₀ o₁
        hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
        c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
        (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
      rcases hstep_e1 with ⟨_, _, _, _, hstep_e1⟩
      rcases hstep_e1 with ⟨θ₀1, θ₁1, _, _, hv₀1_typed, hv₁1_typed, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _⟩
      exact ⟨θ₀1, θ₁1, hv₀1_typed, hv₁1_typed⟩
    have pfnImpossible_under_arrow :
        ∀ {θ1 : RealizationMap} {x : Name} {body : Expr} {env : VarEnv},
          valueHasETyp θ1 (Value.peClosure x body env) result1.qualType.etyp → False := by
      intro θ1 x body env hv_typed
      rcases valueHasETyp_peClosure_etyp_parrow_inv hv_typed with ⟨_, _, _, _, hparr⟩
      rw [hetyp1] at hparr
      cases hparr
    have finish_user_only :
        AppUserOnlyShape e1 e2 cinit₀ cf₀ o₀ →
        AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ →
        StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
          θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
      intro hstruct₀ hstruct₁
      -- Handle runtime closure/peClosure splits for the arrow-typed branch.
      rcases hstruct₀ with h_clo₀ | h_peclo₀
      · rcases hstruct₁ with h_clo₁ | h_peclo₁
        · -- Both runs: closure
          obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1,
            hnotExtern₀, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
          obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
            hnotExtern₁, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
          -- Phase A: Apply IH for e2
          have hstep_e2 := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
            μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
            hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
          rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
          rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
            hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩
          have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
            simpa [ctxAfter] using BoundaryTagMeaningPost.bounded hcanon2
          -- Phase B: Apply IH for e1
          have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
          have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
          have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
          have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
          obtain ⟨hpm₀, heq_cfg₀'⟩ := cfg_pureMode_eq_of_terminatesTo ht₀_e2 rfl rfl
          obtain ⟨hpm₁, heq_cfg₁'⟩ := cfg_pureMode_eq_of_terminatesTo ht₁_e2 rfl rfl
          have hstep_e1 := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
            c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
            c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
            hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
            c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
            (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
          rcases hstep_e1 with ⟨tm1, hcanon1, hpredlaws1, hresTm1, hstep_e1⟩
          rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
            hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩
          -- Phase C: Invert closure typing to extract FnTClosure structure
          have hv₀1_arrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
          have hv₁1_arrow : valueHasETyp θ₁1 (Value.closure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
          -- Invert closure typing for both runs
          cases hv₀1_arrow with
          | closure_extern htcl₀ _henv₀ _hcover₀ =>
            exact False.elim (hnotExtern₀ _ _ _ _ _ rfl)
          | closure htcl₀ henv₀_typing hcover₀ =>
          cases hv₁1_arrow with
          | closure_extern htcl₁ _henv₁ _hcover₁ =>
            exact False.elim (hnotExtern₁ _ _ _ _ _ rfl)
          | closure htcl₁ henv₁_typing hcover₁ =>
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
            fun hclean1_e1 => by
              rcases
                stepFR_app_arrow_sync_from_clean_with_extern
                  (predSat := predSat)
                  (ctx := (ctxAfter ctxᵢ result2))
                  (res1 := result1)
                  (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
                  (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
                  (θ₀ := θ₀1) (θ₁ := θ₁1)
                  (x₀ := x₀) (x₁ := x₁)
                  (body₀ := body₀) (body₁ := body₁)
                  (env₀ := env₀) (env₁ := env₁)
                  hetyp1 hclean1_e1 hres_agree1 with hsync | hdirty
              · rcases hsync with hregular | hextern
                · left
                  exact hregular
                · rcases hextern with
                    ⟨id, _x, y, argTyp, retSpec, effects, _σcap, _hmem,
                      _hx₀, _hx₁, hbody₀, _hbody₁, _hcap⟩
                  exact False.elim (hnotExtern₀ id y argTyp retSpec effects hbody₀)
              · right
                exact hdirty
          have _sync_extract_of_clean :
              ∀ hclean1_e1 :
                  qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                  (∃ σcap cursor fuelBody firstShared result3Shared,
                      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                      result1.nextTag' ≤ cursor.1 ∧
                      result1.nextLoc' ≤ cursor.2 ∧
                      firstShared ∈ results ∧
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
                      applyFnTClosureAtCursor (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
                        etyp2 p2 pred2 ctxᵢ result1 cursor fuel' = .ok firstShared ∧
                    fuel' = Nat.succ fuelBody ∧
                    typecheckExpr
                      { ctxᵢ with
                        pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                        memEnv := result1.memEnv'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                        tagEnv := result1.tagEnv'
                        nextTag := cursor.1
                        nextLoc := cursor.2
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
              rcases applyFnTClosure_regular_inv_of_threaded_mem
                  ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                  x₀ body₀ σcap hmap hmem with
                ⟨cursor, fuelBody, firstShared, result3Shared, hcursorTag, hcursorLoc, hfirstMem,
                  happly', hfuel', htc', hsub', hfirst'⟩
              exact ⟨σcap, cursor, fuelBody, firstShared, result3Shared, hmem, hcursorTag, hcursorLoc, hfirstMem, hx, hbody, hcap,
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
              AppTwoRunOutChoice predSat ctxᵢ res θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
            have hOutMapChoice_p1p_true
                (h_p1p : joinPoison p1 p = true) :
                AppTwoRunOutChoice predSat ctxᵢ res θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
              rcases applyClosuresThreaded_ok_mem_output_exists_input
                  (applyOne := fun tcl cursor =>
                    applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                      ctxᵢ result1 cursor fuel')
                  (xs := tcls) (cursor := (result1.nextTag', result1.nextLoc'))
                  (results := results) (y := first) hmap (by simp [heq_results])
                with ⟨tcl, _htcl_mem, cursorFirst, happly_first_cursor⟩
              let result1CursorFirst : TypeResult :=
                { result1 with nextTag' := cursorFirst.1, nextLoc' := cursorFirst.2 }
              have happly_first :
                  applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                      ctxᵢ result1CursorFirst fuel' = .ok first := by
                unfold applyFnTClosure
                unfold applyFnTClosureAtCursor at happly_first_cursor
                simpa [result1CursorFirst] using happly_first_cursor
              have hfirst_pack :
                  first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
                applyFnTClosure_ok_poison_pred_of_p1p_true
                  (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                  (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                  (result2 := result1CursorFirst) (fuel := fuel') (tcl := tcl) (r := first)
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
                closureCapturedVarsRegime_closure_extract hetyp1 hnotExtern₀
                  (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
              have ⟨σcapA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
                closureCapturedVarsRegime_closure_extract hetyp1 hnotExtern₁
                  (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
              -- Get body typing for σcapA₀ and σcapA₁ from applyFnTClosure
              rcases applyFnTClosure_regular_inv_of_threaded_mem
                  ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                  x₀ body₀ σcapA₀ hmap hσcapA₀_mem with
                ⟨cursorA₀, fuelBodyA₀, firstA₀, result3A₀, hcursorTagA₀, hcursorLocA₀,
                  hfirstA₀_mem, happlyA₀, hfuelA₀,
                  htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
              rcases applyFnTClosure_regular_inv_of_threaded_mem
                  ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                  x₁ body₁ σcapA₁ hmap hσcapA₁_mem with
                ⟨cursorA₁, fuelBodyA₁, firstA₁, result3A₁, hcursorTagA₁, hcursorLocA₁,
                  hfirstA₁_mem, happlyA₁, hfuelA₁,
                  htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
              -- Get membership in first :: rest (for join transport)
              have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
                simpa [heq_results] using hfirstA₀_mem
              have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
                simpa [heq_results] using hfirstA₁_mem
              -- Define body contexts
              let bodyCtxA₀ : TypeContext :=
                { ctxᵢ with
                  pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                  memEnv := result1.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  tagEnv := result1.tagEnv'
                  nextTag := cursorA₀.1
                  nextLoc := cursorA₀.2
                  regime := result1.regime' }
              let bodyCtxA₁ : TypeContext :=
                { ctxᵢ with
                  pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                  memEnv := result1.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  tagEnv := result1.tagEnv'
                  nextTag := cursorA₁.1
                  nextLoc := cursorA₁.2
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
              have hTmBodyA₀ : wfTagMeaningCtx tm1 bodyCtxA₀ := by
                have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := hresTm1
                have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                  simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
                have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                  QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (QTypRespectsTagMeaning_mono
                      (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg)
                    rfl rfl
                simpa [bodyCtxA₀, ctxAfter] using
                  wfTagMeaningCtx_closure_body
                    (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
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
                exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA₀),
                  varEnvRefLocsBounded_update
                    (varEnvRefLocsBounded_ofCaptured
                      (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                        (CapturedEnvRefLocsFullBounded_mono
                          (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)
                          hcursorLocA₀)))
                    (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorLocA₀)),
                  varEnvClosuresCapturedRefLocsBounded_update
                    (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                      (CapturedEnvRefLocsFullBounded_mono
                        (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)
                        hcursorLocA₀))
                    (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorLocA₀))⟩
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
                singleIH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀
                  (by simpa [bodyCtxA₀] using
                    (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₀)
                  result3A₀ htcBodyA₀'
              have hpc_bodyA₀_run : bodyCtxA₀.pc = true := by
                simp [bodyCtxA₀, joinPoison] at h_p1p ⊢
                cases p1 <;> cases p <;> simp at h_p1p ⊢
              -- Thread extern registry: c₁₀ inherits default registry.
              have hreg_c₁₀_A : c₁₀.registry = emptyExternRegistry := by
                have h2 : c₂'₀.registry = emptyExternRegistry := by
                  simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
                exact (terminatesTo_preserves_registry ht₀_e1).trans h2
              rw [hreg_c₁₀_A] at ht₀_body
              have hsr₀ :=
                (hSingle_bodyA₀ hpredlaws1 hExtTyping hTmBodyA₀
                  (by simpa [bodyCtxA₀] using
                    (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₀)).2
                  c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
                  hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀
                  hcwr_bodyA₀ c₁₀.nextAddr false hwfcfg_body_initA₀ ht₀_body
                  hpc_bodyA₀_run
              rcases hsr₀ with
                ⟨θ₀_body, hθext₀_body, hv₀_body_typed,
                  hric_bodyA₀_final, hcwr_bodyA₀_final, hvalc_bodyA₀, _hpres₀, _hfresh₀_body⟩
              -- ===== Run 1: unary body witness =====
              have hTmBodyA₁ : wfTagMeaningCtx tm1 bodyCtxA₁ := by
                have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := hresTm1
                have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                  simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
                have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                  QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (QTypRespectsTagMeaning_mono
                      (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg)
                    rfl rfl
                simpa [bodyCtxA₁, ctxAfter] using
                  wfTagMeaningCtx_closure_body
                    (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
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
                exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA₁),
                  varEnvRefLocsBounded_update
                    (varEnvRefLocsBounded_ofCaptured
                      (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                        (CapturedEnvRefLocsFullBounded_mono
                          (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₁_mem)
                          hcursorLocA₁)))
                    (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorLocA₁)),
                  varEnvClosuresCapturedRefLocsBounded_update
                    (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                      (CapturedEnvRefLocsFullBounded_mono
                        (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₁_mem)
                        hcursorLocA₁))
                    (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorLocA₁))⟩
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
                singleIH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁
                  (by simpa [bodyCtxA₁] using
                    (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₁)
                  result3A₁ htcBodyA₁'
              have hpc_bodyA₁_run : bodyCtxA₁.pc = true := by
                simp [bodyCtxA₁, joinPoison] at h_p1p ⊢
                cases p1 <;> cases p <;> simp at h_p1p ⊢
              -- Thread extern registry: c₁₁ inherits default registry.
              have hreg_c₁₁_A : c₁₁.registry = emptyExternRegistry := by
                have h2 : c₂'₁.registry = emptyExternRegistry := by
                  simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
                exact (terminatesTo_preserves_registry ht₁_e1).trans h2
              rw [hreg_c₁₁_A] at ht₁_body
              have hsr₁ :=
                (hSingle_bodyA₁ hpredlaws1 hExtTyping hTmBodyA₁
                  (by simpa [bodyCtxA₁] using
                    (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₁)).2
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
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                regime_lookup_back_of_monotone hres1_to_firstA₀_mono
              have hlookup_back_res1_to_A₁ :
                  ∀ k b,
                    (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                regime_lookup_back_of_monotone hres1_to_firstA₁_mono
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
                  exact
                    appMember_runtimeInstantiatesCtx_from_body
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtxA₀ result3A₀)
                      (first := first) (src := firstA₀) (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := c₁₀)
                      (θpre := θ₀1) (θbody := θ₀_body)
                      h_join hfirstA₀_mem' hric_bodyA₀_final hric₀1
                      (fun l hcontains_body => by
                        simpa [ctxAfter, hfirstA₀_eq] using hcontains_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hmem₀_eq hvar₀_eq hθext₀_body,
                -- runtimeInstantiatesCtx run 1
                by
                  exact
                    appMember_runtimeInstantiatesCtx_from_body
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtxA₁ result3A₁)
                      (first := first) (src := firstA₁) (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := c₁₁)
                      (θpre := θ₁1) (θbody := θ₁_body)
                      h_join hfirstA₁_mem' hric_bodyA₁_final hric₁1
                      (fun l hcontains_body => by
                        simpa [ctxAfter, hfirstA₁_eq] using hcontains_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hmem₁_eq hvar₁_eq hθext₁_body,
                -- consistentWithRegime run 0
                by
                  exact
                    appMember_consistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtxA₀ result3A₀)
                      (first := first) (src := firstA₀) (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := c₁₀)
                      (θpre := θ₀1) (θbody := θ₀_body)
                      h_join hfirstA₀_mem' hcwr_bodyA₀_final hcwr₀1
                      (fun l qt hlookup => by
                        simpa [ctxAfter, hfirstA₀_eq] using hlookup)
                      (fun k b hk_src => by
                        simpa [ctxAfter, hfirstA₀_eq] using hk_src)
                      (fun k b hk_body => by
                        simpa [ctxAfter, hfirstA₀_eq] using hk_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hlookup_back_res1_to_A₀ hpred_compat₀ hmem₀_eq hvar₀_eq hθext₀_body,
                -- consistentWithRegime run 1
                by
                  exact
                    appMember_consistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtxA₁ result3A₁)
                      (first := first) (src := firstA₁) (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := c₁₁)
                      (θpre := θ₁1) (θbody := θ₁_body)
                      h_join hfirstA₁_mem' hcwr_bodyA₁_final hcwr₁1
                      (fun l qt hlookup => by
                        simpa [ctxAfter, hfirstA₁_eq] using hlookup)
                      (fun k b hk_src => by
                        simpa [ctxAfter, hfirstA₁_eq] using hk_src)
                      (fun k b hk_body => by
                        simpa [ctxAfter, hfirstA₁_eq] using hk_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hlookup_back_res1_to_A₁ hpred_compat₁ hmem₁_eq hvar₁_eq hθext₁_body,
                -- agreeOnClean for ¬qtypCleanUnder (p1=true, different closure bodies)
                by
                  -- Regime monotonicity: result1.regime' → res.regime' (through the join)
                  have h_all_members_mono :
                      ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                    intro x hx
                    have hxResults : x ∈ results := by
                      simpa [heq_results] using hx
                    rcases applyClosuresThreaded_ok_mem_output_exists_input
                        (applyOne := fun tcl cursor =>
                          applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                            ctxᵢ result1 cursor fuel')
                        (xs := tcls) (cursor := (result1.nextTag', result1.nextLoc'))
                        (results := results) (y := x) hmap hxResults with
                      ⟨tcl, _htcl_mem, cursor, happly⟩
                    exact applyFnTClosureAtCursor_regime_mono tcl ctxᵢ st1 st2 p p1
                      etyp2 p2 pred2 result1 x cursor fuel'
                      (fun m _hlt e ctx' res' htc =>
                        by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                      happly
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
                          typecheckExpr_lookup_clean_back_of_pc_true hExtTyping
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
                              | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ hv₀ _ =>
                                cases hv₀
                              | dirty_internal_arrow _ hisA htyp₀ _ =>
                                simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                              | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                                cases hv₀
                              | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ hv₀ _ =>
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
                  exact
                    appMember_valueConsistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ) (bodyCtx := bodyCtxA₀)
                      (first := first) (src := firstA₀) (result3 := result3A₀)
                      (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (θ := θ₀_body) (o := o₀)
                      (p := p) (p1 := p1)
                      h_join hfirstA₀_mem' hfirstA₀_eq hmem₀_eq hvalc_bodyA₀,
                -- valueConsistentWithRegime run 1
                by
                  exact
                    appMember_valueConsistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ) (bodyCtx := bodyCtxA₁)
                      (first := first) (src := firstA₁) (result3 := result3A₁)
                      (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (θ := θ₁_body) (o := o₁)
                      (p := p) (p1 := p1)
                      h_join hfirstA₁_mem' hfirstA₁_eq hmem₁_eq hvalc_bodyA₁,
                -- resultAgreesIfClean (vacuously true since poison=true ∧ pred=noPred)
                resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
            by_cases hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
            · rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
              · rcases hshared with
                  ⟨σcap, cursorShared, fuelBody, firstShared, result3Shared,
                    hmem, hcursorSharedTag, hcursorSharedLoc, hfirstSharedMem, hx, hbody, hcap,
                    hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                    happly, hfuel, htcBody, hsubBody, hfirstShared⟩
                let bodyCtx : TypeContext :=
                  { ctxᵢ with
                    pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                    memEnv := result1.memEnv'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                    tagEnv := result1.tagEnv'
                    nextTag := cursorShared.1
                    nextLoc := cursorShared.2
                    regime := result1.regime' }
                have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
                have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
                have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
                  have hfuel_lt' : fuelBody < fuel' := by
                    rw [hfuel]
                    exact Nat.lt_succ_self fuelBody
                  exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
                have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
                  have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                    simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
                  have hresTm2_arg' : QTypRespectsTagMeaning tm1 ⟨etyp2, p2, pred2⟩ :=
                    QTypRespectsTagMeaning_mono
                      (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg
                  have hargTm' :
                      ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                        QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                        qtypGuardDesc? qt' = some (k, d) →
                        tm1.lookup k = some d :=
                    QTypRespectsTagMeaning_transport_etyp_pred
                      (tm := tm1)
                      (qt := ⟨etyp2, p2, pred2⟩)
                      (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      hresTm2_arg' rfl rfl
                  exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
                have hTmBody : wfTagMeaningCtx tm1 bodyCtx := by
                  have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := hresTm1
                  have hTmBody' :
                      wfTagMeaningCtx tm1
                        { (ctxAfter ctxᵢ result2) with
                          memEnv := result1.memEnv'
                          tagEnv := result1.tagEnv'
                          nextLoc := result1.nextLoc'
                          nextTag := result1.nextTag'
                          regime := result1.regime'
                          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                            ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ } :=
                    wfTagMeaningCtx_closure_body
                      (tm := tm1)
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
                  have hCapBoundBase : CapturedEnvFullBounded σcap result1.nextTag' := hClosFull _ hmem
                  have hCapBound : CapturedEnvFullBounded σcap cursorShared.1 :=
                    CapturedEnvFullBounded_mono hCapBoundBase hcursorSharedTag
                  have hCapPred := capturedPredTagsBounded_of_fullBounded hCapBound
                  -- Arg pred bounded (pred2 from result2, monotone to result1.nextTag')
                  have hmono_r2_r1 : result2.nextTag' ≤ result1.nextTag' :=
                    typecheck_normal_nextTag_mono (ctxAfter ctxᵢ result2) e1 fuel' result1
                      (by simpa [typecheck] using htc1')
                  have hArgPredBase : qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ result1.nextTag' := by
                    have := (typecheckExpr_preserves_predTagsBounded ctxᵢ e2 fuel' result2
                      (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2).2
                    rw [hqt2] at this
                    exact qtypPredTagBounded_mono this hmono_r2_r1
                  have hArgPred :
                      qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ cursorShared.1 :=
                    qtypPredTagBounded_mono hArgPredBase hcursorSharedTag
                  have hArgClosBase : etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp result1.nextTag' := by
                    have := typecheckExpr_preserves_closureCapturedBounded ctxᵢ e2 fuel' result2
                      (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2
                    rw [hqt2] at this; exact etypClosuresFullBounded_mono this hmono_r2_r1
                  have hArgClos :
                      etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp
                        cursorShared.1 :=
                    etypClosuresFullBounded_mono hArgClosBase hcursorSharedTag
                  refine ⟨?_,
                    ⟨predTagsBoundedInVarEnv_update
                      (predTagsBoundedInVarEnv_ofCaptured hCapPred) hArgPred,
                     ?_⟩,
                    varEnvClosuresCapturedBounded_update
                      (varEnvClosuresCapturedBounded_ofCaptured hCapBound) hArgClos⟩
                  · simpa [bodyCtx, ctxAfter] using
                      tagEnvBounded_mono result1.tagEnv' result1.nextTag' cursorShared.1
                        (by simpa [ctxAfter] using hb_tag1) hcursorSharedTag
                  · simpa [bodyCtx, ctxAfter] using
                      predTagsBoundedInMemEnv_mono
                        (by simpa [ctxAfter] using hb_predM1) hcursorSharedTag
                have hTmBoundedBody : TagMeaningBounded tm1 bodyCtx.nextTag := by
                  have hbase : TagMeaningBounded tm1 result1.nextTag' :=
                    BoundaryTagMeaningPost.bounded hcanon1
                  simpa [bodyCtx, ctxAfter] using hbase.mono hcursorSharedTag
                have hIH_body :=
                  IH fuelBody hfuel_lt body₀ bodyCtx hTmBody htagBoundedBody result3Shared htcBody'
                have hwfBodyCtx : wfTypeContext bodyCtx := by
                  simp only [bodyCtx, wfTypeContext]
                  have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                    (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
                  have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
                  exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorSharedLoc),
                    varEnvRefLocsBounded_update
                      (varEnvRefLocsBounded_ofCaptured
                        (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                          (CapturedEnvRefLocsFullBounded_mono
                            (by rw [hetyp1] at hClosRL; exact hClosRL _ hmem)
                            hcursorSharedLoc)))
                      (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                          rw [hqt2] at h; exact etypRefLocsBounded_mono h
                            (Nat.le_trans hmono_e1 hcursorSharedLoc)),
                    varEnvClosuresCapturedRefLocsBounded_update
                      (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                        (CapturedEnvRefLocsFullBounded_mono
                          (by rw [hetyp1] at hClosRL; exact hClosRL _ hmem)
                          hcursorSharedLoc))
                      (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                          rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                            (Nat.le_trans hmono_e1 hcursorSharedLoc))⟩
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
                -- Thread extern registry: c₁₀/c₁₁ inherit default registry.
                have hreg_c₁₀_B : c₁₀.registry = emptyExternRegistry := by
                  have h2 : c₂'₀.registry = emptyExternRegistry := by
                    simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
                  exact (terminatesTo_preserves_registry ht₀_e1).trans h2
                have hreg_c₁₁_B : c₁₁.registry = emptyExternRegistry := by
                  have h2 : c₂'₁.registry = emptyExternRegistry := by
                    simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
                  exact (terminatesTo_preserves_registry ht₁_e1).trans h2
                rw [hreg_c₁₀_B] at ht₀_body
                rw [hreg_c₁₁_B] at ht₁_body
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
                have hstep_body := hIH_body hpredlaws1 hExtTyping hTmBody hTmBoundedBody
                  c₁₀.memory c₁₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
                  evalCfg₀ evalCfg₁ o₀ o₁
                  hθ₀1wf hθ₁1wf hwfBodyCtx htagBoundedBody hric_body₀ hric_body₁ htagR_body
                  hcwr_body₀ hcwr_body₁ hagree_body_start
                  c₁₀.nextAddr c₁₁.nextAddr false
                  hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
                rcases hstep_body with ⟨_tm_body, _hcanon_body, _hpredlaws_body, _hresTm_body, hstep_body⟩
                rcases hstep_body with
                  ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                    _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after, _htagBounded_body_after,
                    _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                    _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                    _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                    _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩
                have hAgree_out_body :
                    ∀ θ₀_body θ₁_body,
                      wfExtendsMap θ₀1 θ₀_body →
                      wfExtendsMap θ₁1 θ₁_body →
                      runtimeInstantiatesCtx (ctxAfter bodyCtx result3Shared)
                        evalCfg₀.memory evalCfg₀.varEnv θ₀_body →
                      runtimeInstantiatesCtx (ctxAfter bodyCtx result3Shared)
                        evalCfg₁.memory evalCfg₁.varEnv θ₁_body →
                      agreeOnClean predSat (ctxAfter bodyCtx result3Shared).regime
                        (ctxAfter bodyCtx result3Shared)
                        evalCfg₀.memory evalCfg₀.varEnv θ₀_body
                        evalCfg₁.memory evalCfg₁.varEnv θ₁_body →
                      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                        cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                  intro θ₀_body θ₁_body _hθext₀_body _hθext₁_body
                    _hric_body_final₀ _hric_body_final₁ hagree_body_after
                  have hsrc_mem : firstShared ∈ first :: rest := by
                    simpa [heq_results] using hfirstSharedMem
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
                    AppTwoRunOutPack predSat ctxᵢ res cf₀ cf₁ o₀ o₁
                      θ₀_body θ₁_body := by
                  have hsrc_mem' : firstShared ∈ first :: rest := by
                    simpa [heq_results] using hfirstSharedMem
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
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                    regime_lookup_back_of_monotone hres1_to_src_mono
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
                    hAgree_out_body θ₀_body θ₁_body _hθext₀_body _hθext₁_body
                      _hric_body_final₀ _hric_body_final₁ hagree_body_after, ?_, ?_, ?_⟩
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
                    exact
                      appMember_runtimeInstantiatesCtx_from_body
                        (ctx := ctxᵢ)
                        (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                        (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                        (first := first) (src := firstShared) (rest := rest) (res := res)
                        (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := c₁₀)
                        (θpre := θ₀1) (θbody := θ₀_body)
                        h_join hsrc_mem' _hric_body_final₀ hric₀1
                        (fun l hcontains_src_body => by
                          simpa [ctxAfter, hfirstShared] using hcontains_src_body)
                        (fun x qt hlookup => by
                          simpa [ctxAfter] using hlookup)
                        hmem₀_eq hvar₀_eq _hθext₀_body
                  · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                    have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                      simp [heq_cfg₁]
                    have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                      simp [heq_cfg₁]
                    exact
                      appMember_runtimeInstantiatesCtx_from_body
                        (ctx := ctxᵢ)
                        (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                        (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                        (first := first) (src := firstShared) (rest := rest) (res := res)
                        (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := c₁₁)
                        (θpre := θ₁1) (θbody := θ₁_body)
                        h_join hsrc_mem' _hric_body_final₁ hric₁1
                        (fun l hcontains_src_body => by
                          simpa [ctxAfter, hfirstShared] using hcontains_src_body)
                        (fun x qt hlookup => by
                          simpa [ctxAfter] using hlookup)
                        hmem₁_eq hvar₁_eq _hθext₁_body
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
                    exact
                      appMember_consistentWithRegime_from_body
                        (predSat := predSat)
                        (ctx := ctxᵢ)
                        (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                        (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                        (first := first) (src := firstShared) (rest := rest) (res := res)
                        (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := c₁₀)
                        (θpre := θ₀1) (θbody := θ₀_body)
                        h_join hsrc_mem' _hcwr_body_final₀ hcwr₀1
                        (fun l qt hlookup => by
                          simpa [ctxAfter, hfirstShared] using hlookup)
                        (fun k b hk_src => by
                          simpa [ctxAfter, hfirstShared] using hk_src)
                        (fun k b hk_body => by
                          simpa [ctxAfter, hfirstShared] using hk_body)
                        (fun x qt hlookup => by
                          simpa [ctxAfter] using hlookup)
                        hlookup_back_res1_to_src hpred_compat₀ hmem₀_eq hvar₀_eq _hθext₀_body
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
                    exact
                      appMember_consistentWithRegime_from_body
                        (predSat := predSat)
                        (ctx := ctxᵢ)
                        (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                        (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                        (first := first) (src := firstShared) (rest := rest) (res := res)
                        (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := c₁₁)
                        (θpre := θ₁1) (θbody := θ₁_body)
                        h_join hsrc_mem' _hcwr_body_final₁ hcwr₁1
                        (fun l qt hlookup => by
                          simpa [ctxAfter, hfirstShared] using hlookup)
                        (fun k b hk_src => by
                          simpa [ctxAfter, hfirstShared] using hk_src)
                        (fun k b hk_body => by
                          simpa [ctxAfter, hfirstShared] using hk_body)
                        (fun x qt hlookup => by
                          simpa [ctxAfter] using hlookup)
                        hlookup_back_res1_to_src hpred_compat₁ hmem₁_eq hvar₁_eq _hθext₁_body
                  · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                    have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                      simp [heq_cfg₀]
                    exact
                      appMember_valueConsistentWithRegime_from_body
                        (predSat := predSat)
                        (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                        (first := first) (src := firstShared) (result3 := result3Shared)
                        (rest := rest) (res := res)
                        (cf := cf₀) (evalCfg := evalCfg₀) (θ := θ₀_body) (o := o₀)
                        (p := p) (p1 := p1)
                        h_join hsrc_mem' hfirstShared hmem₀_eq _hvalc_body₀
                  · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                    have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                      simp [heq_cfg₁]
                    exact
                      appMember_valueConsistentWithRegime_from_body
                        (predSat := predSat)
                        (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                        (first := first) (src := firstShared) (result3 := result3Shared)
                        (rest := rest) (res := res)
                        (cf := cf₁) (evalCfg := evalCfg₁) (θ := θ₁_body) (o := o₁)
                        (p := p) (p1 := p1)
                        h_join hsrc_mem' hfirstShared hmem₁_eq _hvalc_body₁
                  · -- shared-member resultAgreesIfClean -> joined result qualType.
                    have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                      simp [heq_cfg₀]
                    have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                      simp [heq_cfg₁]
                    exact
                      appMember_resultAgreesIfClean_from_body
                        (predSat := predSat)
                        (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                        (first := first) (src := firstShared) (result3 := result3Shared)
                        (rest := rest) (res := res)
                        (cf₀ := cf₀) (cf₁ := cf₁) (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
                        (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                        (p := p) (p1 := p1)
                        h_join hsrc_mem' hfirstShared hmem₀_eq hmem₁_eq _hres_agree_body
                have hbody_post_for_transport :
                    StepFRPost bodyCtx body₀ result3Shared predSat tm1
                      θ₀1 θ₁1 evalCfg₀ evalCfg₁ o₀ o₁ := by
                  exact ⟨_tm_body, _hcanon_body, _hpredlaws_body, _hresTm_body,
                    θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                    _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after,
                    _htagBounded_body_after, _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                    _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                    _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                    _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩
                have hOutChoice_body_from_helper :
                    AppTwoRunOutChoice predSat ctxᵢ res θ₀1 θ₁1 cf₀ cf₁ o₀ o₁ := by
                  have hsrc_mem' : firstShared ∈ first :: rest := by
                    simpa [heq_results] using hfirstSharedMem
                  have hres1_to_src_mono :
                      Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                        (ctxAfter ctxᵢ firstShared).regime := by
                    have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                      regime_monotone bodyCtx body₀ fuelBody result3Shared htcBody'
                    simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                  have hlookup_back_res1_to_src :
                      ∀ k b,
                        (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                    regime_lookup_back_of_monotone hres1_to_src_mono
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  have hpred_compat₀ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₀.memory v' ↔
                          qtypPredHolds predSat qt' cf₀.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₀1)
                      (μ := c₁₀.memory) (μ' := cf₀.memory)
                  have hpred_compat₁ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₁.memory v' ↔
                          qtypPredHolds predSat qt' cf₁.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₁1)
                      (μ := c₁₁.memory) (μ' := cf₁.memory)
                  exact
                    appTwoRunOutChoice_from_body_stepFRPost
                      (predSat := predSat) (tmBody := tm1)
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyCtx := bodyCtx)
                      (postExpr := body₀)
                      (first := first) (src := firstShared) (result3 := result3Shared)
                      (rest := rest) (res := res)
                      (cf₀ := cf₀) (cf₁ := cf₁)
                      (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
                      (preCfg₀ := c₁₀) (preCfg₁ := c₁₁)
                      (θpre₀ := θ₀1) (θpre₁ := θ₁1)
                      (o₀ := o₀) (o₁ := o₁) (p := p) (p1 := p1)
                      h_join hsrc_mem' hfirstShared hlookup_back_res1_to_src
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hpred_compat₀ hpred_compat₁ hmem₀_eq hmem₁_eq hvar₀_eq hvar₁_eq
                      hric₀1 hric₁1 hcwr₀1 hcwr₁1 hAgree_out_body hbody_post_for_transport
                rcases hOutChoice_body_from_helper with
                  ⟨θ₀_out, θ₁_out, hθext_body_out₀, hθext_body_out₁, hOutPack_body_out⟩
                exact
                  ⟨θ₀_out, θ₁_out,
                    wfExtendsMap_trans hθext₀2
                      (wfExtendsMap_trans hθext₀1 hθext_body_out₀),
                    wfExtendsMap_trans hθext₁2
                      (wfExtendsMap_trans hθext₁1 hθext_body_out₁),
                    hOutPack_body_out⟩
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
          have hresTm2_arg : QTypRespectsTagMeaning tm1 ⟨etyp2, p2, pred2⟩ := by
            have hresTm2_arg0 : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
              simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
            intro qt' k d hinq hqd
            exact (BoundaryTagMeaningPost.extends_tm hcanon1).lookup (hresTm2_arg0 hinq hqd)
          have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred
              (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
              (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
              hresTm2_arg rfl rfl
          have hresults_wf :
              ∀ r, r ∈ results → wfTypeResult r :=
            threaded_applyFnTClosure_forall_wfTypeResult
              (fuel_top := fuel' + 1)
              (IH := fun m _ e ctx' res' hwf htc =>
                typecheckExpr_preserves_wfTypeResult ctx' e m res' hwf htc)
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
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
          have hresults_regime :
              ∀ r, r ∈ results →
                regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
            have htagR1_ctx :
                regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
              simpa [ctxAfter] using htagR1
            exact
              threaded_applyFnTClosure_forall_regimeConsistentWithCtx
                (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                (result1 := result1) (fuel := fuel')
                (tcls := tcls) (results := results)
                htagR1_ctx hmap
          have hfirst_in_results : first ∈ results := by
            simp [heq_results]
          have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
          have h_first_regime :
              regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
            hresults_regime first hfirst_in_results
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
          have h_mem_join :
              ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l :=
            joinTypeResults_mem_contains_head_or_rest
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
          have h_tag_join :
              tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv (ctxAfter ctxᵢ res).regime :=
            joinTypeResults_tagEnvConsistentWithRegime
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_first_regime h_rest_regime
          rcases typecheck_preserves_predSatLaws hExtTyping predSat tm ctxᵢ
              (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
              hwfTm hTmBounded hpredlaws htc with
            ⟨tmOut, hcanonOut, hpredlawsOut⟩
          refine ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut,
            hpredlawsOut, ?_, θ₀_out, θ₁_out,
            ?_,
            ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- QTypRespectsTagMeaning tm res.qualType
            exact IsCanonicalExtension.respectsResult hcanonOut
          · -- wfExtendsMap θ₀ θ₀'
            exact hθext_out₀
          · -- wfExtendsMap θ₁ θ₁'
            exact hθext_out₁
          · -- valueHasETyp θ₀1 o₀ res.qualType.etyp
            exact hv_out₀
          · -- valueHasETyp θ₁1 o₁ res.qualType.etyp
            exact hv_out₁
          · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
            exact IsCanonicalExtension.wfCtx hcanonOut
          · -- wfTypeContext (ctxAfter ctxᵢ res)
            exact
              join_transport_wfTypeContext
                (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join h_mem_join
                (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                  (Nat.le_trans
                    (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                      (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                    (threaded_applyFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
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
          obtain ⟨c₂'₀, _, c₁₀, _, _, _, _, ht₀_e2, ht₀_e1, _, _, _, _, _, _⟩ := h_clo₀
          obtain ⟨c₂'₁, _, c₁₁, x₁, body₁, env₁, _, ht₁_e2, ht₁_e1, _, _, _, _, _⟩ := h_peclo₁
          obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          rcases valueHasETyp_peClosure_etyp_parrow_inv hv₁_typed with ⟨_, _, _, _, hparr⟩
          rw [hetyp1] at hparr
          cases hparr
      · rcases hstruct₁ with h_clo₁ | h_peclo₁
        · -- Run 0: peClosure, Run 1: closure (mixed case, impossible under arrow typing)
          obtain ⟨c₂'₀, _, c₁₀, x₀, body₀, env₀, _, ht₀_e2, ht₀_e1, _, _, _, _, _⟩ := h_peclo₀
          obtain ⟨c₂'₁, _, c₁₁, _, _, _, _, ht₁_e2, ht₁_e1, _, _, _, _, _, _⟩ := h_clo₁
          obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          rcases valueHasETyp_peClosure_etyp_parrow_inv hv₀_typed with ⟨_, _, _, _, hparr⟩
          rw [hetyp1] at hparr
          cases hparr
        · -- Run 0: peClosure, Run 1: peClosure (impossible under arrow typing)
          obtain ⟨c₂'₀, _, c₁₀, x₀, body₀, env₀, _, ht₀_e2, ht₀_e1, _, _, _, _, _⟩ := h_peclo₀
          obtain ⟨c₂'₁, _, c₁₁, _, _, _, _, ht₁_e2, ht₁_e1, _, _, _, _, _⟩ := h_peclo₁
          obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          rcases valueHasETyp_peClosure_etyp_parrow_inv hv₀_typed with ⟨_, _, _, _, hparr⟩
          rw [hetyp1] at hparr
          cases hparr
    have hfull₀ := terminatesTo_app_inv_full e1 e2 cinit₀ cf₀ o₀ ht₀
    have hfull₁ := terminatesTo_app_inv_full e1 e2 cinit₁ cf₁ o₁ ht₁
    cases hfull₀ with
    | @userFn c₂'₀ v₂₀ c₁₀ x₀ body₀ env₀ evalCfg₀ ht₀_e2 ht₀_e1 hNot₀ hpm1₀
        ht₀_body heq_cfg₀ hpm_e2₀ hpm_final₀ =>
        have hshape₀ : AppUserOnlyShape e1 e2 cinit₀ cf₀ o₀ := by
          left
          refine ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1,
            notExternFnAst_ne_externFn hNot₀, hpm1₀, ?_, ?_, hpm_e2₀, hpm_final₀⟩
          · simpa using ht₀_body
          · simpa using heq_cfg₀
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ evalCfg₁ ht₁_e2 ht₁_e1 hNot₁ hpm1₁
            ht₁_body heq_cfg₁ hpm_e2₁ hpm_final₁ =>
            have hshape₁ : AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ := by
              left
              refine ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
                notExternFnAst_ne_externFn hNot₁, hpm1₁, ?_, ?_, hpm_e2₁, hpm_final₁⟩
              · simpa using ht₁_body
              · simpa using heq_cfg₁
            exact finish_user_only hshape₀ hshape₁
        | @externFn c₂'₁ _v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact False.elim (by
              have hreg_c₂'₁ : c₂'₁.registry = emptyExternRegistry := by
                simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
              have hreg_c₁₁ : c₁₁.registry = emptyExternRegistry :=
                (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
              rw [hreg_c₁₁] at hGet₁
              simp [emptyExternRegistry] at hGet₁)
        | @userPfn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ evalCfg₁ ht₁_e2 ht₁_e1 _hNot₁ htoP₁
            ht₁_body heq_cfg₁ hpm_e2₁ hpm_final₁ =>
            have hshape₁ : AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ := by
              right
              refine ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
                htoP₁, ?_, heq_cfg₁, hpm_e2₁, hpm_final₁⟩
              simpa using ht₁_body
            exact finish_user_only hshape₀ hshape₁
        | @externPfn c₂'₁ v₂₁ c₁₁ x₁ y₁ id₁ argTyp₁ retSpec₁ env₁ impl₁ vRaw₁
            ht₁_e2 ht₁_e1 hGet₁ hArg₁ hImpl₁ hValRet₁ hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (pfnImpossible_under_arrow hv₁_typed)
    | @externFn c₂'₀ v₂₀ c₁₀ x₀ y₀ id₀ argTyp₀ retSpec₀ eff₀ env₀ impl₀ vRaw₀
        mem'₀ addr'₀ ht₀_e2 ht₀_e1 hpure₀ hGet₀ hArg₀ hImpl₀ hValRet₀ hcfg₀
        _hpm_e2₀ _hpm_final₀ =>
        have finish_with_side1 :
            ∀ {c₂'₁ c₁₁ : Config} {v₂₁ o₁' : Value},
              terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
              terminatesTo e1 c₂'₁ c₁₁ o₁' →
              StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
                θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
          intro c₂'₁ c₁₁ v₂₁ o₁' ht₁_e2 ht₁_e1
          exact False.elim (by
            have hreg_c₂'₀ : c₂'₀.registry = emptyExternRegistry := by
              simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
            have hreg_c₁₀ : c₁₀.registry = emptyExternRegistry :=
              (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
            rw [hreg_c₁₀] at hGet₀
            simp [emptyExternRegistry] at hGet₀)
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externFn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @userPfn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _htoP₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (pfnImpossible_under_arrow hv₁_typed)
        | @externPfn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁ _impl₁
            _vRaw₁ ht₁_e2 ht₁_e1 _hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (pfnImpossible_under_arrow hv₁_typed)
    | @userPfn c₂'₀ v₂₀ c₁₀ x₀ body₀ env₀ evalCfg₀ ht₀_e2 ht₀_e1 _hNot₀ htoP₀
        ht₀_body heq_cfg₀ hpm_e2₀ hpm_final₀ =>
        have hshape₀ : AppUserOnlyShape e1 e2 cinit₀ cf₀ o₀ := by
          right
          refine ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1,
            htoP₀, ?_, heq_cfg₀, hpm_e2₀, hpm_final₀⟩
          simpa using ht₀_body
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ evalCfg₁ ht₁_e2 ht₁_e1 hNot₁ hpm1₁
            ht₁_body heq_cfg₁ hpm_e2₁ hpm_final₁ =>
            have hshape₁ : AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ := by
              left
              refine ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
                notExternFnAst_ne_externFn hNot₁, hpm1₁, ?_, ?_, hpm_e2₁, hpm_final₁⟩
              · simpa using ht₁_body
              · simpa using heq_cfg₁
            exact finish_user_only hshape₀ hshape₁
        | @externFn _c₂'₁ _v₂₁ _c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (pfnImpossible_under_arrow hv₀_typed)
        | @userPfn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ evalCfg₁ ht₁_e2 ht₁_e1 _hNot₁ htoP₁
            ht₁_body heq_cfg₁ hpm_e2₁ hpm_final₁ =>
            have hshape₁ : AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ := by
              right
              refine ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
                htoP₁, ?_, heq_cfg₁, hpm_e2₁, hpm_final₁⟩
              simpa using ht₁_body
            exact finish_user_only hshape₀ hshape₁
        | @externPfn c₂'₁ v₂₁ c₁₁ x₁ y₁ id₁ argTyp₁ retSpec₁ env₁ impl₁ vRaw₁
            ht₁_e2 ht₁_e1 hGet₁ hArg₁ hImpl₁ hValRet₁ hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (pfnImpossible_under_arrow hv₀_typed)
    | @externPfn c₂'₀ v₂₀ c₁₀ x₀ y₀ id₀ argTyp₀ retSpec₀ env₀ impl₀ vRaw₀
        ht₀_e2 ht₀_e1 hGet₀ hArg₀ hImpl₀ hValRet₀ hcfg₀ _hpm_e2₀ _hpm_final₀ =>
        have finish_with_side1 :
            ∀ {c₂'₁ c₁₁ : Config} {v₂₁ o₁' : Value},
              terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
              terminatesTo e1 c₂'₁ c₁₁ o₁' →
              StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
                θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
          intro c₂'₁ c₁₁ v₂₁ o₁' ht₁_e2 ht₁_e1
          obtain ⟨θ₀1, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          exact False.elim (pfnImpossible_under_arrow hv₀_typed)
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externFn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @userPfn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _htoP₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externPfn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁ _impl₁
            _vRaw₁ ht₁_e2 ht₁_e1 _hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1

  | inr h_parrow =>
    -- Pure arrow case (peClosure)
    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, hp1, _hnempty, _hsub,
            hmap, heq_results, h_join⟩ := h_parrow
    have htc2' : typecheck ctxᵢ e2 fuel' = .ok result2 := by
      simpa [typecheck] using htc2
    have htc1' : typecheck (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
      simp [ctxAfter] at htc1 ⊢
      exact htc1
    intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
      o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm htagBounded result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    -- Local helper capturing the shared IH_e2 → IH_e1 ritual (parrow branch).
    -- Used by "impossible" closure/peClosure mismatch branches below.
    have mkValueHasETyp_pair :
        ∀ {c₂'₀ c₂'₁ c₁₀ c₁₁ : Config} {v₂₀ v₂₁ o₀ o₁ : Value},
          terminatesTo e2 cinit₀ c₂'₀ v₂₀ →
          terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
          terminatesTo e1 c₂'₀ c₁₀ o₀ →
          terminatesTo e1 c₂'₁ c₁₁ o₁ →
          ∃ θ₀1 θ₁1, valueHasETyp θ₀1 o₀ result1.qualType.etyp ∧
                      valueHasETyp θ₁1 o₁ result1.qualType.etyp := by
      intro c₂'₀ c₂'₁ c₁₀ c₁₁ v₂₀ v₂₁ o₀ o₁ ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
      have hstep_e2 := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
        μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
        hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
      rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, _hresTm2, hstep_e2⟩
      rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _, _, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
        hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _, _, _⟩
      have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
        simpa [ctxAfter] using BoundaryTagMeaningPost.bounded hcanon2
      have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
      have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
      have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
      obtain ⟨_, heq_cfg₀'⟩ := cfg_pureMode_eq_of_terminatesTo ht₀_e2 rfl rfl
      obtain ⟨_, heq_cfg₁'⟩ := cfg_pureMode_eq_of_terminatesTo ht₁_e2 rfl rfl
      have hstep_e1 := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
        c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
        c₁₀ c₁₁ o₀ o₁
        hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
        c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
        (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
      rcases hstep_e1 with ⟨_, _, _, _, hstep_e1⟩
      rcases hstep_e1 with ⟨θ₀1, θ₁1, _, _, hv₀1_typed, hv₁1_typed, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _⟩
      exact ⟨θ₀1, θ₁1, hv₀1_typed, hv₁1_typed⟩
    have closureImpossible_under_parrow :
        ∀ {θ1 : RealizationMap} {x : Name} {body : Expr} {env : VarEnv},
          valueHasETyp θ1 (Value.closure x body env) result1.qualType.etyp → False := by
      intro θ1 x body env hv_typed
      have hv_parrow : valueHasETyp θ1 (Value.closure x body env) (ETyp.parrow st1 st2 p tcls) := by
        simpa [hetyp1] using hv_typed
      cases hv_parrow
    have finish_user_only :
        AppUserOnlyShape e1 e2 cinit₀ cf₀ o₀ →
        AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ →
        StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
          θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
      intro hstruct₀ hstruct₁
      -- Handle runtime closure/peClosure splits for the parrow-typed branch.
      rcases hstruct₀ with h_clo₀ | h_peclo₀
      · rcases hstruct₁ with h_clo₁ | h_peclo₁
        · -- Both runs: closure (impossible under parrow typing)
          obtain ⟨c₂'₀, _, c₁₀, x₀, body₀, env₀, _, ht₀_e2, ht₀_e1, _, _, _, _, _, _⟩ := h_clo₀
          obtain ⟨c₂'₁, _, c₁₁, _, _, _, _, ht₁_e2, ht₁_e1, _, _, _, _, _, _⟩ := h_clo₁
          obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          have hv₀_parrow : valueHasETyp _ (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) :=
            hetyp1.symm ▸ hv₀_typed
          cases hv₀_parrow
        · -- Run 0: closure, Run 1: peClosure (impossible under parrow typing)
          obtain ⟨c₂'₀, _, c₁₀, x₀, body₀, env₀, _, ht₀_e2, ht₀_e1, _, _, _, _, _, _⟩ := h_clo₀
          obtain ⟨c₂'₁, _, c₁₁, _, _, _, _, ht₁_e2, ht₁_e1, _, _, _, _, _⟩ := h_peclo₁
          obtain ⟨_, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          have hv₀_parrow : valueHasETyp _ (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) :=
            hetyp1.symm ▸ hv₀_typed
          cases hv₀_parrow
      · rcases hstruct₁ with h_clo₁ | h_peclo₁
        · -- Run 0: peClosure, Run 1: closure (impossible under parrow typing)
          obtain ⟨c₂'₀, _, c₁₀, _, _, _, _, ht₀_e2, ht₀_e1, _, _, _, _, _⟩ := h_peclo₀
          obtain ⟨c₂'₁, _, c₁₁, x₁, body₁, env₁, _, ht₁_e2, ht₁_e1, _, _, _, _, _, _⟩ := h_clo₁
          obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          have hv₁_parrow : valueHasETyp _ (Value.closure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) :=
            hetyp1.symm ▸ hv₁_typed
          cases hv₁_parrow
        · -- Both runs: peClosure (the real case for parrow typing)
          obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
          obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
          -- Phase A: Apply IH for e2
          have hstep_e2 := hIH_e2 hpredlaws hExtTyping hwfTm hTmBounded
            μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
            hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ htagR hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
          rcases hstep_e2 with ⟨tm2, hcanon2, hpredlaws2, hresTm2, hstep_e2⟩
          rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, _htagBounded2, hwfcf₂₀, hwfcf₂₁,
            hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩
          have hTmBounded2 : TagMeaningBounded tm2 (ctxAfter ctxᵢ result2).nextTag := by
            simpa [ctxAfter] using BoundaryTagMeaningPost.bounded hcanon2
          -- Phase B: Apply IH for e1
          have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 _htagBounded2 result1 htc1'
          have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
          have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
          have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
          obtain ⟨hpm₀, heq_cfg₀'⟩ := cfg_pureMode_eq_of_terminatesTo ht₀_e2 rfl rfl
          obtain ⟨hpm₁, heq_cfg₁'⟩ := cfg_pureMode_eq_of_terminatesTo ht₁_e2 rfl rfl
          have hstep_e1 := hIH_e1 hpredlaws2 hExtTyping hTm2 hTmBounded2
            c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
            c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
            hθ₀2wf hθ₁2wf hwf2 _htagBounded2 hric₀2 hric₁2 htagR2 hcwr₀2 hcwr₁2 hagree2
            c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
            (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
          rcases hstep_e1 with ⟨tm1, hcanon1, hpredlaws1, _hresTm1, hstep_e1⟩
          rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, _htagBounded1, hwfcf₁₀, hwfcf₁₁,
            hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩
          -- Phase C: Invert peClosure typing to extract closure structure
          have hv₀1_parrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
          have hv₁1_parrow : valueHasETyp θ₁1 (Value.peClosure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
          -- Invert peClosure typing for both runs
          cases hv₀1_parrow with
          | peClosure_extern _ _ _ =>
            -- Same `Expr.toPExpr?` vacuity as the single-run parrow case.
            -- `peClosure_extern` forces `body₀ = Expr.externPfn …` but `htoP₀`
            -- (from the user pure-closure branch of full app inversion) requires
            -- `Expr.toPExpr? body₀ ≠ none`, which is false for extern bodies.
            exact absurd (by simp [Expr.toPExpr?]) htoP₀
          | peClosure hpure₀ htcl₀ henv₀_typing hcover₀ =>
          cases hv₁1_parrow with
          | peClosure_extern _ _ _ =>
            -- Same vacuity argument for side 1 via `htoP₁`.
            exact absurd (by simp [Expr.toPExpr?]) htoP₁
          | peClosure hpure₁ htcl₁ henv₁_typing hcover₁ =>
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
            fun hclean1_e1 => by
              rcases
                stepFR_app_parrow_sync_from_clean_with_extern
                  (predSat := predSat)
                  (ctx := (ctxAfter ctxᵢ result2))
                  (res1 := result1)
                  (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
                  (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
                  (θ₀ := θ₀1) (θ₁ := θ₁1)
                  (x₀ := x₀) (x₁ := x₁)
                  (body₀ := body₀) (body₁ := body₁)
                  (env₀ := env₀) (env₁ := env₁)
                  hetyp1 hclean1_e1 hres_agree1 with hsync | hdirty
              · rcases hsync with hregular | hextern
                · left
                  exact hregular
                · rcases hextern with
                    ⟨_id, _x, _y, _argTyp, _retSpec, _σcap, _hmem,
                      _hx₀, _hx₁, hbody₀, _hbody₁, _hcap⟩
                  exact False.elim (htoP₀ (by rw [hbody₀]; simp [Expr.toPExpr?]))
              · right
                exact hdirty
          have _sync_extract_of_clean :
              ∀ hclean1_e1 :
                  qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                (∃ x pbody σcap cursorShared fuelBody firstShared result3Shared,
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
                    result1.nextTag' ≤ cursorShared.1 ∧
                    result1.nextLoc' ≤ cursorShared.2 ∧
                    firstShared ∈ results ∧
                    applyPFnTClosureAtCursor (PFnTClosure.regular x pbody σcap) st1 st2 p p1
                      etyp2 p2 pred2 ctxᵢ result1 cursorShared fuel' = .ok firstShared ∧
                    fuel' = Nat.succ fuelBody ∧
                    typecheckExpr
                      { ctxᵢ with
                        pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                        memEnv := result1.memEnv'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                        tagEnv := result1.tagEnv'
                        pureCtx := true
                        nextTag := cursorShared.1
                        nextLoc := cursorShared.2
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
              rcases applyPFnTClosure_regular_inv_of_threaded_mem
                  ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                  x pbody σcap hmap hmem with
                ⟨cursorShared, fuelBody, firstShared, result3Shared, hcursorTag, hcursorLoc,
                  hfirstMem, happly', hfuel', htc', hsub', hfirst'⟩
              exact ⟨x, pbody, σcap, cursorShared, fuelBody, firstShared, result3Shared,
                htoPExpr, hmem, hx₀, hx₁, hbody, hcap, hmv₀, hmc₀, hmv₁, hmc₁,
                hcursorTag, hcursorLoc, hfirstMem, happly', hfuel', htc', hsub', hfirst'⟩
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
            threaded_applyPFnTClosure_forall_wfTypeResult
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
          have hresults_regime :
              ∀ r, r ∈ results →
                regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
            have htagR1_ctx :
                regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
              simpa [ctxAfter] using htagR1
            exact
              threaded_applyPFnTClosure_forall_regimeConsistentWithCtx
                (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                (result1 := result1) (fuel := fuel')
                (tcls := tcls) (results := results)
                htagR1_ctx hmap
          have hfirst_in_results : first ∈ results := by
            simp [heq_results]
          have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
          have h_first_regime :
              regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
            hresults_regime first hfirst_in_results
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
              ∃ tm',
                IsCanonicalExtension tm ctxᵢ (Expr.app e1 e2) res tm' ∧
                PredSatLaws predSat tm' ∧
                QTypRespectsTagMeaning tm' res.qualType ∧
                ∃ θ₀' θ₁',
                  wfExtendsMap θ₀ θ₀' ∧
                  wfExtendsMap θ₁ θ₁' ∧
                  valueHasETyp θ₀' o₀ res.qualType.etyp ∧
                  valueHasETyp θ₁' o₁ res.qualType.etyp ∧
                  wfTagMeaningCtx tm' (ctxAfter ctxᵢ res) ∧
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
            rcases applyClosuresThreaded_ok_mem_output_exists_input
                (applyOne := fun tcl cursor =>
                  applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 cursor fuel')
                (hthread := hmap) (hmem := hfirst_in_results)
              with ⟨tcl, _htcl_mem, cursorFirst, happly_first_cursor⟩
            let result1CursorFirst : TypeResult :=
              { result1 with nextTag' := cursorFirst.1, nextLoc' := cursorFirst.2 }
            have happly_first :
                applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                  ctxᵢ result1CursorFirst fuel' = .ok first := by
              unfold applyPFnTClosure
              unfold applyPFnTClosureAtCursor at happly_first_cursor
              simpa [result1CursorFirst] using happly_first_cursor
            have hfirst_pack :
                first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
              applyPFnTClosure_ok_poison_pred_of_p1p_true
                (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                (result2 := result1CursorFirst) (fuel := fuel') (tcl := tcl) (r := first)
                h_p1p happly_first
            have hres_pack :
                res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred :=
              joinTypeResults_poison_pred_of_head_true_noPred
                (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join hfirst_pack.1 hfirst_pack.2
            -- ===== Per-run body IH for not qtypCleanUnder (p1=true) =====
            -- Extract σcap + pbody from closureCapturedVarsRegime for each run.
            have ⟨σcapA₀, pbodyA₀, htoPExprA₀, hσcapA₀_mem, hσcapA₀_regime, hσcapA₀_typing, hσcapA₀_rec⟩ :=
              closureCapturedVarsRegime_peClosure_extract hetyp1 htoP₀
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
            have ⟨σcapA₁, pbodyA₁, htoPExprA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
              closureCapturedVarsRegime_peClosure_extract hetyp1 htoP₁
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
            -- body₀ = PExpr.toExpr pbodyA₀ (and similarly for body₁)
            have hbody₀_eq : PExpr.toExpr pbodyA₀ = body₀ :=
              PExpr_toExpr_of_toPExpr?_some body₀ pbodyA₀ htoPExprA₀
            have hbody₁_eq : PExpr.toExpr pbodyA₁ = body₁ :=
              PExpr_toExpr_of_toPExpr?_some body₁ pbodyA₁ htoPExprA₁
            -- Get body typing for σcapA₀ and σcapA₁ from applyPFnTClosure
            rcases applyPFnTClosure_regular_inv_of_threaded_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₀ pbodyA₀ σcapA₀ hmap hσcapA₀_mem with
              ⟨cursorA₀, fuelBodyA₀, firstA₀, result3A₀, hcursorTagA₀, hcursorLocA₀,
                hfirstA₀_mem, happlyA₀, hfuelA₀, htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
            rcases applyPFnTClosure_regular_inv_of_threaded_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₁ pbodyA₁ σcapA₁ hmap hσcapA₁_mem with
              ⟨cursorA₁, fuelBodyA₁, firstA₁, result3A₁, hcursorTagA₁, hcursorLocA₁,
                hfirstA₁_mem, happlyA₁, hfuelA₁, htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
            let result1CursorA₀ : TypeResult :=
              { result1 with nextTag' := cursorA₀.1, nextLoc' := cursorA₀.2 }
            have happlyA₀_old :
                applyPFnTClosure (PFnTClosure.regular x₀ pbodyA₀ σcapA₀)
                  st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1CursorA₀ fuel' = .ok firstA₀ := by
              unfold applyPFnTClosure
              unfold applyPFnTClosureAtCursor at happlyA₀
              simpa [result1CursorA₀] using happlyA₀
            let result1CursorA₁ : TypeResult :=
              { result1 with nextTag' := cursorA₁.1, nextLoc' := cursorA₁.2 }
            have happlyA₁_old :
                applyPFnTClosure (PFnTClosure.regular x₁ pbodyA₁ σcapA₁)
                  st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1CursorA₁ fuel' = .ok firstA₁ := by
              unfold applyPFnTClosure
              unfold applyPFnTClosureAtCursor at happlyA₁
              simpa [result1CursorA₁] using happlyA₁
            -- Get membership in first :: rest (for join transport)
            have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
              simpa [heq_results] using hfirstA₀_mem
            have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
              simpa [heq_results] using hfirstA₁_mem
            -- Define body contexts (parrow: pc has ctxᵢ.pc before p1, pureCtx := true)
            let bodyCtxA₀ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                pureCtx := true
                nextTag := cursorA₀.1
                nextLoc := cursorA₀.2
                regime := result1.regime' }
            let bodyCtxA₁ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                pureCtx := true
                nextTag := cursorA₁.1
                nextLoc := cursorA₁.2
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
            have hTmBodyA₀ : wfTagMeaningCtx tm1 bodyCtxA₀ := by
              have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := _hresTm1
              have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
              have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (QTypRespectsTagMeaning_mono
                    (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg)
                  rfl rfl
              simpa [bodyCtxA₀, ctxAfter] using
                wfTagMeaningCtx_pclosure_body
                  (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
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
              exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA₀),
                varEnvRefLocsBounded_update
                  (varEnvRefLocsBounded_ofCaptured
                    (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                      (CapturedEnvRefLocsFullBounded_mono
                        (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)
                        hcursorLocA₀)))
                  (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypRefLocsBounded_mono h
                        (Nat.le_trans hmono_e1 hcursorLocA₀)),
                varEnvClosuresCapturedRefLocsBounded_update
                  (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                    (CapturedEnvRefLocsFullBounded_mono
                      (by rw [hetyp1] at hClosRL; exact hClosRL _ hσcapA₀_mem)
                      hcursorLocA₀))
                  (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                        (Nat.le_trans hmono_e1 hcursorLocA₀))⟩
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
                      nextLoc := cursorA₀.2
                      nextTag := cursorA₀.1
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
            -- Thread extern registry: after `subst heq_cfg₀`, cf₀ replaces c₁₀.
            have hreg_cf₀_pp : cf₀.registry = emptyExternRegistry := by
              have h2 : c₂'₀.registry = emptyExternRegistry := by
                simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
              exact (terminatesTo_preserves_registry ht₀_e1).trans h2
            rw [hreg_cf₀_pp] at ht₀_body
            -- The body terminatesTo uses body₀, but init config has pureMode := true
            have ht₀_body' : terminatesTo body₀
                { memory := cf₀.memory, varEnv := env₀.update x₀ v₂₀,
                  nextAddr := cf₀.nextAddr, pureMode := true } evalCfg₀ o₀ := ht₀_body
            have hSingle_bodyA₀ :=
              singleIH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀
                (by simpa [bodyCtxA₀] using
                  (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₀)
                result3A₀ htcBodyA₀_body₀
            have hpc_bodyA₀_run : bodyCtxA₀.pc = true := by
              simp [bodyCtxA₀, joinPoison] at h_p1p ⊢
              cases p1 <;> cases p <;> simp at h_p1p ⊢
            have hsr₀ :=
              (hSingle_bodyA₀ hpredlaws1 hExtTyping hTmBodyA₀
                (by simpa [bodyCtxA₀] using
                  (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₀)).2
                cf₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
                hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀
                hcwr_bodyA₀ cf₀.nextAddr true hwfcfg_body_initA₀ ht₀_body'
                hpc_bodyA₀_run
            rcases hsr₀ with
              ⟨θ₀_body, hθext₀_body, hv₀_body_typed,
                hric_bodyA₀_final, hcwr_bodyA₀_final, hvalc_bodyA₀, hpres₀, _hfresh₀_body⟩
            -- ===== Run 1: unary body witness =====
            have hTmBodyA₁ : wfTagMeaningCtx tm1 bodyCtxA₁ := by
              have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := _hresTm1
              have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
              have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm1) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (QTypRespectsTagMeaning_mono
                    (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg)
                  rfl rfl
              simpa [bodyCtxA₁, ctxAfter] using
                wfTagMeaningCtx_pclosure_body
                  (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
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
              exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorLocA₁),
                varEnvRefLocsBounded_update
                  (varEnvRefLocsBounded_ofCaptured
                    (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                      (CapturedEnvRefLocsFullBounded_mono
                        (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))
                        hcursorLocA₁)))
                  (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypRefLocsBounded_mono h
                        (Nat.le_trans hmono_e1 hcursorLocA₁)),
                varEnvClosuresCapturedRefLocsBounded_update
                  (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                    (CapturedEnvRefLocsFullBounded_mono
                      (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))
                      hcursorLocA₁))
                  (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                      rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                        (Nat.le_trans hmono_e1 hcursorLocA₁))⟩
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
                      nextLoc := cursorA₁.2
                      nextTag := cursorA₁.1
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
            -- Thread extern registry: after `subst heq_cfg₁`, cf₁ replaces c₁₁.
            have hreg_cf₁_pp : cf₁.registry = emptyExternRegistry := by
              have h2 : c₂'₁.registry = emptyExternRegistry := by
                simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
              exact (terminatesTo_preserves_registry ht₁_e1).trans h2
            rw [hreg_cf₁_pp] at ht₁_body
            have ht₁_body' : terminatesTo body₁
                { memory := cf₁.memory, varEnv := env₁.update x₁ v₂₁,
                  nextAddr := cf₁.nextAddr, pureMode := true } evalCfg₁ o₁ := ht₁_body
            have hSingle_bodyA₁ :=
              singleIH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁
                (by simpa [bodyCtxA₁] using
                  (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₁)
                result3A₁ htcBodyA₁_body₁
            have hpc_bodyA₁_run : bodyCtxA₁.pc = true := by
              simp [bodyCtxA₁, joinPoison] at h_p1p ⊢
              cases p1 <;> cases p <;> simp at h_p1p ⊢
            have hsr₁ :=
              (hSingle_bodyA₁ hpredlaws1 hExtTyping hTmBodyA₁
                (by simpa [bodyCtxA₁] using
                  (BoundaryTagMeaningPost.bounded hcanon1).mono hcursorTagA₁)).2
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
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
              regime_lookup_back_of_monotone hres1_to_firstA₀_mono
            have hlookup_back_res1_to_A₁ :
                ∀ k b,
                  (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
              regime_lookup_back_of_monotone hres1_to_firstA₁_mono
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
            rcases typecheck_preserves_predSatLaws hExtTyping predSat tm ctxᵢ
                (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
                hwfTm hTmBounded hpredlaws htc with
              ⟨tmOut, hcanonOut, hpredlawsOut⟩
            exact ⟨tmOut, hcanonOut, hpredlawsOut,
              IsCanonicalExtension.respectsResult hcanonOut,
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
              -- wfTagMeaningCtx tmOut (ctxAfter ctxᵢ res)
              IsCanonicalExtension.wfCtx hcanonOut,
              -- wfTypeContext (ctxAfter ctxᵢ res)
              join_transport_wfTypeContext ctxᵢ first rest res h_join h_mem_join
                (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                  (Nat.le_trans
                    (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                      (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                    (threaded_applyPFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
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
                exact
                  appMember_runtimeInstantiatesCtx_from_body
                    (ctx := ctxᵢ)
                    (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                    (bodyFinalCtx := ctxAfter bodyCtxA₀ result3A₀)
                    (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := cf₀)
                    (θpre := θ₀1) (θbody := θ₀_body)
                    h_join hfirstA₀_mem' hric_bodyA₀_final hric₀1
                    (fun l hcontains_body => by
                      simpa [ctxAfter, hfirstA₀_eq] using hcontains_body)
                    (fun x qt hlookup => by
                      simpa [ctxAfter] using hlookup)
                    hmem₀_eq rfl hθext₀_body,
              -- runtimeInstantiatesCtx run 1
              by
                exact
                  appMember_runtimeInstantiatesCtx_from_body
                    (ctx := ctxᵢ)
                    (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                    (bodyFinalCtx := ctxAfter bodyCtxA₁ result3A₁)
                    (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := cf₁)
                    (θpre := θ₁1) (θbody := θ₁_body)
                    h_join hfirstA₁_mem' hric_bodyA₁_final hric₁1
                    (fun l hcontains_body => by
                      simpa [ctxAfter, hfirstA₁_eq] using hcontains_body)
                    (fun x qt hlookup => by
                      simpa [ctxAfter] using hlookup)
                    hmem₁_eq rfl hθext₁_body,
              -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
              join_transport_regimeConsistentWithCtx ctxᵢ first rest res h_join
                h_tag_join h_first_regime,
              -- consistentWithRegime run 0
              by
                exact
                  appMember_consistentWithRegime_from_body
                    (predSat := predSat)
                    (ctx := ctxᵢ)
                    (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                    (bodyFinalCtx := ctxAfter bodyCtxA₀ result3A₀)
                    (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := cf₀)
                    (θpre := θ₀1) (θbody := θ₀_body)
                    h_join hfirstA₀_mem' hcwr_bodyA₀_final hcwr₀1
                    (fun l qt hlookup => by
                      simpa [ctxAfter, hfirstA₀_eq] using hlookup)
                    (fun k b hk_src => by
                      simpa [ctxAfter, hfirstA₀_eq] using hk_src)
                    (fun k b hk_body => by
                      simpa [ctxAfter, hfirstA₀_eq] using hk_body)
                    (fun x qt hlookup => by
                      simpa [ctxAfter] using hlookup)
                    hlookup_back_res1_to_A₀ hpred_compat₀ hmem₀_eq rfl hθext₀_body,
              -- consistentWithRegime run 1
              by
                exact
                  appMember_consistentWithRegime_from_body
                    (predSat := predSat)
                    (ctx := ctxᵢ)
                    (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                    (bodyFinalCtx := ctxAfter bodyCtxA₁ result3A₁)
                    (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := cf₁)
                    (θpre := θ₁1) (θbody := θ₁_body)
                    h_join hfirstA₁_mem' hcwr_bodyA₁_final hcwr₁1
                    (fun l qt hlookup => by
                      simpa [ctxAfter, hfirstA₁_eq] using hlookup)
                    (fun k b hk_src => by
                      simpa [ctxAfter, hfirstA₁_eq] using hk_src)
                    (fun k b hk_body => by
                      simpa [ctxAfter, hfirstA₁_eq] using hk_body)
                    (fun x qt hlookup => by
                      simpa [ctxAfter] using hlookup)
                    hlookup_back_res1_to_A₁ hpred_compat₁ hmem₁_eq rfl hθext₁_body,
              -- agreeOnClean for ¬qtypCleanUnder (p1=true, parrow, different closure bodies)
              by
                -- Regime monotonicity: result1.regime' → res.regime' (through the join)
                have h_all_members_mono :
                    ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                  intro x hx
                  have hxResults : x ∈ results := by
                    simpa [heq_results] using hx
                  rcases applyClosuresThreaded_ok_mem_output_exists_input
                      (applyOne := fun tcl cursor =>
                        applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                          ctxᵢ result1 cursor fuel')
                      (xs := tcls) (cursor := (result1.nextTag', result1.nextLoc'))
                      (results := results) (y := x) hmap hxResults with
                    ⟨tcl, _htcl_mem, cursor, happly⟩
                  exact applyPFnTClosureAtCursor_regime_mono tcl ctxᵢ st1 st2 p p1
                      etyp2 p2 pred2 result1 x cursor fuel'
                      (fun m _hlt e ctx' res' htc =>
                        by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                      happly
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
                      · rcases applyClosuresThreaded_ok_mem_output_exists_input
                            (applyOne := fun tcl cursor =>
                              applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                                ctxᵢ result1 cursor fuel')
                            (hthread := hmap)
                            (hmem := (show first ∈ results by
                              rw [heq_results]; exact List.Mem.head rest))
                          with ⟨tcl, _, cursor, happlyCursor⟩
                        let result1Cursor : TypeResult :=
                          { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
                        have happly :
                            applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                              ctxᵢ result1Cursor fuel' = .ok first := by
                          unfold applyPFnTClosure
                          unfold applyPFnTClosureAtCursor at happlyCursor
                          simpa [result1Cursor] using happlyCursor
                        exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                          pred2 result1Cursor fuel' tcl first happly l hfirst
                      · rcases applyClosuresThreaded_ok_mem_output_exists_input
                            (applyOne := fun tcl cursor =>
                              applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                                ctxᵢ result1 cursor fuel')
                            (hthread := hmap)
                            (hmem := (by rw [heq_results]; exact List.mem_cons_of_mem first hr))
                          with ⟨tcl, _, cursor, happlyCursor⟩
                        let result1Cursor : TypeResult :=
                          { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
                        have happly :
                            applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2
                              ctxᵢ result1Cursor fuel' = .ok r := by
                          unfold applyPFnTClosure
                          unfold applyPFnTClosureAtCursor at happlyCursor
                          simpa [result1Cursor] using happlyCursor
                        exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                          pred2 result1Cursor fuel' tcl r happly l hrl
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
                        etyp2 p2 pred2 result1CursorA₀ fuel'
                        (PFnTClosure.regular x₀ pbodyA₀ σcapA₀) firstA₀
                        happlyA₀_old l qt' (by simpa [result1CursorA₀] using hlookup_body)
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
                        etyp2 p2 pred2 result1CursorA₁ fuel'
                        (PFnTClosure.regular x₁ pbodyA₁ σcapA₁) firstA₁
                        happlyA₁_old l qt' (by simpa [result1CursorA₁] using hlookup_body)
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
                            | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | dirty_internal_arrow _ hisA htyp₀ _ =>
                              simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                            | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ hv₀ _ =>
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
                exact
                  appMember_valueConsistentWithRegime_from_body
                    (predSat := predSat)
                    (ctx := ctxᵢ) (bodyCtx := bodyCtxA₀)
                    (first := first) (src := firstA₀) (result3 := result3A₀)
                    (rest := rest) (res := res)
                    (cf := cf₀) (evalCfg := evalCfg₀) (θ := θ₀_body) (o := o₀)
                    (p := p) (p1 := p1)
                    h_join hfirstA₀_mem' hfirstA₀_eq hmem₀_eq hvalc_bodyA₀,
              -- valueConsistentWithRegime run 1
              by
                exact
                  appMember_valueConsistentWithRegime_from_body
                    (predSat := predSat)
                    (ctx := ctxᵢ) (bodyCtx := bodyCtxA₁)
                    (first := first) (src := firstA₁) (result3 := result3A₁)
                    (rest := rest) (res := res)
                    (cf := cf₁) (evalCfg := evalCfg₁) (θ := θ₁_body) (o := o₁)
                    (p := p) (p1 := p1)
                    h_join hfirstA₁_mem' hfirstA₁_eq hmem₁_eq hvalc_bodyA₁,
              -- resultAgreesIfClean (vacuously true since poison=true and pred=noPred)
              resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
          by_cases hclean1_e1 :
              qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
          · -- Clean case: shared pure-body IH (TODO: fill later)
            rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
            · rcases hshared with
                ⟨x, pbody, σcap, cursorShared, fuelBody, firstShared, result3Shared,
                  htoPExpr, hmem, hx₀, hx₁, hbody,
                  hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                  hcursorSharedTag, hcursorSharedLoc, hfirstSharedMem,
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
                  nextTag := cursorShared.1
                  nextLoc := cursorShared.2
                  regime := result1.regime' }
              have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
              have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
              have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
                have hfuel_lt' : fuelBody < fuel' := by
                  rw [hfuel]
                  exact Nat.lt_succ_self fuelBody
                exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              have hargTm : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
                have hresTm2_arg : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                  simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm2 result2.qualType)
                have hresTm2_arg' : QTypRespectsTagMeaning tm1 ⟨etyp2, p2, pred2⟩ :=
                  QTypRespectsTagMeaning_mono
                    (BoundaryTagMeaningPost.extends_tm hcanon1) hresTm2_arg
                have hargTm' :
                    ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                      QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                      qtypGuardDesc? qt' = some (k, d) →
                      tm1.lookup k = some d :=
                  QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm1)
                    (qt := ⟨etyp2, p2, pred2⟩)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    hresTm2_arg' rfl rfl
                exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
              have hTmBody : wfTagMeaningCtx tm1 bodyCtx := by
                have hresTm1' : QTypRespectsTagMeaning tm1 result1.qualType := _hresTm1
                have hTmBody' :=
                  wfTagMeaningCtx_pclosure_body
                    (tm := tm1) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
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
                  have hCapBoundBase : CapturedEnvFullBounded σcap result1.nextTag' := hClosFull _ hmem
                  have hCapBound : CapturedEnvFullBounded σcap cursorShared.1 :=
                    CapturedEnvFullBounded_mono hCapBoundBase hcursorSharedTag
                  have hCapPred := capturedPredTagsBounded_of_fullBounded hCapBound
                  have hmono_r2_r1 : result2.nextTag' ≤ result1.nextTag' :=
                    typecheck_normal_nextTag_mono (ctxAfter ctxᵢ result2) e1 fuel' result1
                      (by simpa [typecheck] using htc1')
                  have hArgPredBase :
                      qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                        result1.nextTag' := by
                    have := (typecheckExpr_preserves_predTagsBounded ctxᵢ e2 fuel' result2
                      (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2).2
                    rw [hqt2] at this
                    exact qtypPredTagBounded_mono this hmono_r2_r1
                  have hArgPred :
                      qtypPredTagBounded ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                        cursorShared.1 :=
                    qtypPredTagBounded_mono hArgPredBase hcursorSharedTag
                  have hArgClosBase :
                      etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp
                        result1.nextTag' := by
                    have := typecheckExpr_preserves_closureCapturedBounded ctxᵢ e2 fuel' result2
                      (by simpa [typecheck] using htc2') htagBounded.2.1 htagBounded.2.2
                    rw [hqt2] at this; exact etypClosuresFullBounded_mono this hmono_r2_r1
                  have hArgClos :
                      etypClosuresFullBounded (⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ : QTyp).etyp
                        cursorShared.1 :=
                    etypClosuresFullBounded_mono hArgClosBase hcursorSharedTag
                  refine ⟨?_,
                    ⟨predTagsBoundedInVarEnv_update
                      (predTagsBoundedInVarEnv_ofCaptured hCapPred) hArgPred,
                     ?_⟩,
                    varEnvClosuresCapturedBounded_update
                      (varEnvClosuresCapturedBounded_ofCaptured hCapBound) hArgClos⟩
                  · simpa [bodyCtx, ctxAfter] using
                      tagEnvBounded_mono result1.tagEnv' result1.nextTag' cursorShared.1
                        (by simpa [ctxAfter] using hb_tag1) hcursorSharedTag
                  · simpa [bodyCtx, ctxAfter] using
                      predTagsBoundedInMemEnv_mono
                        (by simpa [ctxAfter] using hb_predM1) hcursorSharedTag
              have hIH_body :=
                IH fuelBody hfuel_lt (PExpr.toExpr pbody) bodyCtx hTmBody htagBoundedBody result3Shared htcBody'
              have hTmBoundedBody : TagMeaningBounded tm1 bodyCtx.nextTag := by
                have hbase : TagMeaningBounded tm1 result1.nextTag' :=
                  BoundaryTagMeaningPost.bounded hcanon1
                simpa [bodyCtx, ctxAfter] using hbase.mono hcursorSharedTag
              have hwfBodyCtx : wfTypeContext bodyCtx := by
                simp only [bodyCtx, wfTypeContext]
                have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                  (ctxAfter ctxᵢ result2) e1 fuel' result1 hwf2 htc1'
                have hmono_e1 := typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
                exact ⟨(fun l hl => Nat.lt_of_lt_of_le (hwf1.1 l hl) hcursorSharedLoc),
                  varEnvRefLocsBounded_update
                    (varEnvRefLocsBounded_ofCaptured
                      (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                        (CapturedEnvRefLocsFullBounded_mono
                          (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))
                          hcursorSharedLoc)))
                    (by have h := typecheckExpr_preserves_etypRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorSharedLoc)),
                  varEnvClosuresCapturedRefLocsBounded_update
                    (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                      (CapturedEnvRefLocsFullBounded_mono
                        (by rw [hetyp1] at hClosRL; exact hClosRL _ (by assumption))
                        hcursorSharedLoc))
                    (by have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctxᵢ e2 fuel' result2 hwf htc2'
                        rw [hqt2] at h; exact etypClosuresCapturedRefLocsBounded_mono h
                          (Nat.le_trans hmono_e1 hcursorSharedLoc))⟩
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
                        nextLoc := cursorShared.2
                        nextTag := cursorShared.1
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
                        nextLoc := cursorShared.2
                        nextTag := cursorShared.1
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
              -- Thread extern registry: after subst heq_cfg, cf₀/cf₁ replace c₁₀/c₁₁.
              have hreg_cf₀_pp2 : cf₀.registry = emptyExternRegistry := by
                have h2 : c₂'₀.registry = emptyExternRegistry := by
                  simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
                exact (terminatesTo_preserves_registry ht₀_e1).trans h2
              have hreg_cf₁_pp2 : cf₁.registry = emptyExternRegistry := by
                have h2 : c₂'₁.registry = emptyExternRegistry := by
                  simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
                exact (terminatesTo_preserves_registry ht₁_e1).trans h2
              rw [hreg_cf₀_pp2] at ht₀_body
              rw [hreg_cf₁_pp2] at ht₁_body
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
              have hstep_body := hIH_body hpredlaws1 hExtTyping hTmBody hTmBoundedBody
                cf₀.memory cf₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
                evalCfg₀ evalCfg₁ o₀ o₁
                hθ₀1wf hθ₁1wf hwfBodyCtx htagBoundedBody hric_body₀ hric_body₁ htagR_body
                hcwr_body₀ hcwr_body₁ hagree_body_start
                cf₀.nextAddr cf₁.nextAddr true
                hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
              rcases hstep_body with ⟨_tm_body, _hcanon_body, _hpredlaws_body, _hresTm_body, hstep_body⟩
              rcases hstep_body with
                ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                  _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after, _htagBounded_body_after,
                  _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                  _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                  _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                  _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩
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
                  ∀ θ₀_body θ₁_body,
                    wfExtendsMap θ₀1 θ₀_body →
                    wfExtendsMap θ₁1 θ₁_body →
                    runtimeInstantiatesCtx (ctxAfter bodyCtx result3Shared)
                      evalCfg₀.memory evalCfg₀.varEnv θ₀_body →
                    runtimeInstantiatesCtx (ctxAfter bodyCtx result3Shared)
                      evalCfg₁.memory evalCfg₁.varEnv θ₁_body →
                    agreeOnClean predSat (ctxAfter bodyCtx result3Shared).regime
                      (ctxAfter bodyCtx result3Shared)
                      evalCfg₀.memory evalCfg₀.varEnv θ₀_body
                      evalCfg₁.memory evalCfg₁.varEnv θ₁_body →
                    agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                      cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                intro θ₀_body θ₁_body _hθext₀_body _hθext₁_body
                  _hric_body_final₀ _hric_body_final₁ hagree_body_after
                have hsrc_mem : firstShared ∈ first :: rest := by
                  simpa [heq_results] using hfirstSharedMem
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
                  True ∧
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
                    cf₀.memory cf₁.memory θ₀_body θ₁_body res.qualType o₀ o₁ ∧
                  ∃ tm', IsCanonicalExtension tm ctxᵢ (Expr.app e1 e2) res tm' ∧
                    PredSatLaws predSat tm' := by
                have hsrc_mem' : firstShared ∈ first :: rest := by
                  simpa [heq_results] using hfirstSharedMem
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
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                  regime_lookup_back_of_monotone hres1_to_src_mono
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                  hAgree_out_body θ₀_body θ₁_body _hθext₀_body _hθext₁_body
                    _hric_body_final₀ _hric_body_final₁ hagree_body_after, ?_, ?_, ?_, ?_⟩
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
                · trivial
                · -- wfTypeContext (ctxAfter ctxᵢ res)
                  exact
                    join_transport_wfTypeContext
                      (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                      h_join h_mem_join
                      (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf hwf
                  (Nat.le_trans
                    (Nat.le_trans (typecheck_nextLoc_mono ctxᵢ e2 fuel' result2 htc2')
                      (typecheck_nextLoc_mono (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'))
                    (threaded_applyPFnTClosure_member_nextLoc_mono st1 st2 p p1 etyp2 p2 pred2
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
                  exact
                    appMember_runtimeInstantiatesCtx_from_body
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                      (first := first) (src := firstShared) (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := cf₀)
                      (θpre := θ₀1) (θbody := θ₀_body)
                      h_join hsrc_mem' _hric_body_final₀ hric₀1
                      (fun l hcontains_src_body => by
                        simpa [ctxAfter, hfirstShared] using hcontains_src_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hmem₀_eq hvar₀_eq _hθext₀_body
                · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                  have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                  exact
                    appMember_runtimeInstantiatesCtx_from_body
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                      (first := first) (src := firstShared) (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := cf₁)
                      (θpre := θ₁1) (θbody := θ₁_body)
                      h_join hsrc_mem' _hric_body_final₁ hric₁1
                      (fun l hcontains_src_body => by
                        simpa [ctxAfter, hfirstShared] using hcontains_src_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hmem₁_eq hvar₁_eq _hθext₁_body
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
                  exact
                    appMember_consistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                      (first := first) (src := firstShared) (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (preCfg := cf₀)
                      (θpre := θ₀1) (θbody := θ₀_body)
                      h_join hsrc_mem' _hcwr_body_final₀ hcwr₀1
                      (fun l qt hlookup => by
                        simpa [ctxAfter, hfirstShared] using hlookup)
                      (fun k b hk_src => by
                        simpa [ctxAfter, hfirstShared] using hk_src)
                      (fun k b hk_body => by
                        simpa [ctxAfter, hfirstShared] using hk_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hlookup_back_res1_to_src hpred_compat₀ hmem₀_eq hvar₀_eq _hθext₀_body
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
                  exact
                    appMember_consistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ)
                      (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                      (bodyFinalCtx := ctxAfter bodyCtx result3Shared)
                      (first := first) (src := firstShared) (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (preCfg := cf₁)
                      (θpre := θ₁1) (θbody := θ₁_body)
                      h_join hsrc_mem' _hcwr_body_final₁ hcwr₁1
                      (fun l qt hlookup => by
                        simpa [ctxAfter, hfirstShared] using hlookup)
                      (fun k b hk_src => by
                        simpa [ctxAfter, hfirstShared] using hk_src)
                      (fun k b hk_body => by
                        simpa [ctxAfter, hfirstShared] using hk_body)
                      (fun x qt hlookup => by
                        simpa [ctxAfter] using hlookup)
                      hlookup_back_res1_to_src hpred_compat₁ hmem₁_eq hvar₁_eq _hθext₁_body
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                  exact
                    appMember_valueConsistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                      (first := first) (src := firstShared) (result3 := result3Shared)
                      (rest := rest) (res := res)
                      (cf := cf₀) (evalCfg := evalCfg₀) (θ := θ₀_body) (o := o₀)
                      (p := p) (p1 := p1)
                      h_join hsrc_mem' hfirstShared hmem₀_eq _hvalc_body₀
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                  exact
                    appMember_valueConsistentWithRegime_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                      (first := first) (src := firstShared) (result3 := result3Shared)
                      (rest := rest) (res := res)
                      (cf := cf₁) (evalCfg := evalCfg₁) (θ := θ₁_body) (o := o₁)
                      (p := p) (p1 := p1)
                      h_join hsrc_mem' hfirstShared hmem₁_eq _hvalc_body₁
                · -- shared-member resultAgreesIfClean -> joined result qualType.
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                  exact
                    appMember_resultAgreesIfClean_from_body
                      (predSat := predSat)
                      (ctx := ctxᵢ) (bodyCtx := bodyCtx)
                      (first := first) (src := firstShared) (result3 := result3Shared)
                      (rest := rest) (res := res)
                      (cf₀ := cf₀) (cf₁ := cf₁) (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
                      (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                      (p := p) (p1 := p1)
                      h_join hsrc_mem' hfirstShared hmem₀_eq hmem₁_eq _hres_agree_body
                · exact
                    typecheck_preserves_predSatLaws hExtTyping predSat tm ctxᵢ
                      (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
                      hwfTm hTmBounded hpredlaws htc
              rcases typecheck_preserves_predSatLaws hExtTyping predSat tm ctxᵢ
                  (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) res
                  hwfTm hTmBounded hpredlaws htc with
                ⟨tmOut, hcanonOut, hpredlawsOut⟩
              rcases hOutPack_body with
                ⟨_hv_body_out₀, _hv_body_out₁, _hwfTmOld, hwfFinal, htagBoundedFinal,
                  hwfcfFinal₀, hwfcfFinal₁, _hricFinal₀, _hricFinal₁, htagFinal,
                  _hcwrFinal₀, _hcwrFinal₁, _hagreeFinal, _hvalcFinal₀, _hvalcFinal₁,
                  _hresAgreeFinal, _hcanonOld⟩
              have hbody_post_for_transport :
                  StepFRPost bodyCtx (PExpr.toExpr pbody) result3Shared predSat tm1
                    θ₀1 θ₁1 evalCfg₀ evalCfg₁ o₀ o₁ := by
                exact ⟨_tm_body, _hcanon_body, _hpredlaws_body, _hresTm_body,
                  θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                  _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after,
                  _htagBounded_body_after, _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                  _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                  _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                  _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩
              have hOutChoice_body_from_helper :
                  AppTwoRunOutChoice predSat ctxᵢ res θ₀1 θ₁1 cf₀ cf₁ o₀ o₁ := by
                have hsrc_mem' : firstShared ∈ first :: rest := by
                  simpa [heq_results] using hfirstSharedMem
                have hres1_to_src_mono :
                    Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      (ctxAfter ctxᵢ firstShared).regime := by
                  have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                    regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3Shared htcBody'
                  simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                have hlookup_back_res1_to_src :
                    ∀ k b,
                      (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b :=
                  regime_lookup_back_of_monotone hres1_to_src_mono
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
                exact
                  appTwoRunOutChoice_from_body_stepFRPost
                    (predSat := predSat) (tmBody := tm1)
                    (ctx := ctxᵢ)
                    (preCtx := ctxAfter (ctxAfter ctxᵢ result2) result1)
                    (bodyCtx := bodyCtx)
                    (postExpr := PExpr.toExpr pbody)
                    (first := first) (src := firstShared) (result3 := result3Shared)
                    (rest := rest) (res := res)
                    (cf₀ := cf₀) (cf₁ := cf₁)
                    (evalCfg₀ := evalCfg₀) (evalCfg₁ := evalCfg₁)
                    (preCfg₀ := cf₀) (preCfg₁ := cf₁)
                    (θpre₀ := θ₀1) (θpre₁ := θ₁1)
                    (o₀ := o₀) (o₁ := o₁) (p := p) (p1 := p1)
                    h_join hsrc_mem' hfirstShared hlookup_back_res1_to_src
                    (fun x qt hlookup => by
                      simpa [ctxAfter] using hlookup)
                    hpred_compat₀ hpred_compat₁ hmem₀_eq hmem₁_eq rfl rfl
                    hric₀1 hric₁1 hcwr₀1 hcwr₁1 hAgree_out_body hbody_post_for_transport
              rcases hOutChoice_body_from_helper with
                ⟨θ₀_out, θ₁_out, hθext_body_out₀, hθext_body_out₁, hOutPack_body_out⟩
              rcases hOutPack_body_out with
                ⟨hvCore₀, hvCore₁, hricCore₀, hricCore₁, hcwrCore₀, hcwrCore₁,
                  hagreeCore, hvalCore₀, hvalCore₁, hresAgreeCore⟩
              exact ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut,
                hpredlawsOut,
                IsCanonicalExtension.respectsResult hcanonOut, θ₀_out, θ₁_out,
                wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 hθext_body_out₀),
                wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 hθext_body_out₁),
                hvCore₀, hvCore₁, IsCanonicalExtension.wfCtx hcanonOut,
                hwfFinal, htagBoundedFinal, hwfcfFinal₀, hwfcfFinal₁, hricCore₀,
                hricCore₁, htagFinal, hcwrCore₀, hcwrCore₁, hagreeCore,
                hvalCore₀, hvalCore₁, hresAgreeCore⟩
            · -- dirty-internal fallback branch (¬ internalPoisonClean).
              have hptrue : p = true := by
                have : ¬ p = false := by
                  simpa [hetyp1, internalPoisonClean, getInternalPoison] using hdirty
                cases p <;> simp at this
                rfl
              have h_p1p : joinPoison p1 p = true := by
                simp [hptrue, joinPoison]
              rcases hOutPack_p1p_true h_p1p with
                ⟨tmOut, hcanonOut, hpredlawsOut, hresTmOut, hrest⟩
              exact
                ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut,
                  hpredlawsOut, hresTmOut, hrest⟩
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
            rcases hOutPack_p1p_true h_p1p with
              ⟨tmOut, hcanonOut, hpredlawsOut, hresTmOut, hrest⟩
            exact
              ⟨tmOut, BoundaryTagMeaningPost.of_isCanonical_predSat hcanonOut hpredlawsOut,
                hpredlawsOut, hresTmOut, hrest⟩

    have hfull₀ := terminatesTo_app_inv_full e1 e2 cinit₀ cf₀ o₀ ht₀
    have hfull₁ := terminatesTo_app_inv_full e1 e2 cinit₁ cf₁ o₁ ht₁
    cases hfull₀ with
    | @userFn c₂'₀ v₂₀ c₁₀ x₀ body₀ env₀ _evalCfg₀ ht₀_e2 ht₀_e1 _hNot₀ _hpm1₀
        _ht₀_body _heq_cfg₀ _hpm_e2₀ _hpm_final₀ =>
        have finish_with_side1 :
            ∀ {c₂'₁ c₁₁ : Config} {v₂₁ o₁' : Value},
              terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
              terminatesTo e1 c₂'₁ c₁₁ o₁' →
              StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
                θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
          intro c₂'₁ c₁₁ v₂₁ o₁' ht₁_e2 ht₁_e1
          obtain ⟨θ₀1, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          exact False.elim (closureImpossible_under_parrow hv₀_typed)
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externFn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @userPfn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _htoP₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externPfn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁ _impl₁
            _vRaw₁ ht₁_e2 ht₁_e1 _hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
    | @externFn c₂'₀ v₂₀ c₁₀ x₀ y₀ id₀ argTyp₀ retSpec₀ eff₀ env₀ _impl₀ _vRaw₀
        _mem'₀ _addr'₀ ht₀_e2 ht₀_e1 _hpure₀ _hGet₀ _hArg₀ _hImpl₀ _hValRet₀
        _hcfg₀ _hpm_e2₀ _hpm_final₀ =>
        have finish_with_side1 :
            ∀ {c₂'₁ c₁₁ : Config} {v₂₁ o₁' : Value},
              terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
              terminatesTo e1 c₂'₁ c₁₁ o₁' →
              StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
                θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
          intro c₂'₁ c₁₁ v₂₁ o₁' ht₁_e2 ht₁_e1
          obtain ⟨θ₀1, _, hv₀_typed, _⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
          exact False.elim (closureImpossible_under_parrow hv₀_typed)
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externFn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @userPfn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _htoP₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externPfn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁ _impl₁
            _vRaw₁ ht₁_e2 ht₁_e1 _hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
    | @userPfn c₂'₀ v₂₀ c₁₀ x₀ body₀ env₀ evalCfg₀ ht₀_e2 ht₀_e1 _hNot₀ htoP₀
        ht₀_body heq_cfg₀ hpm_e2₀ hpm_final₀ =>
        have hshape₀ : AppUserOnlyShape e1 e2 cinit₀ cf₀ o₀ := by
          right
          refine ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1,
            htoP₀, ?_, heq_cfg₀, hpm_e2₀, hpm_final₀⟩
          simpa using ht₀_body
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, θ₁1, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (closureImpossible_under_parrow hv₁_typed)
        | @externFn c₂'₁ v₂₁ c₁₁ x₁ y₁ id₁ argTyp₁ retSpec₁ eff₁ env₁ _impl₁ _vRaw₁
            _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁ _hImpl₁ _hValRet₁
            _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, θ₁1, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (closureImpossible_under_parrow hv₁_typed)
        | @userPfn c₂'₁ v₂₁ c₁₁ x₁ body₁ env₁ evalCfg₁ ht₁_e2 ht₁_e1 _hNot₁ htoP₁
            ht₁_body heq_cfg₁ hpm_e2₁ hpm_final₁ =>
            have hshape₁ : AppUserOnlyShape e1 e2 cinit₁ cf₁ o₁ := by
              right
              refine ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1,
                htoP₁, ?_, heq_cfg₁, hpm_e2₁, hpm_final₁⟩
              simpa using ht₁_body
            exact finish_user_only hshape₀ hshape₁
        | @externPfn c₂'₁ _v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁
            _impl₁ _vRaw₁ ht₁_e2 ht₁_e1 hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact False.elim (by
              have hreg_c₂'₁ : c₂'₁.registry = emptyExternRegistry := by
                simpa [cinit₁] using terminatesTo_preserves_registry ht₁_e2
              have hreg_c₁₁ : c₁₁.registry = emptyExternRegistry :=
                (terminatesTo_preserves_registry ht₁_e1).trans hreg_c₂'₁
              rw [hreg_c₁₁] at hGet₁
              simp [emptyExternRegistry] at hGet₁)
    | @externPfn c₂'₀ v₂₀ c₁₀ x₀ y₀ id₀ argTyp₀ retSpec₀ env₀ impl₀ vRaw₀
        ht₀_e2 ht₀_e1 hGet₀ hArg₀ hImpl₀ hValRet₀ hcfg₀ _hpm_e2₀ _hpm_final₀ =>
        have finish_with_side1 :
            ∀ {c₂'₁ c₁₁ : Config} {v₂₁ o₁' : Value},
              terminatesTo e2 cinit₁ c₂'₁ v₂₁ →
              terminatesTo e1 c₂'₁ c₁₁ o₁' →
              StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm
                θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
          intro c₂'₁ c₁₁ v₂₁ o₁' ht₁_e2 ht₁_e1
          exact False.elim (by
            have hreg_c₂'₀ : c₂'₀.registry = emptyExternRegistry := by
              simpa [cinit₀] using terminatesTo_preserves_registry ht₀_e2
            have hreg_c₁₀ : c₁₀.registry = emptyExternRegistry :=
              (terminatesTo_preserves_registry ht₀_e1).trans hreg_c₂'₀
            rw [hreg_c₁₀] at hGet₀
            simp [emptyExternRegistry] at hGet₀)
        cases hfull₁ with
        | @userFn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _hpm1₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (closureImpossible_under_parrow hv₁_typed)
        | @externFn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _eff₁ _env₁
            _impl₁ _vRaw₁ _mem'₁ _addr'₁ ht₁_e2 ht₁_e1 _hpure₁ _hGet₁ _hArg₁
            _hImpl₁ _hValRet₁ _hcfg₁ _hpm_e2₁ _hpm_final₁ =>
            obtain ⟨_, _, _, hv₁_typed⟩ := mkValueHasETyp_pair ht₀_e2 ht₁_e2 ht₀_e1 ht₁_e1
            exact False.elim (closureImpossible_under_parrow hv₁_typed)
        | @userPfn c₂'₁ v₂₁ c₁₁ _x₁ _body₁ _env₁ _evalCfg₁ ht₁_e2 ht₁_e1
            _hNot₁ _htoP₁ _ht₁_body _heq_cfg₁ _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
        | @externPfn c₂'₁ v₂₁ c₁₁ _x₁ _y₁ _id₁ _argTyp₁ _retSpec₁ _env₁ _impl₁
            _vRaw₁ ht₁_e2 ht₁_e1 _hGet₁ _hArg₁ _hImpl₁ _hValRet₁ _hcfg₁
            _hpm_e2₁ _hpm_final₁ =>
            exact finish_with_side1 ht₁_e2 ht₁_e1
