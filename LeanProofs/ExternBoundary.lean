/-
  ExternBoundary.lean - Theorem-facing FR boundary contract layer.

  Runtime extern event predicates (`ExternDeclBoundaryRun`,
  `ExternCallBoundaryRun`, `ExternBoundaryWFRun`) and the operational safety
  contract (`ExternOperationalSafe`) live in `LeanProofs/ExternRuntime.lean`,
  below the FR proof stack so `SemanticsProperties.lean` can consume them.

  This file carries the FR-shaped fields (`StepFRPost`-producing) and the
  trusted-registry interface consumed by the top-level fault-robustness
  theorem.
-/
import LeanProofs.StepFR
import LeanProofs.ExternRuntime

open Std

/-- Agreement and well-formedness facts at two call-body entries. -/
structure BodyEntryInputsAgree
    (predSat : PredSat) (ctx : TypeContext)
    (entry₀ entry₁ : ExternCallEntry)
    (θ₀ θ₁ : RealizationMap) : Prop where
  wfRealization₀ : wfRealizationMap θ₀
  wfRealization₁ : wfRealizationMap θ₁
  wfCtx : wfTypeContext ctx
  tagBounded : TagBoundedCtx ctx
  runtime₀ :
    runtimeInstantiatesCtx ctx entry₀.bodyConfig.memory entry₀.bodyConfig.varEnv θ₀
  runtime₁ :
    runtimeInstantiatesCtx ctx entry₁.bodyConfig.memory entry₁.bodyConfig.varEnv θ₁
  regime : regimeConsistentWithCtx ctx
  consistent₀ :
    consistentWithRegime predSat ctx.regime ctx
      entry₀.bodyConfig.memory entry₀.bodyConfig.varEnv θ₀
  consistent₁ :
    consistentWithRegime predSat ctx.regime ctx
      entry₁.bodyConfig.memory entry₁.bodyConfig.varEnv θ₁
  agree :
    agreeOnClean predSat ctx.regime ctx
      entry₀.bodyConfig.memory entry₀.bodyConfig.varEnv θ₀
      entry₁.bodyConfig.memory entry₁.bodyConfig.varEnv θ₁
  wfConfig₀ : wfConfig entry₀.bodyConfig
  wfConfig₁ : wfConfig entry₁.bodyConfig

namespace ExternBoundaryTyping

/-- Declaration-boundary typing origin: the result is the one produced by
    typechecking the same extern declaration expression represented by `d`. -/
inductive Decl : ExternDeclaration → Expr → TypeContext → TypeResult → Prop where
  | val {ctx : TypeContext} {fuel : Nat} {id : ExternId}
      {typ : Typ} {poison : Poison} {pred : SyntaxPredicate} {res : TypeResult} :
      typecheck ctx (Expr.externVal id typ poison pred) fuel = .ok res →
      Decl
        { id := id, kind := .val, typ := typ, argName := none, retSpec := none,
          effects := [], preds := [pred], argPoison := false }
        (Expr.externVal id typ poison pred) ctx res
  | fn {ctx : TypeContext} {fuel : Nat} {id : ExternId} {x : Name}
      {argTyp : Typ} {argPoison : Bool} {argPred : SyntaxPredicate}
      {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
      {res : TypeResult} :
      typecheck ctx (Expr.externFn id x argTyp argPoison argPred retSpec effects captures) fuel = .ok res →
      Decl
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := captures }
        (Expr.externFn id x argTyp argPoison argPred retSpec effects captures) ctx res
  | pfn {ctx : TypeContext} {fuel : Nat} {id : ExternId} {x : Name}
      {argTyp : Typ} {argPoison : Bool} {argPred : SyntaxPredicate}
      {retSpec : ExternReturn} {captures : List Capture} {res : TypeResult} :
      typecheck ctx (Expr.externPfn id x argTyp argPoison argPred retSpec captures) fuel = .ok res →
      Decl
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [], preds := collectExternPreds retSpec [],
          argPoison := argPoison, captures := captures }
        (Expr.externPfn id x argTyp argPoison argPred retSpec captures) ctx res

/-- Call-boundary typing origin: the selected extern call result is the result
    of applying the closure member that corresponds to the same boundary
    declaration and runtime call entry. -/
inductive Call : ExternDeclaration → Expr → ExternCallEntry → TypeResult → Prop where
  | fnExternMember
      {d : ExternDeclaration}
      {ctx : TypeContext} {bodyState : TypeResult} {cursor : Tag × Loc} {fuel : Nat}
      {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison}
      {argPred : Predicate} {id : ExternId} {x y : Name} {argTyp : Typ}
      {argPoisonAst : Bool} {argPredAst : SyntaxPredicate} {declaredArgQt : QTyp}
      {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
      {tenv : CapturedVarEnv}
      {entry : ExternCallEntry} {res : TypeResult} :
      d.id = id →
      d.kind = .fn →
      d.typ = argTyp →
      d.argName = some x →
      d.retSpec = some retSpec →
      d.effects = effects →
      -- The trusted contract: the decl's captures equal the applied closure's
      -- type-member captures (`captures`), driving `capturesSatisfied` (mirrors pfn).
      d.captures = captures →
      declaredArgQt.poison = d.argPoison →
      entry.bodyCtx =
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := bodyState.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := bodyState.tagEnv'
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := bodyState.regime' } →
      applyFnTClosureAtCursor (FnTClosure.extern id x retSpec effects tenv declaredArgQt captures)
        st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor fuel = .ok res →
      Call
        d
        (Expr.externFn id y argTyp argPoisonAst argPredAst retSpec effects captures) entry res
  | fnRegularExternBody
      {d : ExternDeclaration}
      {bodyCtx : TypeContext} {result3 : TypeResult} {fuel : Nat}
      {p p1 : Poison} {id : ExternId} {x y : Name} {argTyp : Typ}
      {argPoisonAst : Bool} {argPredAst : SyntaxPredicate}
      {retSpec : ExternReturn} {effects : List Effect}
      {entry : ExternCallEntry} {res : TypeResult} :
      d.id = id →
      d.kind = .fn →
      d.typ = argTyp →
      d.argName = some x →
      d.retSpec = some retSpec →
      d.effects = effects →
      entry.bodyCtx = bodyCtx →
      typecheck bodyCtx (Expr.externFn id y argTyp argPoisonAst argPredAst retSpec effects captures) fuel = .ok result3 →
      res =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } →
      Call
        d
        (Expr.externFn id y argTyp argPoisonAst argPredAst retSpec effects captures) entry res
  | pfnExternMember
      {d : ExternDeclaration}
      {ctx : TypeContext} {bodyState : TypeResult} {cursor : Tag × Loc} {fuel : Nat}
      {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison}
      {argPred : Predicate} {id : ExternId} {x y : Name} {argTyp : Typ}
      {argPoisonAst : Bool} {argPredAst : SyntaxPredicate} {declaredArgQt : QTyp}
      {retSpec : ExternReturn} {captures bodyCaptures : List Capture}
      {tenv : CapturedVarEnv}
      {entry : ExternCallEntry} {res : TypeResult} :
      d.id = id →
      d.kind = .pfn →
      d.typ = argTyp →
      d.argName = some x →
      d.retSpec = some retSpec →
      -- The trusted contract: the decl's captures equal the applied closure's
      -- type-member captures (`captures`).  These drive `capturesSatisfied`.
      d.captures = captures →
      declaredArgQt.poison = d.argPoison →
      entry.bodyCtx =
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := bodyState.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := bodyState.tagEnv'
          pureCtx := true
          nextTag := cursor.1
          nextLoc := cursor.2
          regime := bodyState.regime' } →
      applyPFnTClosureAtCursor (PFnTClosure.extern id x retSpec tenv declaredArgQt captures)
        st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor fuel = .ok res →
      -- `bodyCaptures` records only the runtime closure body AST shape; it is
      -- DECOUPLED from the trusted/member `captures` (two-track discipline).
      Call
        d
        (Expr.externPfn id y argTyp argPoisonAst argPredAst retSpec bodyCaptures) entry res

end ExternBoundaryTyping

/-- Paired extern-declaration boundary runs produce the same post as `StepFR`.

    `postExpr` is explicit because the current `StepFRPost` remains indexed by
    the expression whose typechecking produced the result. -/
def ExternDeclBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (postExpr : Expr) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning),
    ExternBoundaryTyping.Decl d postExpr ctx res →
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv)
      (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      wfRealizationMap θ₀ →
      wfRealizationMap θ₁ →
      wfTypeContext ctx →
      TagBoundedCtx ctx →
      runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
      runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
      regimeConsistentWithCtx ctx →
      consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →
      consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
      agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
      ∀ (a₀ a₁ : Address) (pm : Bool) (registry : ExternRegistry),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
                   registry := registry } →
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
                   registry := registry } →
        ExternDeclBoundaryRunForExpr postExpr d impl ctx res
          { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
            registry := registry } cf₀ o₀ →
        ExternDeclBoundaryRunForExpr postExpr d impl ctx res
          { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
            registry := registry } cf₁ o₁ →
        StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

/-- Paired extern-call boundary runs produce the same post as the surrounding
    expression step. -/
def ExternCallBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (postExpr typedExpr₀ typedExpr₁ : Expr)
    (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (entry₀ entry₁ : ExternCallEntry),
    let ctx := entry₀.bodyCtx
    entry₁.bodyCtx = ctx →
    ExternBoundaryTyping.Call d typedExpr₀ entry₀ res →
    ExternBoundaryTyping.Call d typedExpr₁ entry₁ res →
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    ∀ (θ₀ θ₁ : RealizationMap),
      BodyEntryInputsAgree predSat ctx entry₀ entry₁ θ₀ θ₁ →
      ∀ (cf₀ cf₁ : Config) (o₀ o₁ : Value),
        ExternCallBoundaryRun d impl entry₀ res cf₀ o₀ →
        ExternCallBoundaryRun d impl entry₁ res cf₁ o₁ →
        StepFRPost ctx postExpr res predSat tm θ₀ θ₁
          (entry₀.bodyOutputConfig cf₀) (entry₁.bodyOutputConfig cf₁) o₀ o₁

def ExternBoundarySinglePost
    (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning)
    (θ : RealizationMap)
    (μ : Memory) (cf : Config) (o : Value) : Prop :=
  ∃ tm',
  BoundaryTagMeaningPost ctx res predSat tm tm' ∧
  ∃ θ',
    wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime
      (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime
      res.qualType cf.memory θ' o ∧
    PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' ∧
    FreshCleanLocsUnrealizedOneRun ctx res θ'

namespace ExternBoundarySinglePost

theorem to_maskedRegParamPost
    {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {θ : RealizationMap} {μ : Memory} {ρ : VarEnv}
    {cf : Config} {o : Value} {registry : ExternRegistry}
    (hθwf : wfRealizationMap θ)
    (hwf : wfTypeContext ctx)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hreg : regimeConsistentWithCtxMasked masked ctx)
    (hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none)
    (hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx)
    (hmasked_bounded : ∀ k, masked k → k < ctx.nextTag)
    (hbnd : TagBoundedCtx ctx)
    (hctxCons :
      consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
    (a : Address) (pm : Bool)
    (hwfcfg :
      wfConfig ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } : Config))
    (h : ExternBoundarySinglePost ctx res predSat tm θ μ cf o) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctx res (registry := registry) μ ρ θ cf o
      hθwf hwf hric hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg := by
  rcases h with ⟨_tm', _htag, θ', hθext, hvtyp, hric', hcwr', hvalc', hpres, hfresh⟩
  exact
    ⟨θ', hθext, hvtyp, hric', consistentWithRegime_to_masked hcwr',
      valueConsistentWithRegime_to_masked hvalc', hpres, hfresh⟩

end ExternBoundarySinglePost

def ExternDeclBoundarySingle
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (postExpr : Expr) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning),
    ExternBoundaryTyping.Decl d postExpr ctx res →
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (cf : Config) (o : Value),
      wfRealizationMap θ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx μ ρ θ →
      regimeConsistentWithCtx ctx →
      consistentWithRegime predSat ctx.regime ctx μ ρ θ →
      ∀ (a : Address) (pm : Bool) (registry : ExternRegistry),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                   registry := registry } →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
            registry := registry } cf o →
        ctx.pc = true →
        ExternBoundarySinglePost ctx res predSat tm θ μ cf o

def ExternCallBoundarySingle
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (typedExpr : Expr) (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (entry : ExternCallEntry),
    let ctx := entry.bodyCtx
    ExternBoundaryTyping.Call d typedExpr entry res →
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    TagMeaningBounded tm ctx.nextTag →
    ∀ (θ : RealizationMap) (cf : Config) (o : Value),
      wfRealizationMap θ →
      wfTypeContext ctx →
      runtimeInstantiatesCtx ctx entry.bodyConfig.memory entry.bodyConfig.varEnv θ →
      regimeConsistentWithCtx ctx →
      consistentWithRegime predSat ctx.regime ctx
        entry.bodyConfig.memory entry.bodyConfig.varEnv θ →
      wfConfig entry.bodyConfig →
      ExternCallBoundaryRun d impl entry res cf o →
      ctx.pc = true →
      ExternBoundarySinglePost ctx res predSat tm θ entry.bodyConfig.memory
        (entry.bodyOutputConfig cf) o

structure ExternBoundarySpec
    (d : ExternDeclaration) (impl : ExternImpl) : Prop where
  declFR : ExternDeclBoundaryFR d impl
  callFR : ExternCallBoundaryFR d impl
  declSingle : ExternDeclBoundarySingle d impl
  callSingle : ExternCallBoundarySingle d impl
  operational : ExternOperationalSafe d impl

/-- Registry-parametric masked single-run declaration-boundary adapter used by
    the step proof. -/
def ExternDeclBoundarySingleMaskedContract
    (masked : Tag → Prop) (postExpr : Expr) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning) (registry : ExternRegistry)
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  PredSatLaws predSat tm →
  ExternTypingAssumptions →
  wfTagMeaningCtx tm ctx →
  TagMeaningBounded tm ctx.nextTag →
  ExternBoundaryTyping.Decl d postExpr ctx res →
  ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value),
    (hθwf : wfRealizationMap θ) →
    (hwf : wfTypeContext ctx) →
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) →
    (hreg : regimeConsistentWithCtxMasked masked ctx) →
    (hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none) →
    (hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx) →
    (hmasked_bounded : ∀ k, masked k → k < ctx.nextTag) →
    (hbnd : TagBoundedCtx ctx) →
    (hctxCons : consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ) →
    ∀ (a : Address) (pm : Bool),
      (hwfcfg :
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                   registry := registry}) →
      ExternDeclBoundaryRun d impl ctx res
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
          registry := registry } cf o →
      ctx.pc = true →
      StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
        masked
        (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
        (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
        ctx res (registry := registry) μ ρ θ cf o
        hθwf hwf hric hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg

theorem ExternDeclBoundarySingleMaskedContract.of_spec
    {masked : Tag → Prop} {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning} {registry : ExternRegistry}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hspec : ExternBoundarySpec d impl) :
    ExternDeclBoundarySingleMaskedContract masked postExpr ctx res predSat tm registry
      d impl := by
  intro hpredlaws _hExtTyping hwfTm hTmBounded htyped μ ρ θ cf o hθwf hwf hric
    hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg hrun hpc
  have hregOrd : regimeConsistentWithCtx ctx :=
    regimeConsistentWithCtxMasked_unmask hreg hmasked_absent
  have hctxConsOrd :
      consistentWithRegime predSat ctx.regime ctx μ ρ θ :=
    consistentWithRegimeMasked_unmask hmasked_none hctxCons
  have hsingle :
      ExternBoundarySinglePost ctx res predSat tm θ μ cf o :=
    hspec.declSingle postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
      μ ρ θ cf o hθwf hwf hric hregOrd hctxConsOrd a pm registry hwfcfg hrun hpc
  exact
    ExternBoundarySinglePost.to_maskedRegParamPost
      (masked := masked) (ctx := ctx) (res := res) (predSat := predSat)
      (tm := tm) (θ := θ) (μ := μ) (ρ := ρ) (cf := cf) (o := o)
      (registry := registry)
      hθwf hwf hric hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg hsingle

/-- Registry-parametric two-run declaration-boundary adapter used by the step
    proof. -/
def ExternDeclBoundaryFRContract
    (ctx : TypeContext) (postExpr : Expr) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning) (registry : ExternRegistry)
    (d : ExternDeclaration) (impl₀ impl₁ : ExternImpl) : Prop :=
  PredSatLaws predSat tm →
  ExternTypingAssumptions →
  wfTagMeaningCtx tm ctx →
  TagMeaningBounded tm ctx.nextTag →
  ExternBoundaryTyping.Decl d postExpr ctx res →
  ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value),
    wfRealizationMap θ₀ →
    wfRealizationMap θ₁ →
    wfTypeContext ctx →
    TagBoundedCtx ctx →
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
    regimeConsistentWithCtx ctx →
    consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →
    consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
    agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ →
    ∀ (a₀ a₁ : Address) (pm : Bool),
      wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
                 registry := registry } →
      wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
                 registry := registry } →
      ExternDeclBoundaryRunForExpr postExpr d impl₀ ctx res
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
          registry := registry } cf₀ o₀ →
      ExternDeclBoundaryRunForExpr postExpr d impl₁ ctx res
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
          registry := registry } cf₁ o₁ →
      StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

theorem ExternDeclBoundaryFRContract.of_spec
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning} {registry : ExternRegistry}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hspec : ExternBoundarySpec d impl) :
    ExternDeclBoundaryFRContract ctx postExpr res predSat tm registry
      d impl impl := by
  intro hpredlaws _hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  exact
    hspec.declFR postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
      μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded
      hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm
      registry hwfcfg₀ hwfcfg₁ hrun₀ hrun₁

structure TrustedExternEntry where
  decl : ExternDeclaration
  impl : ExternImpl
  spec : ExternBoundarySpec decl impl

/-- Proof-side trusted registry.  The runtime registry is projected by folding
    these proof-carrying entries into the flat executable registry. -/
abbrev TrustedRegistry := List TrustedExternEntry

namespace TrustedRegistry

def lookup? : TrustedRegistry → ExternId → Option TrustedExternEntry
  | [], _ => none
  | entry :: rest, id =>
      if entry.decl.id == id then some entry else lookup? rest id

def toRuntimeRegistry (tr : TrustedRegistry) : ExternRegistry :=
  tr.foldr (fun entry reg => reg.insert entry.decl.id entry.impl) emptyExternRegistry

theorem lookup_toRuntimeRegistry
    {tr : TrustedRegistry} {id : ExternId} {entry : TrustedExternEntry}
    (hlookup : TrustedRegistry.lookup? tr id = some entry) :
    (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl := by
  induction tr with
  | nil =>
      simp [TrustedRegistry.lookup?] at hlookup
  | cons head rest ih =>
      unfold TrustedRegistry.lookup? at hlookup
      unfold TrustedRegistry.toRuntimeRegistry
      by_cases hhead : head.decl.id == id
      · simp [hhead] at hlookup
        cases hlookup
        have hid : entry.decl.id = id := LawfulBEq.eq_of_beq hhead
        rw [← hid]
        exact
          Std.HashMap.getElem?_insert_self
            (m := TrustedRegistry.toRuntimeRegistry rest)
            (k := entry.decl.id) (v := entry.impl)
      · simp [hhead] at hlookup
        change ((TrustedRegistry.toRuntimeRegistry rest).insert head.decl.id head.impl)[id]? =
          some entry.impl
        rw [Std.HashMap.getElem?_insert]
        simp [hhead]
        exact ih hlookup

theorem runtime_lookup_exists
    {tr : TrustedRegistry} {id : ExternId} {impl : ExternImpl}
    (hlookup : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry, TrustedRegistry.lookup? tr id = some entry ∧ entry.impl = impl := by
  induction tr with
  | nil =>
      simp [TrustedRegistry.toRuntimeRegistry, emptyExternRegistry] at hlookup
  | cons head rest ih =>
      unfold TrustedRegistry.toRuntimeRegistry at hlookup
      change ((TrustedRegistry.toRuntimeRegistry rest).insert head.decl.id head.impl)[id]? =
        some impl at hlookup
      rw [Std.HashMap.getElem?_insert] at hlookup
      by_cases hhead : head.decl.id == id
      · simp [hhead] at hlookup
        refine ⟨head, ?_, hlookup⟩
        unfold TrustedRegistry.lookup?
        simp [hhead]
      · simp [hhead] at hlookup
        rcases ih hlookup with ⟨entry, hlookupEntry, himpl⟩
        refine ⟨entry, ?_, himpl⟩
        unfold TrustedRegistry.lookup?
        simp [hhead, hlookupEntry]

/-- Bridge: a trusted registry's runtime projection satisfies the
    operational safety contract consumed by `SemanticsProperties.lean`.
    Each clause unpacks `entry.spec.operational` via the per-kind shape of
    `ExternOperationalSafe` after looking up the entry through
    `runtime_lookup_exists`. -/
theorem operationalSafe (tr : TrustedRegistry) :
    RegistryOperationalSafe (TrustedRegistry.toRuntimeRegistry tr) := by
  refine ⟨?fnMono, ?fnWf, ?pfn, ?val⟩
  case fnMono =>
    intro id implFn hlookup env vArg mem addr vRaw mem' addr' himpl
    rcases runtime_lookup_exists hlookup with ⟨entry, _, himplEq⟩
    have hop :=
      entry.spec.operational.1 implFn himplEq
        env vArg mem addr vRaw mem' addr' himpl
    exact hop.1
  case fnWf =>
    intro id implFn hlookup env vArg mem addr vRaw mem' addr' himpl
      hmem hwfenv hwfarg
    rcases runtime_lookup_exists hlookup with ⟨entry, _, himplEq⟩
    have hop :=
      entry.spec.operational.1 implFn himplEq
        env vArg mem addr vRaw mem' addr' himpl
    exact hop.2 hmem hwfenv hwfarg
  case pfn =>
    intro id implPfn hlookup env vArg mem addr vRaw himpl
      hmem hwfenv hwfarg
    rcases runtime_lookup_exists hlookup with ⟨entry, _, himplEq⟩
    exact entry.spec.operational.2.1 implPfn himplEq
      env vArg mem addr vRaw himpl hmem hwfenv hwfarg
  case val =>
    intro cfg hwfcfg _hreg id v hlookup
    rcases runtime_lookup_exists hlookup with ⟨entry, _, himplEq⟩
    exact entry.spec.operational.2.2 v himplEq cfg hwfcfg

end TrustedRegistry

/-- `d` is an extern declaration synthetically exposed by an extern return
    descriptor.  This is what makes nested returned callables visible to the
    trusted-registry agreement layer. -/
inductive ExternDeclarationInReturn : ExternReturn → ExternId → ExternDeclaration → Prop where
  | nestedFn_here {innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects} :
      ExternDeclarationInReturn
        (ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures)
        innerId
        { id := innerId, kind := .fn, typ := innerArgTyp, argName := some innerArg,
          retSpec := some innerRet, effects := innerEffects,
          preds := collectExternPreds innerRet innerEffects, argPoison := innerArgPoison,
          captures := innerCaptures }
  | nestedFn_inner {innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects id d} :
      ExternDeclarationInReturn innerRet id d →
      ExternDeclarationInReturn
        (ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures) id d
  | nestedPfn_here {innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet} :
      ExternDeclarationInReturn
        (ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures)
        innerId
        { id := innerId, kind := .pfn, typ := innerArgTyp, argName := some innerArg,
          retSpec := some innerRet, effects := [], preds := collectExternPreds innerRet [],
          argPoison := innerArgPoison, captures := innerCaptures }
  | nestedPfn_inner {innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet id d} :
      ExternDeclarationInReturn innerRet id d →
      ExternDeclarationInReturn
        (ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures) id d

/-- `d` is an extern declaration syntactically present in `e`. -/
inductive ExternDeclarationInProgram : Expr → ExternId → ExternDeclaration → Prop where
  | externVal {id typ poison pred} :
      ExternDeclarationInProgram (Expr.externVal id typ poison pred) id
        { id := id, kind := .val, typ := typ, argName := none, retSpec := none,
          effects := [], preds := [pred], argPoison := false }
  | externFn {id x argTyp argPoison argPred retSpec eff} :
      ExternDeclarationInProgram (Expr.externFn id x argTyp argPoison argPred retSpec eff cap) id
        { id := id, kind := .fn, typ := argTyp, argName := some x, retSpec := some retSpec,
          effects := eff, preds := collectExternPreds retSpec eff, argPoison := argPoison,
          captures := cap }
  | externFn_return {id x argTyp argPoison argPred retSpec eff nestedId d} :
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationInProgram (Expr.externFn id x argTyp argPoison argPred retSpec eff cap) nestedId d
  | externPfn {id x argTyp argPoison argPred retSpec} :
      ExternDeclarationInProgram (Expr.externPfn id x argTyp argPoison argPred retSpec cap) id
        { id := id, kind := .pfn, typ := argTyp, argName := some x, retSpec := some retSpec,
          effects := [], preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := cap }
  | externPfn_return {id x argTyp argPoison argPred retSpec nestedId d} :
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationInProgram (Expr.externPfn id x argTyp argPoison argPred retSpec cap) nestedId d
  | op_left {e1 e2 op id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.op e1 op e2) id d
  | op_right {e1 e2 op id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.op e1 op e2) id d
  | unaryop {e op id d} :
      ExternDeclarationInProgram e id d →
      ExternDeclarationInProgram (Expr.unaryop op e) id d
  | ite_cond {e1 e2 e3 id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.ite e1 e2 e3) id d
  | ite_then {e1 e2 e3 id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.ite e1 e2 e3) id d
  | ite_else {e1 e2 e3 id d} :
      ExternDeclarationInProgram e3 id d →
      ExternDeclarationInProgram (Expr.ite e1 e2 e3) id d
  | newRef {e id d} :
      ExternDeclarationInProgram e id d →
      ExternDeclarationInProgram (Expr.newRef e) id d
  | assign_left {e1 e2 id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.assign e1 e2) id d
  | assign_right {e1 e2 id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.assign e1 e2) id d
  | deref {e id d} :
      ExternDeclarationInProgram e id d →
      ExternDeclarationInProgram (Expr.deref e) id d
  | seq_left {e1 e2 id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.seq e1 e2) id d
  | seq_right {e1 e2 id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.seq e1 e2) id d
  | vlet_bound {x e1 e2 id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.vlet x e1 e2) id d
  | vlet_body {x e1 e2 id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.vlet x e1 e2) id d
  | fn_body {x argTyp body retTyp id d} :
      ExternDeclarationInProgram body id d →
      ExternDeclarationInProgram (Expr.fn x argTyp body retTyp) id d
  | fn_extern_body_runtime {x argTyp retTyp id y bodyArgTyp bodyArgPoison bodyArgPred retSpec effects} :
      ExternDeclarationInProgram
        (Expr.fn x argTyp (Expr.externFn id y bodyArgTyp bodyArgPoison bodyArgPred retSpec effects cap) retTyp) id
        { id := id, kind := .fn, typ := bodyArgTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := bodyArgPoison,
          captures := cap }
  | pfn_body {x argTyp body retTyp id d} :
      ExternDeclarationInProgram body id d →
      ExternDeclarationInProgram (Expr.pfn x argTyp body retTyp) id d
  | app_fun {e1 e2 id d} :
      ExternDeclarationInProgram e1 id d →
      ExternDeclarationInProgram (Expr.app e1 e2) id d
  | app_arg {e1 e2 id d} :
      ExternDeclarationInProgram e2 id d →
      ExternDeclarationInProgram (Expr.app e1 e2) id d

namespace ExternDeclarationInReturn

private theorem id_eq
    {retSpec : ExternReturn} {id : ExternId} {d : ExternDeclaration}
    (h : ExternDeclarationInReturn retSpec id d) :
    d.id = id := by
  induction h with
  | nestedFn_here => rfl
  | nestedFn_inner _ ih => exact ih
  | nestedPfn_here => rfl
  | nestedPfn_inner _ ih => exact ih

end ExternDeclarationInReturn

namespace ExternDeclarationInProgram

theorem id_eq
    {e : Expr} {id : ExternId} {d : ExternDeclaration}
    (h : ExternDeclarationInProgram e id d) :
    d.id = id := by
  induction h with
  | externVal => rfl
  | externFn => rfl
  | externFn_return hret => exact ExternDeclarationInReturn.id_eq hret
  | externPfn => rfl
  | externPfn_return hret => exact ExternDeclarationInReturn.id_eq hret
  | op_left _ ih => exact ih
  | op_right _ ih => exact ih
  | unaryop _ ih => exact ih
  | ite_cond _ ih => exact ih
  | ite_then _ ih => exact ih
  | ite_else _ ih => exact ih
  | newRef _ ih => exact ih
  | assign_left _ ih => exact ih
  | assign_right _ ih => exact ih
  | deref _ ih => exact ih
  | seq_left _ ih => exact ih
  | seq_right _ ih => exact ih
  | vlet_bound _ ih => exact ih
  | vlet_body _ ih => exact ih
  | fn_body _ ih => exact ih
  | fn_extern_body_runtime => rfl
  | pfn_body _ ih => exact ih
  | app_fun _ ih => exact ih
  | app_arg _ ih => exact ih

end ExternDeclarationInProgram

/-- Trusted entries may only implement declarations with the same id and
    declaration shape as the program. -/
def TrustedRegistryAgreesWithProgram (e : Expr) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationInProgram e id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d

def TrustedRegistryEntryMatchesFn
    (entry : TrustedExternEntry) (id : ExternId) (x : Name)
    (argTyp : Typ) (retSpec : ExternReturn) (effects : List Effect)
    (captures : List Capture) : Prop :=
  entry.decl.id = id ∧
  entry.decl.kind = .fn ∧
  entry.decl.typ = argTyp ∧
  entry.decl.argName = some x ∧
  entry.decl.retSpec = some retSpec ∧
  entry.decl.effects = effects ∧
  entry.decl.captures = captures

def TrustedRegistryEntryMatchesPfn
    (entry : TrustedExternEntry) (id : ExternId) (x : Name)
    (argTyp : Typ) (retSpec : ExternReturn) (captures : List Capture) : Prop :=
  entry.decl.id = id ∧
  entry.decl.kind = .pfn ∧
  entry.decl.typ = argTyp ∧
  entry.decl.argName = some x ∧
  entry.decl.retSpec = some retSpec ∧
  entry.decl.captures = captures

theorem TrustedRegistryAgreesWithProgram.resolveFnDeclaration
    {e : Expr} {tr : TrustedRegistry} {id : ExternId} {x : Name}
    {argTyp : Typ} {argPoison : Bool} {retSpec : ExternReturn} {effects : List Effect}
    {captures : List Capture} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := captures })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hprog hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesFn, hdecl]

theorem TrustedRegistryAgreesWithProgram.resolvePfnDeclaration
    {e : Expr} {tr : TrustedRegistry} {id : ExternId} {x : Name}
    {argTyp : Typ} {argPoison : Bool} {retSpec : ExternReturn} {impl : ExternImpl}
    {memberCap : List Capture}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := memberCap })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hprog hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesPfn, hdecl]

namespace TrustedRegistryEntryMatchesFn

theorem id_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.id = id :=
  h.1

private theorem kind_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.kind = .fn :=
  h.2.1

private theorem typ_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.typ = argTyp :=
  h.2.2.1

private theorem argName_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.argName = some x :=
  h.2.2.2.1

private theorem retSpec_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.retSpec = some retSpec :=
  h.2.2.2.2.1

theorem captures_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures) :
    entry.decl.captures = captures :=
  h.2.2.2.2.2.2

end TrustedRegistryEntryMatchesFn

namespace TrustedRegistryEntryMatchesPfn

theorem id_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.id = id :=
  h.1

private theorem kind_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.kind = .pfn :=
  h.2.1

private theorem typ_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.typ = argTyp :=
  h.2.2.1

private theorem argName_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.argName = some x :=
  h.2.2.2.1

private theorem retSpec_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.retSpec = some retSpec :=
  h.2.2.2.2.1

theorem captures_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {captures : List Capture}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures) :
    entry.decl.captures = captures :=
  h.2.2.2.2.2

end TrustedRegistryEntryMatchesPfn

theorem ExternCallBoundaryRun.fn_of_match
    {entry : TrustedExternEntry} {id : ExternId} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    {implFn : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address)}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value} {mem' : Memory} {addr' : Address}
    (hmatch :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects captures)
    (hpure : callEntry.callConfig.pureMode = false)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hlookup : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl)
    (himpl : entry.impl = ExternImpl.fn implFn)
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw, mem', addr'))
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = { callEntry.callConfig with memory := mem', nextAddr := addr' }) :
    ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  subst cf
  refine ExternCallBoundaryRun.fn ?_
  refine
    { kind_fn := TrustedRegistryEntryMatchesFn.kind_eq hmatch
      argName := TrustedRegistryEntryMatchesFn.argName_eq hmatch
      retSpec := ⟨retSpec, TrustedRegistryEntryMatchesFn.retSpec_eq hmatch⟩
      pureMode_false := hpure
      unifiedEnv_eq := hunified
      lookup := hlookup
      impl_success := ?_
      output_config := ?_ }
  · refine ⟨implFn, retSpec, vRaw, himpl, TrustedRegistryEntryMatchesFn.retSpec_eq hmatch,
      ?_, hImpl, ?_⟩
    · simpa [TrustedRegistryEntryMatchesFn.typ_eq hmatch] using hArg
    · simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hValRet
  · simp

theorem ExternCallBoundaryRun.pfn_of_match
    {entry : TrustedExternEntry} {id : ExternId} {argTyp : Typ}
    {retSpec : ExternReturn}
    {implFn : VarEnv → Value → Memory → Except ExternError Value}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value}
    (hmatch :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec captures)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hlookup : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl)
    (himpl : entry.impl = ExternImpl.pfn implFn)
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw)
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = callEntry.callConfig) :
    ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  subst cf
  refine ExternCallBoundaryRun.pfn ?_
  refine
    { kind_pfn := TrustedRegistryEntryMatchesPfn.kind_eq hmatch
      argName := TrustedRegistryEntryMatchesPfn.argName_eq hmatch
      retSpec := ⟨retSpec, TrustedRegistryEntryMatchesPfn.retSpec_eq hmatch⟩
      unifiedEnv_eq := hunified
      lookup := hlookup
      impl_success := ?_
      output_config := rfl }
  refine ⟨implFn, retSpec, vRaw, himpl, TrustedRegistryEntryMatchesPfn.retSpec_eq hmatch,
    ?_, hImpl, ?_⟩
  · simpa [TrustedRegistryEntryMatchesPfn.typ_eq hmatch] using hArg
  · simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hValRet

def TrustedRegistryAgreesWithFnTClosures
    (tr : TrustedRegistry) (argTyp : Typ) (tcls : List FnTClosure) : Prop :=
  ∀ {id x retSpec effects capturedEnv argQt captures},
    FnTClosure.extern id x retSpec effects capturedEnv argQt captures ∈ tcls →
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures ∧
      -- The trusted entry's declared-argument poison must agree with the closure
      -- member's resolved argument condition.  `TrustedRegistryEntryMatchesFn` is a
      -- deliberately lossy projection of `entry.decl = d` (it drops `argPoison`,
      -- which the reachable path carries via the full declaration equality), so the
      -- closure-list agreement pins `argPoison` explicitly here: this forbids a clean
      -- trusted entry from being matched against a poison-permissive closure member.
      entry.decl.argPoison = argQt.poison

/-- Static pure closure-list members can be resolved to trusted entries. -/
def TrustedRegistryAgreesWithPFnTClosures
    (tr : TrustedRegistry) (argTyp : Typ) (tcls : List PFnTClosure) : Prop :=
  ∀ {id x retSpec capturedEnv argQt captures},
    PFnTClosure.extern id x retSpec capturedEnv argQt captures ∈ tcls →
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures ∧
      -- See `TrustedRegistryAgreesWithFnTClosures`: pin the declared-argument poison
      -- so a clean trusted entry cannot be matched against a permissive closure member.
      entry.decl.argPoison = argQt.poison

/-- Evidence that an impure app proof is using the function closure list
    produced by typechecking the app's function expression. -/
structure AppFnClosureListFromTypecheck
    (ctx : TypeContext) (e1 e2 : Expr) (res : TypeResult)
    (tcls : List FnTClosure) where
  appFuel : Nat
  fnFuel : Nat
  result2 : TypeResult
  result1 : TypeResult
  st1 : Typ
  st2 : Typ
  p : Poison
  app_typed : typecheck ctx (Expr.app e1 e2) appFuel = .ok res
  arg_typed : typecheck ctx e2 fnFuel = .ok result2
  fn_typed : typecheck (ctxAfter ctx result2) e1 fnFuel = .ok result1
  result_arrow : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls

/-- Evidence that a pure app proof is using the pfunction closure list produced
    by typechecking the app's function expression. -/
structure AppPfnClosureListFromTypecheck
    (ctx : TypeContext) (e1 e2 : Expr) (res : TypeResult)
    (tcls : List PFnTClosure) where
  appFuel : Nat
  fnFuel : Nat
  result2 : TypeResult
  result1 : TypeResult
  st1 : Typ
  st2 : Typ
  p : Poison
  app_typed : typecheck ctx (Expr.app e1 e2) appFuel = .ok res
  arg_typed : typecheck ctx e2 fnFuel = .ok result2
  fn_typed : typecheck (ctxAfter ctx result2) e1 fnFuel = .ok result1
  result_parrow : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls

mutual

/-- Extern declarations reachable through closure-typed values in a captured
    type environment.  This is the non-AST part of the trusted registry domain:
    initial contexts can contain function-typed variables whose closure bodies
    are not syntactically under the root expression. -/
inductive ExternDeclarationReachableFromCapturedEnv
    (root : Expr) (ctxRoot : TypeContext) :
    CapturedVarEnv → ExternId → ExternDeclaration → Prop where
  | head {x : Name} {qt : QTyp} {rest : CapturedVarEnv} {id : ExternId}
      {d : ExternDeclaration} :
      ExternDeclarationReachableFromQTyp root ctxRoot qt id d →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot ((x, qt) :: rest) id d
  | tail {x : Name} {qt : QTyp} {rest : CapturedVarEnv} {id : ExternId}
      {d : ExternDeclaration} :
      ExternDeclarationReachableFromCapturedEnv root ctxRoot rest id d →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot ((x, qt) :: rest) id d

inductive ExternDeclarationReachableFromQTyp
    (root : Expr) (ctxRoot : TypeContext) :
    QTyp → ExternId → ExternDeclaration → Prop where
  | arrow_regular_body {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {x : Name} {body : Expr} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      FnTClosure.regular x body σcap ∈ tcls →
      ExternDeclarationInProgram body id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | arrow_regular_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {x : Name} {body : Expr} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      FnTClosure.regular x body σcap ∈ tcls →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | arrow_extern_member {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {id : ExternId} {x : Name}
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp} :
      FnTClosure.extern id x retSpec effects σcap argQt captures ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .fn, typ := st1, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argQt.poison,
          captures := captures }
  | arrow_extern_return {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {outerId nestedId : ExternId} {x : Name}
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp}
      {d : ExternDeclaration} :
      FnTClosure.extern outerId x retSpec effects σcap argQt captures ∈ tcls →
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } nestedId d
  | arrow_extern_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {outerId : ExternId} {x : Name}
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp}
      {id : ExternId} {d : ExternDeclaration} :
      FnTClosure.extern outerId x retSpec effects σcap argQt captures ∈ tcls →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | arrow_regular_extern_body {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {id : ExternId} {x y : Name}
      {argTyp : Typ} {argPoison : Bool} {argPred : SyntaxPredicate}
      {retSpec : ExternReturn} {effects : List Effect}
      {σcap : CapturedVarEnv} :
      FnTClosure.regular x (Expr.externFn id y argTyp argPoison argPred retSpec effects cap) σcap ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := cap }
  | parrow_regular_body {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      PFnTClosure.regular x body σcap ∈ tcls →
      ExternDeclarationInProgram (PExpr.toExpr body) id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | parrow_regular_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      PFnTClosure.regular x body σcap ∈ tcls →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | parrow_extern_member {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {id : ExternId} {x : Name}
      {retSpec : ExternReturn} {σcap : CapturedVarEnv} {argQt : QTyp} :
      PFnTClosure.extern id x retSpec σcap argQt captures ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .pfn, typ := st1, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argQt.poison,
          captures := captures }
  | parrow_extern_return {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {outerId nestedId : ExternId} {x : Name}
      {retSpec : ExternReturn} {σcap : CapturedVarEnv} {argQt : QTyp} {d : ExternDeclaration} :
      PFnTClosure.extern outerId x retSpec σcap argQt captures ∈ tcls →
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } nestedId d
  | parrow_extern_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {outerId : ExternId} {x : Name}
      {retSpec : ExternReturn} {σcap : CapturedVarEnv} {argQt : QTyp}
      {id : ExternId} {d : ExternDeclaration} :
      PFnTClosure.extern outerId x retSpec σcap argQt captures ∈ tcls →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d

end

/-- `d` is an extern declaration reachable from the initial typed
    configuration consisting of root expression `root` and initial type context
    `ctxRoot`. -/
inductive ExternDeclarationReachableFromContext
    (root : Expr) (ctxRoot : TypeContext) :
    ExternId → ExternDeclaration → Prop where
  | ast {id : ExternId} {d : ExternDeclaration} :
      ExternDeclarationInProgram root id d →
      ExternDeclarationReachableFromContext root ctxRoot id d
  | var {x : Name} {qt : QTyp} {id : ExternId} {d : ExternDeclaration} :
      ctxRoot.varEnv.lookup x = some qt →
      ExternDeclarationReachableFromQTyp root ctxRoot qt id d →
      ExternDeclarationReachableFromContext root ctxRoot id d

/-- Trusted entries may only implement declarations reachable from the initial
    typed configuration. -/
def TrustedRegistryAgreesWithReachable
    (root : Expr) (ctxRoot : TypeContext) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationReachableFromContext root ctxRoot id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d

/-- The context-variable/closure branch of reachability in isolation: `d` is an
    extern declaration reachable from a variable bound in `ctxRoot.varEnv`, via
    that variable's qualified-type closures / captured environments.  Unlike
    `ExternDeclarationReachableFromContext`, this does NOT fold in the program AST
    declarations — it is exactly the `var` constructor's premise
    (doc/extern-regime.md, "Unblocking direction"). -/
def ContextExternReachable
    (root : Expr) (ctxRoot : TypeContext) (id : ExternId) (d : ExternDeclaration) : Prop :=
  ∃ (x : Name) (qt : QTyp),
    ctxRoot.varEnv.lookup x = some qt ∧
    ExternDeclarationReachableFromQTyp root ctxRoot qt id d

/-- The per-context trust premise of the public FR theorem: the trusted registry
    agrees with every extern declaration reachable from the *actual* initial
    typed configuration `(e, ctx)` — not from every adversarial extension of it.
    Definitionally `TrustedRegistryAgreesWithReachable e ctx tr`. -/
def InitialContextTrusted
    (tr : TrustedRegistry) (e : Expr) (ctx : TypeContext) : Prop :=
  TrustedRegistryAgreesWithReachable e ctx tr

/-- Registry-covered admissibility (doc/extern-regime.md, "Unblocking
    direction"): the trusted registry agrees with every *context-reachable*
    extern declaration.  Combined with `TrustedRegistryAgreesWithProgram` this
    yields the full `TrustedRegistryAgreesWithReachable` (see
    `TrustedRegistryAgreesWithReachable.of_registryCover`).  It also supports
    extern closures supplied only by the context. -/
def TrustedRegistryAgreesWithInitialContext
    (e : Expr) (ctx : TypeContext) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ContextExternReachable e ctx id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d

/-- Every syntactic extern declaration in `current` is covered by the initial
    reachable trust domain.  This keeps the proof spine's expression-indexed
    `CanUse` shape while allowing the public trust premise to be scoped to the
    initial typed configuration. -/
def ExternDeclarationReachableFromExpr
    (root : Expr) (ctxRoot : TypeContext) (current : Expr) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationInProgram current id d →
    ExternDeclarationReachableFromContext root ctxRoot id d

namespace ExternDeclarationReachableFromExpr

theorem root (root : Expr) (ctxRoot : TypeContext) :
    ExternDeclarationReachableFromExpr root ctxRoot root := by
  intro _id _d hprog
  exact ExternDeclarationReachableFromContext.ast hprog

theorem op_left {root ctxRoot e1 e2 op}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.op e1 op e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.op_left hprog)

theorem op_right {root ctxRoot e1 e2 op}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.op e1 op e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.op_right hprog)

theorem unaryop {root ctxRoot e op}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.unaryop op e)) :
    ExternDeclarationReachableFromExpr root ctxRoot e := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.unaryop hprog)

theorem ite_cond {root ctxRoot e1 e2 e3}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.ite e1 e2 e3)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.ite_cond hprog)

theorem ite_then {root ctxRoot e1 e2 e3}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.ite e1 e2 e3)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.ite_then hprog)

theorem ite_else {root ctxRoot e1 e2 e3}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.ite e1 e2 e3)) :
    ExternDeclarationReachableFromExpr root ctxRoot e3 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.ite_else hprog)

theorem newRef {root ctxRoot e}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.newRef e)) :
    ExternDeclarationReachableFromExpr root ctxRoot e := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.newRef hprog)

theorem assign_left {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.assign e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.assign_left hprog)

theorem assign_right {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.assign e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.assign_right hprog)

theorem deref {root ctxRoot e}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.deref e)) :
    ExternDeclarationReachableFromExpr root ctxRoot e := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.deref hprog)

theorem seq_left {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.seq e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.seq_left hprog)

theorem seq_right {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.seq e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.seq_right hprog)

theorem vlet_bound {root ctxRoot x e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.vlet x e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.vlet_bound hprog)

theorem vlet_body {root ctxRoot x e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.vlet x e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.vlet_body hprog)

theorem fn_body {root ctxRoot x argTyp body retTyp}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.fn x argTyp body retTyp)) :
    ExternDeclarationReachableFromExpr root ctxRoot body := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.fn_body hprog)

theorem pfn_body {root ctxRoot x argTyp body retTyp}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.pfn x argTyp body retTyp)) :
    ExternDeclarationReachableFromExpr root ctxRoot body := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.pfn_body hprog)

theorem app_fun {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.app e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e1 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.app_fun hprog)

theorem app_arg {root ctxRoot e1 e2}
    (h : ExternDeclarationReachableFromExpr root ctxRoot (Expr.app e1 e2)) :
    ExternDeclarationReachableFromExpr root ctxRoot e2 := by
  intro _id _d hprog
  exact h (ExternDeclarationInProgram.app_arg hprog)

end ExternDeclarationReachableFromExpr
