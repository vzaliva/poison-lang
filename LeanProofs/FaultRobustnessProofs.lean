/-
  FaultRobustnessProofs.lean - Orchestration of fault-robustness proofs.

  Imports all per-operator StepFR* files and assembles the step-level
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
import LeanProofs.ExternBoundary
import LeanProofs.ExternBoundaryProofs

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

private structure ExternDeclCanUseSyntaxClosed (CanUse : Expr → Prop) where
  op_left :
    ∀ {e1 e2 : Expr} {op : Op}, CanUse (Expr.op e1 op e2) → CanUse e1
  op_right :
    ∀ {e1 e2 : Expr} {op : Op}, CanUse (Expr.op e1 op e2) → CanUse e2
  unaryop :
    ∀ {e : Expr} {op : UnaryOp}, CanUse (Expr.unaryop op e) → CanUse e
  ite_cond :
    ∀ {e1 e2 e3 : Expr}, CanUse (Expr.ite e1 e2 e3) → CanUse e1
  ite_then :
    ∀ {e1 e2 e3 : Expr}, CanUse (Expr.ite e1 e2 e3) → CanUse e2
  ite_else :
    ∀ {e1 e2 e3 : Expr}, CanUse (Expr.ite e1 e2 e3) → CanUse e3
  newRef :
    ∀ {e : Expr}, CanUse (Expr.newRef e) → CanUse e
  assign_left :
    ∀ {e1 e2 : Expr}, CanUse (Expr.assign e1 e2) → CanUse e1
  assign_right :
    ∀ {e1 e2 : Expr}, CanUse (Expr.assign e1 e2) → CanUse e2
  deref :
    ∀ {e : Expr}, CanUse (Expr.deref e) → CanUse e
  seq_left :
    ∀ {e1 e2 : Expr}, CanUse (Expr.seq e1 e2) → CanUse e1
  seq_right :
    ∀ {e1 e2 : Expr}, CanUse (Expr.seq e1 e2) → CanUse e2
  vlet_bound :
    ∀ {x : Name} {e1 e2 : Expr}, CanUse (Expr.vlet x e1 e2) → CanUse e1
  vlet_body :
    ∀ {x : Name} {e1 e2 : Expr}, CanUse (Expr.vlet x e1 e2) → CanUse e2
  fn_body :
    ∀ {x : Name} {argTyp retTyp : Typ} {body : Expr},
      CanUse (Expr.fn x argTyp body retTyp) → CanUse body
  pfn_body :
    ∀ {x : Name} {argTyp retTyp : Typ} {body : Expr},
      CanUse (Expr.pfn x argTyp body retTyp) → CanUse body
  app_fun :
    ∀ {e1 e2 : Expr}, CanUse (Expr.app e1 e2) → CanUse e1
  app_arg :
    ∀ {e1 e2 : Expr}, CanUse (Expr.app e1 e2) → CanUse e2

namespace ExternDeclCanUseSyntaxClosed

private theorem of_reachable {root : Expr} {ctxRoot : TypeContext} :
    ExternDeclCanUseSyntaxClosed
      (fun current => ExternDeclarationReachableFromExpr root ctxRoot current) where
  op_left := fun h => ExternDeclarationReachableFromExpr.op_left h
  op_right := fun h => ExternDeclarationReachableFromExpr.op_right h
  unaryop := fun h => ExternDeclarationReachableFromExpr.unaryop h
  ite_cond := fun h => ExternDeclarationReachableFromExpr.ite_cond h
  ite_then := fun h => ExternDeclarationReachableFromExpr.ite_then h
  ite_else := fun h => ExternDeclarationReachableFromExpr.ite_else h
  newRef := fun h => ExternDeclarationReachableFromExpr.newRef h
  assign_left := fun h => ExternDeclarationReachableFromExpr.assign_left h
  assign_right := fun h => ExternDeclarationReachableFromExpr.assign_right h
  deref := fun h => ExternDeclarationReachableFromExpr.deref h
  seq_left := fun h => ExternDeclarationReachableFromExpr.seq_left h
  seq_right := fun h => ExternDeclarationReachableFromExpr.seq_right h
  vlet_bound := fun h => ExternDeclarationReachableFromExpr.vlet_bound h
  vlet_body := fun h => ExternDeclarationReachableFromExpr.vlet_body h
  fn_body := fun h => ExternDeclarationReachableFromExpr.fn_body h
  pfn_body := fun h => ExternDeclarationReachableFromExpr.pfn_body h
  app_fun := fun h => ExternDeclarationReachableFromExpr.app_fun h
  app_arg := fun h => ExternDeclarationReachableFromExpr.app_arg h

end ExternDeclCanUseSyntaxClosed

private abbrev ExternCallSingleFnProviderCtx
    (registry : ExternRegistry) (CanUse : Expr → Prop)
    (CtxReach : TypeContext → Prop) : Prop :=
  ∀ {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctx : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure},
    CtxReach ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctx res e1 e2 tcls
      htyped.st1 (registry := registry)

private abbrev ExternCallSinglePfnProviderCtx
    (registry : ExternRegistry) (CanUse : Expr → Prop)
    (CtxReach : TypeContext → Prop) : Prop :=
  ∀ {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctx : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure},
    CtxReach ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctx res e1 e2 tcls
      htyped.st1 (registry := registry)

private abbrev ExternCallSingleFnProviderReachableCtx
    (registry : ExternRegistry) (root : Expr) (ctxRoot : TypeContext)
    (CanUse : Expr → Prop) : Prop :=
  ∀ {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctx : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure},
    ContextReachableFrom root ctxRoot ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctx res e1 e2 tcls
      htyped.st1 (registry := registry)

private abbrev ExternCallSinglePfnProviderReachableCtx
    (registry : ExternRegistry) (root : Expr) (ctxRoot : TypeContext)
    (CanUse : Expr → Prop) : Prop :=
  ∀ {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctx : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure},
    ContextReachableFrom root ctxRoot ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctx res e1 e2 tcls
      htyped.st1 (registry := registry)

private abbrev ExternCallFRFnLocalProviderCtx
    (registry : ExternRegistry) (entryKey : ExternCallEntryKey)
    (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop) : Prop :=
  ∀ {ctx : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure},
    CtxReach ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
    TrustedRegistryAgreesWithProgramLocal ctx predSat tm e1 e2 res tcls
      htyped.st1 (entryKey := entryKey) (registry := registry)

private abbrev ExternCallFRPfnLocalProviderCtx
    (registry : ExternRegistry) (entryKey : ExternCallEntryKey)
    (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop) : Prop :=
  ∀ {ctx : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure},
    CtxReach ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
    TrustedRegistryAgreesWithPfnProgramLocal ctx predSat tm e1 e2 res tcls
      htyped.st1 (entryKey := entryKey) (registry := registry)

private abbrev ExternCallFRFnLocalProviderReachableCtx
    (registry : ExternRegistry) (entryKey : ExternCallEntryKey)
    (root : Expr) (ctxRoot : TypeContext) (CanUse : Expr → Prop) : Prop :=
  ∀ {ctx : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure},
    ContextReachableFrom root ctxRoot ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
    TrustedRegistryAgreesWithProgramLocal ctx predSat tm e1 e2 res tcls
      htyped.st1 (entryKey := entryKey) (registry := registry)

private abbrev ExternCallFRPfnLocalProviderReachableCtx
    (registry : ExternRegistry) (entryKey : ExternCallEntryKey)
    (root : Expr) (ctxRoot : TypeContext) (CanUse : Expr → Prop) : Prop :=
  ∀ {ctx : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure},
    ContextReachableFrom root ctxRoot ctx →
    CanUse (Expr.app e1 e2) →
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
    TrustedRegistryAgreesWithPfnProgramLocal ctx predSat tm e1 e2 res tcls
      htyped.st1 (entryKey := entryKey) (registry := registry)

private theorem AppFnClosureListFromTypecheck.regularBody_reachable
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 body : Expr}
    {res : TypeResult} {tcls : List FnTClosure} {x : Name}
    {σcap : CapturedVarEnv}
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls)
    (hqt : QTypReachableFrom root ctxRoot htyped.result1.qualType)
    (hmem : FnTClosure.regular x body σcap ∈ tcls) :
    ExternDeclarationReachableFromExpr root ctxRoot body := by
  intro id d hprog
  have hqtArrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow htyped.st1 htyped.st2 htyped.p tcls,
          poison := htyped.result1.qualType.poison, pred := htyped.result1.qualType.pred } := by
    cases hres : htyped.result1.qualType with
    | mk etyp qpoison qpred =>
        have harrow : etyp = ETyp.arrow htyped.st1 htyped.st2 htyped.p tcls := by
          simpa [hres] using htyped.result_arrow
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              htyped.result1.qualType id d := by
          simpa [hres] using hreach
        exact hqt hreach'
  exact QTypReachableFrom.fn_regular_body hqtArrow hmem hprog

private theorem AppPfnClosureListFromTypecheck.regularBody_reachable
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 : Expr} {body : PExpr}
    {res : TypeResult} {tcls : List PFnTClosure} {x : Name}
    {σcap : CapturedVarEnv}
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls)
    (hqt : QTypReachableFrom root ctxRoot htyped.result1.qualType)
    (hmem : PFnTClosure.regular x body σcap ∈ tcls) :
    ExternDeclarationReachableFromExpr root ctxRoot (PExpr.toExpr body) := by
  intro id d hprog
  have hqtParrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow htyped.st1 htyped.st2 htyped.p tcls,
          poison := htyped.result1.qualType.poison, pred := htyped.result1.qualType.pred } := by
    cases hres : htyped.result1.qualType with
    | mk etyp qpoison qpred =>
        have hparrow : etyp = ETyp.parrow htyped.st1 htyped.st2 htyped.p tcls := by
          simpa [hres] using htyped.result_parrow
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              htyped.result1.qualType id d := by
          simpa [hres] using hreach
        exact hqt hreach'
  exact QTypReachableFrom.pfn_regular_body hqtParrow hmem hprog

private theorem ExternCallSingleFnProviderReachableCtx_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {CanUse : Expr → Prop}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hqtOfApp :
      ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
        {tcls : List FnTClosure},
        ContextReachableFrom root ctxRoot ctx →
        CanUse (Expr.app e1 e2) →
        (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
        QTypReachableFrom root ctxRoot htyped.result1.qualType) :
    ExternCallSingleFnProviderReachableCtx
      (TrustedRegistry.toRuntimeRegistry tr) root ctxRoot CanUse := by
  intro _masked _CtxCons _ValCons _ctx _res _e1 _e2 _tcls hctx hcan htyped
  exact
    ExternCallBoundarySingleFnContract.of_trustedReachable hagrees
      (fun {_argTyp} {_argPoison} {_id} {_x} {_y} {_retSpec} {_effects}
          {_capturedEnv} {_memberCap} hsource =>
        ExternCallBoundaryFnStaticSource.reachable_from_app_typecheck
          htyped (hqtOfApp hctx hcan htyped) hsource)

private theorem ExternCallSinglePfnProviderReachableCtx_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {CanUse : Expr → Prop}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hqtOfApp :
      ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
        {tcls : List PFnTClosure},
        ContextReachableFrom root ctxRoot ctx →
        CanUse (Expr.app e1 e2) →
        (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
        QTypReachableFrom root ctxRoot htyped.result1.qualType) :
    ExternCallSinglePfnProviderReachableCtx
      (TrustedRegistry.toRuntimeRegistry tr) root ctxRoot CanUse := by
  intro _masked _CtxCons _ValCons _ctx _res _e1 _e2 _tcls hctx hcan htyped
  exact
    ExternCallBoundarySinglePfnContract.of_trustedReachable hagrees
      (fun {_argTyp} {_argPoison} {_id} {_x} {_y} {_retSpec}
          {_capturedEnv} {_memberCap} hsource =>
        ExternCallBoundaryPfnStaticSource.reachable_from_app_typecheck
          htyped (hqtOfApp hctx hcan htyped) hsource)

private theorem ExternCallFRFnLocalProviderReachableCtx_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {CanUse : Expr → Prop}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hqtOfApp :
      ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
        {tcls : List FnTClosure},
        ContextReachableFrom root ctxRoot ctx →
        CanUse (Expr.app e1 e2) →
        (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
        QTypReachableFrom root ctxRoot htyped.result1.qualType) :
    ExternCallFRFnLocalProviderReachableCtx
      (TrustedRegistry.toRuntimeRegistry tr) (ExternCallTrustedEntryKey tr)
      root ctxRoot CanUse := by
  intro _ctx _predSat _tm _e1 _e2 _res _tcls hctx hcan htyped
  exact
    TrustedRegistryAgreesWithProgramLocal.of_trustedReachable hagrees
      (fun {_argTyp} {_argPoison} {_id} {_x} {_y} {_retSpec} {_effects}
          {_capturedEnv} {_memberCap} hsource =>
        ExternCallBoundaryFnStaticSource.reachable_from_app_typecheck
          htyped (hqtOfApp hctx hcan htyped) hsource)

private theorem ExternCallFRPfnLocalProviderReachableCtx_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {CanUse : Expr → Prop}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hqtOfApp :
      ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
        {tcls : List PFnTClosure},
        ContextReachableFrom root ctxRoot ctx →
        CanUse (Expr.app e1 e2) →
        (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
        QTypReachableFrom root ctxRoot htyped.result1.qualType) :
    ExternCallFRPfnLocalProviderReachableCtx
      (TrustedRegistry.toRuntimeRegistry tr) (ExternCallTrustedEntryKey tr)
      root ctxRoot CanUse := by
  intro _ctx _predSat _tm _e1 _e2 _res _tcls hctx hcan htyped
  exact
    TrustedRegistryAgreesWithPfnProgramLocal.of_trustedReachable hagrees
      (fun {_argTyp} {_argPoison} {_id} {_x} {_y} {_retSpec}
          {_capturedEnv} {_memberCap} hsource =>
        ExternCallBoundaryPfnStaticSource.reachable_from_app_typecheck
          htyped (hqtOfApp hctx hcan htyped) hsource)

/-- Shared scaffold for the four literal arms (`unit`/`num`/`bool`/`str`) of the masked
single-run theorem.  Given the literal expression/value/element-type plus the fact that
`res` is the canonical literal result (`hres`), it discharges the
`isFunctionType`/`pred`/`ctxAfter` boilerplate and delegates to
`stepFRSingleRunFinalCleanPcTrue_literal_maskedReg`. -/
private lemma stepFRSingleRunFinalCleanPcTrue_literalArm_maskedReg
    (registry : ExternRegistry)
    (masked : Tag → Prop) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e₀ : Expr) (v₀ : Value) (ety : ETyp) (res : TypeResult)
    (hval : Expr.toValue? e₀ = some v₀)
    (hvtyp : ∀ θ, valueHasETyp θ v₀ ety)
    (hnotfun : ety.isFunctionType = false)
    (hres : res =
      { qualType := ⟨ety, false, Predicate.noPred⟩
        memEnv' := ctxᵢ.memEnv
        tagEnv' := ctxᵢ.tagEnv
        nextLoc' := ctxᵢ.nextLoc
        nextTag' := ctxᵢ.nextTag
        regime' := ctxᵢ.regime
        declared' := ctxᵢ.declaredExternRefs }) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctxᵢ e₀ res predSat tm (registry := registry) := by
  subst hres
  exact stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
    masked ctxᵢ predSat tm e₀ _ v₀ hval hvtyp hnotfun rfl (by simp [ctxAfter])

/-- Shared scaffold for the four extern-declaration arms (`externVal`/`externFn`/
`externPfn`/`externRef`) of the masked single-run theorem.  Each arm supplies its
declaration descriptor `d`, the `ExternDeclarationInProgram` witness, the boundary-typing
derivation `htyped`, and the kind-specific boundary-run obtainer `hBoundaryRun`; this lemma
runs the common normalize-then-delegate scaffold against the caller's `hdeclSingle`
contract.  Factored out of the masked single-run theorem (refactor T15). -/
private lemma stepFRSingleRunFinalCleanPcTrue_externDeclArm_maskedReg
    (registry : ExternRegistry) (CanUse : Expr → Prop)
    (masked : Tag → Prop) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e₀ : Expr) (fuel : Nat) (res : TypeResult)
    (id : ExternId) (d : ExternDeclaration)
    (hcan : CanUse e₀)
    (hdeclSingle :
      ∀ {e : Expr} {id : ExternId} {d : ExternDeclaration}
        {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
        {predSat : PredSat} {tm : TagMeaning} {impl : ExternImpl},
        CanUse e →
        ExternDeclarationInProgram e id d →
        ExternDeclBoundarySingleMaskedContract masked e ctx res predSat tm registry d impl)
    (hInProgram : ExternDeclarationInProgram e₀ id d)
    (hBoundaryRun :
      ∀ {cᵢ cₒ : Config} {v : Value},
        terminatesTo e₀ cᵢ cₒ v →
        ∃ impl, ExternDeclBoundaryRunForExpr e₀ d impl ctxᵢ res cᵢ cₒ v)
    (htyped : ExternBoundaryTyping.Decl d e₀ ctxᵢ res)
    (htc : typecheck ctxᵢ e₀ (Nat.succ fuel) = .ok res) :
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctxᵢ e₀ res predSat tm (registry := registry) := by
  intro hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨?_, ?_⟩
  · exact
      StepFRSingleRunTagMeaningPost.of_typecheck_preserves
        hExtTyping predSat tm ctxᵢ e₀ (Nat.succ fuel) res hwfTm hTmBounded hpredlaws htc
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm
        hwfcfg hres hrd ht hpc
  obtain ⟨impl, hrun⟩ := hBoundaryRun ht
  exact
    hdeclSingle
      (e := e₀) (id := id) (d := d) (impl := impl) hcan hInProgram
      hpredlaws hExtTyping hwfTm hTmBounded htyped μ ρ θ cf o hθwf hwf hric
      hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg hres hrd hrun.run hpc

/-- Bundle of the reachability/boundary contract hypotheses shared verbatim by the
masked and non-masked single-run FR theorems.  Projecting (or `obtain`-destructuring)
this record restores the individual hypotheses exactly as before. -/
private structure FRCtxContracts (registry : ExternRegistry)
    (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop) where
  hcallSingleFn : ExternCallSingleFnProviderCtx registry CanUse CtxReach
  hcallSinglePfn : ExternCallSinglePfnProviderCtx registry CanUse CtxReach
  hclosed : ExternDeclCanUseSyntaxClosed CanUse
  hctxPure :
    ∀ {ctx : TypeContext}, CtxReach ctx → CtxReach { ctx with pureCtx := true }
  hctxAfter : ∀ {ctx : TypeContext} {res : TypeResult},
    CtxReach ctx → CtxReach (ctxAfter ctx res)
  hctxTagTrue :
    ∀ {ctx : TypeContext} {k : Tag} {deps : Deps} {declared : List ExternId},
      CtxReach ctx →
        CtxReach { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                            declaredExternRefs := declared }
  hctxTagFalseNext :
    ∀ {ctx : TypeContext} {k : Tag} {deps : Deps} {nextLoc nextTag : Nat}
      {declared : List ExternId},
      CtxReach ctx →
        CtxReach
          { ctx with
            tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
            nextLoc := nextLoc,
            nextTag := nextTag,
            declaredExternRefs := declared }
  hctxAfterPc :
    ∀ {ctx : TypeContext} {res : TypeResult} {pc : Poison},
      CtxReach ctx → CtxReach { ctxAfter ctx res with pc := pc }
  hctxNext :
    ∀ {ctx : TypeContext} {nextLoc nextTag : Nat} {declared : List ExternId},
      CtxReach ctx → CtxReach { ctx with nextLoc := nextLoc, nextTag := nextTag,
                                         declaredExternRefs := declared }
  hctxVletBody :
    ∀ {ctx : TypeContext} {vname : Name} {e1 : Expr} {fuel : Nat}
      {res1 : TypeResult} {bodyCtx : TypeContext},
      CtxReach ctx →
      CanUse e1 →
      typecheck ctx e1 fuel = .ok res1 →
      bodyCtx =
        ({ ctx with
          memEnv := res1.memEnv',
          varEnv := VarTypeEnv.update ctx.varEnv vname res1.qualType,
          tagEnv := res1.tagEnv',
          nextLoc := res1.nextLoc',
          nextTag := res1.nextTag',
          regime := res1.regime',
          declaredExternRefs := res1.declared' } : TypeContext) →
      CtxReach bodyCtx
  hctxFnBody :
    ∀ {ctx : TypeContext} {res : TypeResult} {e1 e2 : Expr}
      {tcls : List FnTClosure} {x : Name} {body : Expr}
      {σcap : List (Name × QTyp)} {bodyCtx : TypeContext}
      {etyp2 : ETyp} {p2 : Poison} {pred2 : Predicate},
      CtxReach ctx →
      CanUse (Expr.app e1 e2) →
      (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls) →
      htyped.result2.qualType = ⟨etyp2, p2, pred2⟩ →
      FnTClosure.regular x body σcap ∈ tcls →
      bodyCtx.varEnv =
        VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } →
      CtxReach bodyCtx
  hctxPfnBody :
    ∀ {ctx : TypeContext} {res : TypeResult} {e1 e2 : Expr}
      {tcls : List PFnTClosure} {x : Name} {pbody : PExpr}
      {σcap : List (Name × QTyp)} {bodyCtx : TypeContext}
      {etyp2 : ETyp} {p2 : Poison} {pred2 : Predicate},
      CtxReach ctx →
      CanUse (Expr.app e1 e2) →
      (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls) →
      htyped.result2.qualType = ⟨etyp2, p2, pred2⟩ →
      PFnTClosure.regular x pbody σcap ∈ tcls →
      bodyCtx.varEnv =
        VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } →
      CtxReach bodyCtx
  hcanFnBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {x : Name} {body : Expr}
      {σcap : List (Name × QTyp)},
      CtxReach ctx →
      CanUse (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      FnTClosure.regular x body σcap ∈ tcls →
      CanUse body
  hcanPfnBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List PFnTClosure} {x : Name} {pbody : PExpr}
      {σcap : List (Name × QTyp)},
      CtxReach ctx →
      CanUse (Expr.app e1 e2) →
      AppPfnClosureListFromTypecheck ctx e1 e2 res tcls →
      PFnTClosure.regular x pbody σcap ∈ tcls →
      CanUse (PExpr.toExpr pbody)
  hdeclSingle :
    ∀ {e : Expr} {id : ExternId} {d : ExternDeclaration}
      {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
      {predSat : PredSat} {tm : TagMeaning} {impl : ExternImpl},
      CanUse e →
      ExternDeclarationInProgram e id d →
      ExternDeclBoundarySingleMaskedContract masked e ctx res predSat tm registry d impl

/-- Step-theorem contract bundle: extends `FRCtxContracts` with the entry-key
uniqueness/FR providers and the FR-level declaration boundary contract used only by
the two-run step theorem. -/
private structure FRStepContracts (registry : ExternRegistry)
    (entryKey : ExternCallEntryKey)
    (CanUse : Expr → Prop) (CtxReach : TypeContext → Prop)
    extends FRCtxContracts registry CanUse CtxReach where
  hentryKey_unique :
    ∀ {id : ExternId} {entry₀ entry₁ : TrustedExternEntry},
      entryKey id entry₀ → entryKey id entry₁ → entry₀ = entry₁
  hcallFR_of_entryKey :
    ∀ {id : ExternId} {entry : TrustedExternEntry},
      entryKey id entry → ExternCallBoundaryFR entry.decl entry.impl
  hfnLocal : ExternCallFRFnLocalProviderCtx registry entryKey CanUse CtxReach
  hpfnLocal : ExternCallFRPfnLocalProviderCtx registry entryKey CanUse CtxReach
  hdeclFR :
    ∀ {e : Expr} {id : ExternId} {d : ExternDeclaration}
      {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
      {predSat : PredSat} {tm : TagMeaning} {impl₀ impl₁ : ExternImpl},
      CanUse e →
      ExternDeclarationInProgram e id d →
      ExternDeclBoundaryFRContract ctx postExpr res predSat tm registry d impl₀ impl₁

private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_with_contracts_canUse_ctxReach
    (registry : ExternRegistry)
  (hOp : RegistryOperationalSafe registry)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (C : FRCtxContracts registry CanUse CtxReach)
  (masked : Tag → Prop)
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  CtxReach ctxᵢ →
  CanUse e →
  ∀ fuel res,
    typecheck ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      ctxᵢ e res predSat tm (registry := registry) := by
  obtain ⟨hcallSingleFn, hcallSinglePfn, hclosed, hctxPure, hctxAfter, hctxTagTrue,
    hctxTagFalseNext, hctxAfterPc, hctxNext, hctxVletBody, hctxFnBody, hctxPfnBody,
    hcanFnBody, hcanPfnBody, hdeclSingle⟩ := C
  intro hctxCurrent hcan fuel res htc
  revert tm masked e ctxᵢ res htc hcan hctxCurrent
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
      intro masked e ctxᵢ tm hctxCurrent hcan res htc
      have IH' :
          ∀ m < n, ∀ (tm' : TagMeaning) (masked' : Tag → Prop) (e' : Expr)
            (ctx' : TypeContext),
            CtxReach ctx' →
            CanUse e' →
            ∀ (res' : TypeResult),
            typecheck ctx' e' m = .ok res' →
            StepFRSingleRunFinalCleanPcTrueMaskedRegParam
              masked'
              (fun ctx μ ρ θ =>
                consistentWithRegimeMasked masked' predSat ctx.regime ctx μ ρ θ)
              (fun R qt μ θ v =>
                valueConsistentWithRegimeMasked masked' predSat R qt μ θ v)
              ctx' e' res' predSat tm' (registry := registry) := by
        intro m hm tm' masked' e' ctx' hctx' hcan' res' htc'
        exact IH m hm masked' e' ctx' tm' hctx' hcan' res' htc'
      cases n with
      | zero =>
          simp [typecheck, typecheckExpr] at htc
      | succ fuel =>
          cases e with
          | unit =>
              simp [typecheck, typecheckExpr, typecheckUnit] at htc
              exact stepFRSingleRunFinalCleanPcTrue_literalArm_maskedReg
                registry masked ctxᵢ predSat tm Expr.unit Value.unit ETyp.unit res
                (by simp [Expr.toValue?]) (fun _ => valueHasETyp.unit) (by decide)
                (by cases htc; rfl)
          | num k =>
              simp [typecheck, typecheckExpr, typecheckInt] at htc
              exact stepFRSingleRunFinalCleanPcTrue_literalArm_maskedReg
                registry masked ctxᵢ predSat tm (Expr.num k) (Value.num k) ETyp.int res
                (by simp [Expr.toValue?]) (fun _ => valueHasETyp.num k) (by decide)
                (by cases htc; rfl)
          | bool b =>
              simp [typecheck, typecheckExpr, typecheckBool] at htc
              exact stepFRSingleRunFinalCleanPcTrue_literalArm_maskedReg
                registry masked ctxᵢ predSat tm (Expr.bool b) (Value.bool b) ETyp.bool res
                (by simp [Expr.toValue?]) (fun _ => valueHasETyp.bool b) (by decide)
                (by cases htc; rfl)
          | str s =>
              simp [typecheck, typecheckExpr, typecheckString] at htc
              exact stepFRSingleRunFinalCleanPcTrue_literalArm_maskedReg
                registry masked ctxᵢ predSat tm (Expr.str s) (Value.str s) ETyp.string res
                (by simp [Expr.toValue?]) (fun _ => valueHasETyp.str s) (by decide)
                (by cases htc; rfl)
          | var name =>
              exact
                stepFRSingleRunFinalCleanPcTrue_var_maskedReg
                  masked
                  ctxᵢ predSat tm name res fuel
                  htc
          | op e1 op e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_op_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e1 e2 op fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.op_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.op_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      hOp
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      htc
          | unaryop uop e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_unaryop_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e uop fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.unaryop hclosed hcan)
                      hctxCurrent
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      htc
          | ite e1 e2 e3 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_ite_succ, typecheckIf] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_ite_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e1 e2 e3 fuel' res
                      CanUse CtxReach hOp
                      (ExternDeclCanUseSyntaxClosed.ite_cond hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.ite_then hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.ite_else hclosed hcan)
                      hctxCurrent hctxPure hctxTagTrue hctxTagFalseNext
                      hctxAfterPc hctxNext IH' htc
          | newRef e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckNewRef] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_newRef_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.newRef hclosed hcan)
                      hctxCurrent
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      hOp
                      htc
          | assign e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckAssign] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_assign_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.assign_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.assign_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      hOp
                      htc
          | deref e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckDeref] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_deref_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm e fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.deref hclosed hcan)
                      hctxCurrent
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      htc
          | seq e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_seq_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm hOp e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.seq_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.seq_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      htc
          | vlet z e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_vlet_maskedReg_with_expr_proof
                      masked ctxᵢ predSat tm z e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.vlet_bound hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.vlet_body hclosed hcan)
                      hctxCurrent
                      (fun htc1 hbodyEq hctx =>
                        hctxVletBody hctx (ExternDeclCanUseSyntaxClosed.vlet_bound hclosed hcan)
                          htc1 hbodyEq)
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                        IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      hOp
                      htc
          | fn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_fn_maskedReg
                  masked ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | pfn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_pfn_maskedReg
                  masked ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | app e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckApp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_app_maskedReg_with_expr_proof_ctxReach
                      masked ctxᵢ predSat tm (registry := registry) hOp
                      e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.app_fun hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.app_arg hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      (fun {tcls} {x} {body} {σcap} htyped hmem =>
                        hcanFnBody hctxCurrent hcan htyped hmem)
                      (fun {tcls} {x} {pbody} {σcap} htyped hmem =>
                        hcanPfnBody hctxCurrent hcan htyped hmem)
                      (fun {_tcls} {_x} {_body} {_σcap} {_bodyCtx}
                        {_etyp2} {_p2} {_pred2} htyped hqt hmem hbodyCtx =>
                          hctxFnBody hctxCurrent hcan htyped hqt hmem hbodyCtx)
                      (fun {_tcls} {_x} {_pbody} {_σcap} {_bodyCtx}
                        {_etyp2} {_p2} {_pred2} htyped hqt hmem hbodyCtx =>
                          hctxPfnBody hctxCurrent hcan htyped hqt hmem hbodyCtx)
                      (fun m hm {tmᵢ} e' ctx' _hctx hcan' _hwfTm _hTmBounded res' htc' =>
                          IH' m hm tmᵢ masked e' ctx' _hctx hcan' res' htc')
                      (fun {tcls} htyped => hcallSingleFn (tcls := tcls) hctxCurrent hcan htyped)
                      (fun {tcls} htyped => hcallSinglePfn (tcls := tcls) hctxCurrent hcan htyped)
                      htc
          | externVal id t p pr =>
              exact stepFRSingleRunFinalCleanPcTrue_externDeclArm_maskedReg
                registry CanUse masked ctxᵢ predSat tm (Expr.externVal id t p pr) fuel res
                id { id := id, kind := .val, typ := t, argName := none,
                     retSpec := none, effects := [], preds := [pr], argPoison := false }
                hcan hdeclSingle ExternDeclarationInProgram.externVal
                (fun {_cᵢ _cₒ _v} ht =>
                  ExternDeclBoundaryRun.of_terminatesTo_externVal (ctx := ctxᵢ) (res := res) ht)
                (ExternBoundaryTyping.Decl.val htc) htc
          | externFn id n t argPoison argPred r eff caps =>
              exact stepFRSingleRunFinalCleanPcTrue_externDeclArm_maskedReg
                registry CanUse masked ctxᵢ predSat tm
                (Expr.externFn id n t argPoison argPred r eff caps) fuel res
                id { id := id, kind := .fn, typ := t, argName := some n,
                     retSpec := some r, effects := eff,
                     preds := collectExternPreds r eff, argPoison := argPoison, captures := caps }
                hcan hdeclSingle ExternDeclarationInProgram.externFn
                (fun {_cᵢ _cₒ _v} ht =>
                  ExternDeclBoundaryRun.of_terminatesTo_externFn (ctx := ctxᵢ) (res := res) ht)
                (ExternBoundaryTyping.Decl.fn htc) htc
          | externPfn id n t argPoison argPred r caps =>
              exact stepFRSingleRunFinalCleanPcTrue_externDeclArm_maskedReg
                registry CanUse masked ctxᵢ predSat tm
                (Expr.externPfn id n t argPoison argPred r caps) fuel res
                id { id := id, kind := .pfn, typ := t, argName := some n,
                     retSpec := some r, effects := [],
                     preds := collectExternPreds r [], argPoison := argPoison, captures := caps }
                hcan hdeclSingle ExternDeclarationInProgram.externPfn
                (fun {_cᵢ _cₒ _v} ht =>
                  ExternDeclBoundaryRun.of_terminatesTo_externPfn (ctx := ctxᵢ) (res := res) ht)
                (ExternBoundaryTyping.Decl.pfn htc) htc
          | externRef id rp rpred cp cpred =>
              exact stepFRSingleRunFinalCleanPcTrue_externDeclArm_maskedReg
                registry CanUse masked ctxᵢ predSat tm (Expr.externRef id rp rpred cp cpred) fuel res
                id { id := id, kind := .ref, typ := Typ.ref Typ.int, argName := none,
                     retSpec := none, effects := [], preds := [rpred, cpred],
                     argPoison := false, refPoison := rp, cellPoison := cp }
                hcan hdeclSingle ExternDeclarationInProgram.externRef
                (fun {_cᵢ _cₒ _v} ht =>
                  ExternDeclBoundaryRun.of_terminatesTo_externRef (ctx := ctxᵢ) (res := res) ht)
                (ExternBoundaryTyping.Decl.ref htc) htc

private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_with_contracts_canUse_ctxReach
  (registry : ExternRegistry)
  (hOp : RegistryOperationalSafe registry)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (C : FRCtxContracts registry CanUse CtxReach)
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  CtxReach ctxᵢ →
  CanUse e →
  ∀ fuel res,
    typecheck ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrue ctxᵢ e res predSat tm (registry := registry) := by
  intro hctxCurrent hcan fuel res htc
  have hmasked :=
    TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_with_contracts_canUse_ctxReach
      registry hOp CanUse CtxReach C
      (masked := fun _ => False) e ctxᵢ predSat tm hctxCurrent hcan fuel res htc
  intro hpredlaws hExtTyping hwfTm hTmBounded htagBnd
  have hmasked_inst := hmasked hpredlaws hExtTyping hwfTm hTmBounded
  refine ⟨hmasked_inst.1, ?_⟩
  intro μ ρ θ cf o hθwf hwf hric hreg hcwr a pm hwfcfg hres hrd ht hpc
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
  have hmasked_absent_init :
      MaskedTagsAbsentFromTrueTagEnv (fun _ => False) ctxᵢ :=
    MaskedTagsAbsentFromTrueTagEnv_false ctxᵢ
  rcases
      hmasked_inst.2 μ ρ θ cf o hθwf hwf hric hreg_masked hmasked_none_init
        hmasked_absent_init (fun k hk => hk.elim) htagBnd hcwr_masked a pm hwfcfg hres hrd ht hpc
    with ⟨θ', hθext, hvaltyp, hric', hcwr_masked', hvalc_masked', hpres, hfresh, hrd'⟩
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
  exact ⟨θ', hθext, hvaltyp, hric', hcwr', hvalc', hpres, hfresh, hrd'⟩

-- Step theorem: proves StepFR directly.
-- Restructured to avoid variable capture: induction is generalized over all expressions
private theorem TypeSystemEnforcesFaultRobustness_step_with_contracts_canUse_ctxReach
  (registry : ExternRegistry)
  (hOp : RegistryOperationalSafe registry)
  (entryKey : ExternCallEntryKey)
  (CanUse : Expr → Prop)
  (CtxReach : TypeContext → Prop)
  (C : FRStepContracts registry entryKey CanUse CtxReach)
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  CtxReach ctxᵢ →
  CanUse e →
  TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat tm (registry := registry) := by
  have Cbase := C.toFRCtxContracts
  obtain ⟨⟨hcallSingleFn, hcallSinglePfn, hclosed, hctxPure, hctxAfter, hctxTagTrue,
      hctxTagFalseNext, hctxAfterPc, hctxNext, hctxVletBody, hctxFnBody, hctxPfnBody,
      hcanFnBody, hcanPfnBody, hdeclSingle⟩,
      hentryKey_unique, hcallFR_of_entryKey, hfnLocal, hpfnLocal, hdeclFR⟩ := C
  intro hctxStart hcan
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel res htc
  -- Use strong induction on fuel, generalized over all e and ctxᵢ
  -- The key insight: we need IH to work for any expression, not just our specific e
  revert tm e ctxᵢ res htc hcan hctxStart
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctxᵢ tm hctxCurrent hcan res htc
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
              declared' := ctxᵢ.declaredExternRefs
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
            exact stepFR_literal ctxᵢ predSat tm Expr.unit res Value.unit hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.unit) hpoison hnotfun hnotref hpredNo hctxAfter
        | num n =>
            simp [typecheck, typecheckExpr, typecheckInt] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.int, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
              declared' := ctxᵢ.declaredExternRefs
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
            exact stepFR_literal ctxᵢ predSat tm (Expr.num n) res (Value.num n) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.num n) hpoison hnotfun hnotref hpredNo hctxAfter
        | bool b =>
            simp [typecheck, typecheckExpr, typecheckBool] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.bool, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
              declared' := ctxᵢ.declaredExternRefs
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
            exact stepFR_literal ctxᵢ predSat tm (Expr.bool b) res (Value.bool b) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.bool b) hpoison hnotfun hnotref hpredNo hctxAfter
        | str s =>
            simp [typecheck, typecheckExpr, typecheckString] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.string, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
              declared' := ctxᵢ.declaredExternRefs
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
            exact stepFR_literal ctxᵢ predSat tm (Expr.str s) res (Value.str s) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.str s) hpoison hnotfun hnotref hpredNo hctxAfter
        | var name =>
            exact stepFR_var ctxᵢ predSat tm name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                exact
                    stepFR_op_with_expr_proof ctxᵢ predSat e1 e2 op fuel' res tm
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.op_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.op_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      hOp
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      htc
        | unaryop uop e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                exact
                    stepFR_unaryop_with_expr_proof ctxᵢ predSat e uop fuel' res tm
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.unaryop hclosed hcan)
                      hctxCurrent
                      hOp
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      htc
        | ite e1 e2 e3 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckIf] at htc
              | succ fuel' =>
                have hsingleIH :
                    StepFRSingleRunFinalCleanPcTrue_IH_WithExprCtx predSat tm
                      (Nat.succ (Nat.succ fuel')) CanUse CtxReach
                      (registry := registry) := by
                  intro m _hm tmᵢ e ctx' hctx' hcan' hwfTm' hTmBounded' res' htc'
                  exact
                    TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_with_contracts_canUse_ctxReach
                      registry hOp CanUse CtxReach Cbase
                      e ctx' predSat tmᵢ hctx' hcan' m res' htc'
                exact
                  stepFR_ite_with_expr_proof ctxᵢ predSat tm e1 e2 e3 fuel' res
                    CanUse
                    CtxReach
                    hOp
                    hctxCurrent
                    (hctxPure hctxCurrent)
                    (fun k deps declared => hctxTagTrue hctxCurrent)
                    (fun k deps nextLoc nextTag declared => hctxTagFalseNext hctxCurrent)
                    (fun {res1} _htc1 => by
                      simpa [ctxAfter] using
                        hctxAfterPc (ctx := ctxᵢ) (res := res1)
                          (pc := joinPoison ctxᵢ.pc res1.qualType.poison) hctxCurrent)
                    (fun {res1} {res2} _htc1 => by
                      simpa [ctxAfter] using
                        hctxNext
                          (ctx := { ctxAfter ctxᵢ res1 with
                            pc := joinPoison ctxᵢ.pc res1.qualType.poison })
                          (nextLoc := res2.nextLoc') (nextTag := res2.nextTag')
                          (hctxAfterPc (ctx := ctxᵢ) (res := res1)
                            (pc := joinPoison ctxᵢ.pc res1.qualType.poison) hctxCurrent))
                    (ExternDeclCanUseSyntaxClosed.ite_cond hclosed hcan)
                    (ExternDeclCanUseSyntaxClosed.ite_then hclosed hcan)
                    (ExternDeclCanUseSyntaxClosed.ite_else hclosed hcan)
                    (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                      IH m hm e ctx tmᵢ hctx hcan' res htc)
                    hsingleIH
                    htc
        | newRef e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                exact
                    stepFR_newRef_with_expr_proof ctxᵢ predSat e fuel' res tm
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.newRef hclosed hcan)
                      hctxCurrent
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      hOp
                      htc
        | assign e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckAssign] at htc
            | succ fuel' =>
                exact
                    stepFR_assign_with_expr_proof ctxᵢ predSat tm e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.assign_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.assign_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      hOp
                      htc
        | deref e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckDeref] at htc
            | succ fuel' =>
                exact
                    stepFR_deref_with_expr_proof ctxᵢ predSat tm e fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.deref hclosed hcan)
                      hctxCurrent
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      hOp
                      htc
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                exact
                    stepFR_seq_with_expr_proof ctxᵢ predSat e1 e2 fuel' res tm
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.seq_left hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.seq_right hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      hOp
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      htc
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                exact
                    stepFR_vlet_with_expr_proof ctxᵢ predSat vname e1 e2 fuel' res tm
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.vlet_bound hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.vlet_body hclosed hcan)
                      hctxCurrent
                      (fun {res1} {bodyCtx} htc1 hbodyEq hctx =>
                        hctxVletBody hctx (ExternDeclCanUseSyntaxClosed.vlet_bound hclosed hcan)
                          htc1 hbodyEq)
                      (fun m hm {tmᵢ} e ctx hctx hcan' _hwfTm _htagBounded res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      hOp
                      htc
        | fn name ty e1 ty2 =>
            exact stepFR_fn ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | pfn name ty e1 ty2 =>
            exact stepFR_pfn ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | app e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckApp] at htc
            | succ fuel' =>
                have hsingleIH :
                    StepFRSingleRunFinalCleanPcTrue_IH_WithExprCtx predSat tm
                      (Nat.succ (Nat.succ fuel')) CanUse
                      CtxReach
                      (registry := registry) := by
                  intro m _hm tmᵢ e ctx' hctx' hcan' hwfTm' _hTmBounded' res' htc'
                  exact
                    TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_with_contracts_canUse_ctxReach
                      registry hOp CanUse CtxReach Cbase
                      e ctx' predSat tmᵢ hctx' hcan' m res' htc'
                exact
                    stepFR_app_with_expr_proof ctxᵢ predSat tm (registry := registry) hOp
                      e1 e2 fuel' res
                      CanUse
                      CtxReach
                      (ExternDeclCanUseSyntaxClosed.app_fun hclosed hcan)
                      (ExternDeclCanUseSyntaxClosed.app_arg hclosed hcan)
                      hctxCurrent
                      hctxAfter
                      (fun {tcls} {x} {body} {σcap} htyped hmem =>
                        hcanFnBody hctxCurrent hcan htyped hmem)
                      (fun {tcls} {x} {pbody} {σcap} htyped hmem =>
                        hcanPfnBody hctxCurrent hcan htyped hmem)
                      (fun {_tcls} {_x} {_body} {_σcap} {_bodyCtx}
                        {_etyp2} {_p2} {_pred2} htyped hqt hmem hbodyCtx =>
                          hctxFnBody hctxCurrent hcan htyped hqt hmem hbodyCtx)
                      (fun {_tcls} {_x} {_pbody} {_σcap} {_bodyCtx}
                        {_etyp2} {_p2} {_pred2} htyped hqt hmem hbodyCtx =>
                          hctxPfnBody hctxCurrent hcan htyped hqt hmem hbodyCtx)
                      (fun m hm {tmᵢ} e ctx hctx hcan' hwfTm' htagBounded' res htc =>
                        IH m hm e ctx tmᵢ hctx hcan' res htc)
                      (fun m hm {tmᵢ} e ctx hctx hcan' hwfTm' hTmBounded' res htc =>
                        hsingleIH m hm (tmᵢ := tmᵢ) e ctx hctx hcan' hwfTm'
                          hTmBounded' res htc)
                      (entryKey := entryKey)
                    (_hentryKey_unique := hentryKey_unique)
                    (_hcallFR_of_entryKey := hcallFR_of_entryKey)
                    (_hfnLocal := fun {tcls} htyped =>
                      hfnLocal (tcls := tcls) hctxCurrent hcan htyped)
                    (_hpfnLocal := fun {tcls} htyped =>
                      hpfnLocal (tcls := tcls) hctxCurrent hcan htyped)
                    htc
        | externVal id t p pr =>
            -- Extern declaration success is normalized to boundary-run evidence before the
            -- caller-supplied boundary provider consumes it.
            intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
                  o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁
                  hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
            obtain ⟨impl₀, hrun₀⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externVal
                (ctx := ctxᵢ) (res := res) ht₀
            obtain ⟨impl₁, hrun₁⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externVal
                (ctx := ctxᵢ) (res := res) ht₁
            have htyped :
                ExternBoundaryTyping.Decl
                  { id := id, kind := .val, typ := t, argName := none,
                    retSpec := none, effects := [], preds := [pr], argPoison := false }
                  (Expr.externVal id t p pr) ctxᵢ res :=
              ExternBoundaryTyping.Decl.val htc
            exact
              hdeclFR
                (e := Expr.externVal id t p pr) (id := id)
                (d := { id := id, kind := .val, typ := t, argName := none,
                        retSpec := none, effects := [], preds := [pr], argPoison := false })
                (impl₀ := impl₀) (impl₁ := impl₁)
                hcan
                ExternDeclarationInProgram.externVal
                hpredlaws hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁
                cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
                hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrun₀ hrun₁
        | externFn id n t argPoison argPred r eff caps =>
            -- Extern declaration success is normalized to boundary-run evidence before the
            -- caller-supplied boundary provider consumes it.
            intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
                  o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁
                  hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
            obtain ⟨impl₀, hrun₀⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externFn
                (ctx := ctxᵢ) (res := res) ht₀
            obtain ⟨impl₁, hrun₁⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externFn
                (ctx := ctxᵢ) (res := res) ht₁
            have htyped :
                ExternBoundaryTyping.Decl
                  { id := id, kind := .fn, typ := t, argName := some n,
                    retSpec := some r, effects := eff,
                    preds := collectExternPreds r eff, argPoison := argPoison, captures := caps }
                  (Expr.externFn id n t argPoison argPred r eff caps) ctxᵢ res :=
              ExternBoundaryTyping.Decl.fn htc
            exact
              hdeclFR
                (e := Expr.externFn id n t argPoison argPred r eff caps) (id := id)
                (d := { id := id, kind := .fn, typ := t, argName := some n,
                        retSpec := some r, effects := eff,
                        preds := collectExternPreds r eff, argPoison := argPoison, captures := caps })
                (impl₀ := impl₀) (impl₁ := impl₁)
                hcan
                ExternDeclarationInProgram.externFn
                hpredlaws hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁
                cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
                hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrun₀ hrun₁
        | externPfn id n t argPoison argPred r caps =>
            -- Extern declaration success is normalized to boundary-run evidence before the
            -- caller-supplied boundary provider consumes it.
            intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
                  o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁
                  hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
            obtain ⟨impl₀, hrun₀⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externPfn
                (ctx := ctxᵢ) (res := res) ht₀
            obtain ⟨impl₁, hrun₁⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externPfn
                (ctx := ctxᵢ) (res := res) ht₁
            have htyped :
                ExternBoundaryTyping.Decl
                  { id := id, kind := .pfn, typ := t, argName := some n,
                    retSpec := some r, effects := [],
                    preds := collectExternPreds r [], argPoison := argPoison, captures := caps }
                  (Expr.externPfn id n t argPoison argPred r caps) ctxᵢ res :=
              ExternBoundaryTyping.Decl.pfn htc
            exact
              hdeclFR
                (e := Expr.externPfn id n t argPoison argPred r caps) (id := id)
                (d := { id := id, kind := .pfn, typ := t, argName := some n,
                        retSpec := some r, effects := [],
                        preds := collectExternPreds r [], argPoison := argPoison, captures := caps })
                (impl₀ := impl₀) (impl₁ := impl₁)
                hcan
                ExternDeclarationInProgram.externPfn
                hpredlaws hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁
                cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
                hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrun₀ hrun₁
        | externRef id rp rpred cp cpred =>
            -- Extern ref declaration success is normalized to boundary-run evidence
            -- before the caller-supplied boundary provider consumes it.
            intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
                  o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁
                  hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ ht₀ ht₁
            obtain ⟨impl₀, hrun₀⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externRef
                (ctx := ctxᵢ) (res := res) ht₀
            obtain ⟨impl₁, hrun₁⟩ :=
              ExternDeclBoundaryRun.of_terminatesTo_externRef
                (ctx := ctxᵢ) (res := res) ht₁
            have htyped :
                ExternBoundaryTyping.Decl
                  { id := id, kind := .ref, typ := Typ.ref Typ.int, argName := none,
                    retSpec := none, effects := [], preds := [rpred, cpred],
                    argPoison := false, refPoison := rp, cellPoison := cp }
                  (Expr.externRef id rp rpred cp cpred) ctxᵢ res :=
              ExternBoundaryTyping.Decl.ref htc
            exact
              hdeclFR
                (e := Expr.externRef id rp rpred cp cpred) (id := id)
                (d := { id := id, kind := .ref, typ := Typ.ref Typ.int, argName := none,
                        retSpec := none, effects := [], preds := [rpred, cpred],
                        argPoison := false, refPoison := rp, cellPoison := cp })
                (impl₀ := impl₀) (impl₁ := impl₁)
                hcan
                ExternDeclarationInProgram.externRef
                hpredlaws hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁
                cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
                hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrun₀ hrun₁

private theorem TypeSystemEnforcesFaultRobustness_step_with_reachableCtx_canUse
  {tr : TrustedRegistry} {root current : Expr} {ctxRoot : TypeContext}
  (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
  (hcurrent : ExternDeclarationReachableFromExpr root ctxRoot current)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (hOp : RegistryOperationalSafe (TrustedRegistry.toRuntimeRegistry tr)) :
  ContextReachableFrom root ctxRoot ctxᵢ →
  TypeSystemEnforcesFaultRobustness_step_spec current ctxᵢ predSat tm
    (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro hctxStart
  let hqtypOfTypecheck :
      ∀ {ctx : TypeContext} {e : Expr} {fuel : Nat} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e fuel = .ok res →
        QTypReachableFrom root ctxRoot res.qualType :=
    fun {ctx} {e} {_fuel} {_res} hctx hcan htc =>
      QTypReachableFrom.of_typecheck hctx hcan htc
  exact
    TypeSystemEnforcesFaultRobustness_step_with_contracts_canUse_ctxReach
      (TrustedRegistry.toRuntimeRegistry tr) hOp
      (ExternCallTrustedEntryKey tr)
      (fun e => ExternDeclarationReachableFromExpr root ctxRoot e)
      (ContextReachableFrom root ctxRoot)
      {
        hcallSingleFn :=
      (ExternCallSingleFnProviderReachableCtx_of_reachable hagrees
        (fun {ctx} {e1} {e2} {_res} {_tcls} hctx hcanApp htyped =>
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)),
        hcallSinglePfn :=
      (ExternCallSinglePfnProviderReachableCtx_of_reachable hagrees
        (fun {ctx} {e1} {e2} {_res} {_tcls} hctx hcanApp htyped =>
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)),
        hclosed :=
      ExternDeclCanUseSyntaxClosed.of_reachable,
        hctxPure :=
      (fun {ctx} hctx => by
        intro x qt hlookup
        exact hctx (by simpa using hlookup)),
        hctxAfter :=
      (fun {ctx} {res} hctx => ContextReachableFrom.ctxAfter hctx),
        hctxTagTrue :=
      (fun {ctx} {_k} {_deps} {_declared} hctx => by
        intro x qt hlookup
        exact hctx (by simpa using hlookup)),
        hctxTagFalseNext :=
      (fun {ctx} {_k} {_deps} {_nextLoc} {_nextTag} {_declared} hctx => by
        intro x qt hlookup
        exact hctx (by simpa using hlookup)),
        hctxAfterPc :=
      (fun {ctx} {_res} {_pc} hctx => by
        intro x qt hlookup
        exact ContextReachableFrom.ctxAfter hctx (by simpa using hlookup)),
        hctxNext :=
      (fun {ctx} {_nextLoc} {_nextTag} {_declared} hctx => by
        intro x qt hlookup
        exact hctx (by simpa using hlookup)),
        hctxVletBody :=
      (fun {ctx} {_vname} {e1} {fuel} {res1} {bodyCtx}
          hctx hcan1 htc1 hbodyEq => by
        have hqt : QTypReachableFrom root ctxRoot res1.qualType :=
          hqtypOfTypecheck hctx hcan1 htc1
        have hctxUpdate :
            ContextReachableFrom root ctxRoot
              { ctx with varEnv := VarTypeEnv.update ctx.varEnv _vname res1.qualType } :=
          ContextReachableFrom.update hctx hqt
        intro x qt hlookup
        exact hctxUpdate (by simpa [hbodyEq] using hlookup)),
        hctxFnBody :=
      (fun {ctx} {res} {e1} {e2} {_tcls} {_x} {_body} {_σcap}
          {_bodyCtx} {etyp2} {p2} {pred2}
          hctx hcanApp htyped hargQt hmem hbodyCtx => by
        have hqtFn : QTypReachableFrom root ctxRoot htyped.result1.qualType :=
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed
        have hqtArgRaw : QTypReachableFrom root ctxRoot htyped.result2.qualType :=
          hqtypOfTypecheck hctx
            (ExternDeclarationReachableFromExpr.app_arg hcanApp)
            htyped.arg_typed
        have hqtArg :
            QTypReachableFrom root ctxRoot
              { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } :=
          QTypReachableFrom.of_eq_redecorate hqtArgRaw hargQt
        intro y qt hlookup
        exact
          ContextReachableFrom.fnBody_of_arrow_member
            hqtFn htyped.result_arrow hmem hqtArg hbodyCtx hlookup),
        hctxPfnBody :=
      (fun {ctx} {res} {e1} {e2} {_tcls} {_x} {_pbody} {_σcap}
          {_bodyCtx} {etyp2} {p2} {pred2}
          hctx hcanApp htyped hargQt hmem hbodyCtx => by
        have hqtPfn : QTypReachableFrom root ctxRoot htyped.result1.qualType :=
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed
        have hqtArgRaw : QTypReachableFrom root ctxRoot htyped.result2.qualType :=
          hqtypOfTypecheck hctx
            (ExternDeclarationReachableFromExpr.app_arg hcanApp)
            htyped.arg_typed
        have hqtArg :
            QTypReachableFrom root ctxRoot
              { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } :=
          QTypReachableFrom.of_eq_redecorate hqtArgRaw hargQt
        intro y qt hlookup
        exact
          ContextReachableFrom.pfnBody_of_parrow_member
            hqtPfn htyped.result_parrow hmem hqtArg hbodyCtx hlookup),
        hcanFnBody :=
      (fun {ctx} {e1} {e2} {_res} {_tcls} {_x} {_body} {_σcap}
          hctx hcanApp htyped hmem =>
        AppFnClosureListFromTypecheck.regularBody_reachable
          htyped
          (hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)
          hmem),
        hcanPfnBody :=
      (fun {ctx} {e1} {e2} {_res} {_tcls} {_x} {_pbody} {_σcap}
          hctx hcanApp htyped hmem =>
        AppPfnClosureListFromTypecheck.regularBody_reachable
          htyped
          (hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)
          hmem),
        hdeclSingle :=
      (fun {e} {id} {d} {masked} {ctx} {res} {predSat} {tm} {impl}
          hcan hprog =>
        have hreachable :
            ExternDeclarationReachableFromContext root ctxRoot d.id d := by
          have hdid : d.id = id := ExternDeclarationInProgram.id_eq hprog
          simpa [hdid] using hcan hprog
        ExternDeclBoundarySingleMaskedContract.of_trustedReachable
          (tr := tr) (root := root) (ctxRoot := ctxRoot)
          (masked := masked) (postExpr := e) (ctx := ctx) (res := res)
          (predSat := predSat) (tm := tm) (d := d) (impl := impl)
          hagrees hreachable),
        hentryKey_unique :=
      (by
        intro _id _entry₀ _entry₁ h₀ h₁
        exact ExternCallTrustedEntryKey_eq_of_same_id h₀ h₁),
        hcallFR_of_entryKey :=
      (by
        intro _id entry _hkey
        exact entry.spec.callFR),
        hfnLocal :=
      (ExternCallFRFnLocalProviderReachableCtx_of_reachable hagrees
        (fun {ctx} {e1} {e2} {_res} {_tcls} hctx hcanApp htyped =>
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)),
        hpfnLocal :=
      (ExternCallFRPfnLocalProviderReachableCtx_of_reachable hagrees
        (fun {ctx} {e1} {e2} {_res} {_tcls} hctx hcanApp htyped =>
          hqtypOfTypecheck
            (ContextReachableFrom.ctxAfter hctx)
            (ExternDeclarationReachableFromExpr.app_fun hcanApp)
            htyped.fn_typed)),
        hdeclFR :=
      (fun {e} {id} {d} {ctx} {postExpr} {res} {predSat} {tm} {impl₀} {impl₁}
          hcan hprog =>
        have hreachable :
            ExternDeclarationReachableFromContext root ctxRoot d.id d := by
          have hdid : d.id = id := ExternDeclarationInProgram.id_eq hprog
          simpa [hdid] using hcan hprog
        ExternDeclBoundaryFRContract.of_trustedReachable
          (tr := tr) (root := root) (ctxRoot := ctxRoot)
          (ctx := ctx) (postExpr := postExpr) (res := res) (predSat := predSat)
          (tm := tm) (d := d) (impl₀ := impl₀) (impl₁ := impl₁)
          hagrees hreachable)
      }
      current ctxᵢ predSat tm
      hctxStart hcurrent

-- Bridge from a registry-parametric step theorem for one expression to the
-- per-context fault-robustness specification at a fixed initial context.
private theorem faultRobustnessSpecForCtx_of_step
  (registry : ExternRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
  (ctx : TypeContext)
  (_hOp : RegistryOperationalSafe registry)
  (hstepctx : ctxMatchesInputSpec s ctx → ∀ predSat tm,
      TypeSystemEnforcesFaultRobustness_step_spec e ctx predSat tm
        (registry := registry)) :
  FaultRobustnessSpecForCtx registry e s obs ctx := by
  rintro his _hos hctx hwf _hpc hte hdeclEmpty htagBoundedInit predSat tm hwfTm hTmBounded
    hps hExtTyping ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstepctx hctx predSat tm
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hWfRegime hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hres₁ hres₂ hrdInit₁ hrdInit₂ hics₁ hics₂ hric₁ hric₂ htrustedInit₁ htrustedInit₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
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
  have htagBounded : TagBoundedCtx ctx := htagBoundedInit
  have hstep_fr :=
    hstep' hps hExtTyping hwfTm hTmBounded μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ hwf htagBounded hric₁ hric₂ hreg hcwr₁ hcwr₂ hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ hres₁ hres₂ hrdInit₁ hrdInit₂ ht₁ ht₂
  -- StepFR result structure: ∃ θ₁' θ₂', wfExtendsMap ∧ wfExtendsMap ∧ valueHasETyp ∧ valueHasETyp ∧
  --   wfTagMeaningCtx ∧ wfTypeContext ∧ TagBoundedCtx ∧ wfConfig ∧ wfConfig ∧ ... ∧ agreeOnClean ∧ resultAgreesIfClean
  rcases hstep_fr with ⟨_tm', _hcanon, _hpredlaws', _hresTm, hstep_fr⟩
  rcases hstep_fr with ⟨θ₁', θ₂', hwfext₁, hwfext₂, _hvtyp₁, _hvtyp₂, _hTm',
    _hwfctx', _htagBounded', _hwfcfg₁', _hwfcfg₂', _hric₁', _hric₂', _hreg',
    _hcwr₁', _hcwr₂', hagree_clean', _hval_consist₁, _hval_consist₂,
    hret_agree, _hrd₁', _hrd₂'⟩
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
          | clean_internal_arrow _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isArrow = true implies function type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisArrow) (by decide)
          | clean_internal_parrow _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ _ _ hv1 _ =>
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
            | clean_internal_arrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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
            | clean_internal_parrow_extern _ hetyp _ _ _ _ _ _ _ _ _ =>
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

-- Recover the registry-parametric (all-context) specification from the
-- per-context core: instantiate at every context and feed the per-context step
-- hypothesis from the universal one.
private theorem faultRobustnessSpec_of_step
  (registry : ExternRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
  (hOp : RegistryOperationalSafe registry) :
  (∀ ctxᵢ, ctxMatchesInputSpec s ctxᵢ → ∀ predSat tm,
      TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat tm
        (registry := registry)) →
  FaultRobustnessSpecForRegistry registry e s obs := by
  intro hstep ctx
  exact
    faultRobustnessSpecForCtx_of_step registry e s obs ctx hOp
      (fun hctx => hstep ctx hctx)

-- Per-context trusted-registry fault-robustness theorem.  Registry agreement is
-- required only for the actual initial context `ctx`, not every adversarial
-- extension of it.  The operational safety predicate is derived internally from
-- the trusted registry via `TrustedRegistry.operationalSafe`.
theorem TypeSystemEnforcesFaultRobustness_at
  (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
  (ctx : TypeContext)
  (hagrees : TrustedRegistryAgreesWithReachable e ctx tr) :
  FaultRobustnessSpecForCtx (TrustedRegistry.toRuntimeRegistry tr) e s obs ctx :=
  let hOp := TrustedRegistry.operationalSafe tr
  faultRobustnessSpecForCtx_of_step
    (TrustedRegistry.toRuntimeRegistry tr) e s obs ctx hOp
    (fun _hctx predSat tm =>
      TypeSystemEnforcesFaultRobustness_step_with_reachableCtx_canUse
        (tr := tr) (root := e) (current := e) (ctxRoot := ctx)
        hagrees
        (ExternDeclarationReachableFromExpr.root e ctx)
        ctx predSat tm hOp
        (ContextReachableFrom.refl e ctx))

-- All-context corollary under a universal agreement premise. The public theorem
-- uses per-context trust; callers that can supply universal agreement can use
-- this stronger wrapper. The premise is gated on `ctxMatchesInputSpec`, so it is
-- fed per-context inside `faultRobustnessSpec_of_step` where that hypothesis is
-- in scope.
theorem TypeSystemEnforcesFaultRobustness_allCtx
  (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
  (hagrees :
    ∀ {ctx : TypeContext},
      ctxMatchesInputSpec s ctx →
      TrustedRegistryAgreesWithReachable e ctx tr) :
  FaultRobustnessSpecForRegistry (TrustedRegistry.toRuntimeRegistry tr) e s obs :=
  let hOp := TrustedRegistry.operationalSafe tr
  faultRobustnessSpec_of_step
    (TrustedRegistry.toRuntimeRegistry tr) e s obs hOp
    (fun ctxᵢ hctx predSat tm =>
      TypeSystemEnforcesFaultRobustness_step_with_reachableCtx_canUse
        (tr := tr) (root := e) (current := e) (ctxRoot := ctxᵢ)
        (hagrees hctx)
        (ExternDeclarationReachableFromExpr.root e ctxᵢ)
        ctxᵢ predSat tm hOp
        (ContextReachableFrom.refl e ctxᵢ))

/-- The public trusted-registry-facing fault-robustness specification.  Registry
    trust is required per initial context (`InitialContextTrusted`), matching the
    real obligation rather than every adversarial extension of it.  The
    extern-regime domain bridge `ExternRegimeMatchesInputSpec` is threaded as part
    of the public contract (it is not consumed by the proof body — see its
    definition). -/
def FaultRobustnessSpec
    (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec) : Prop :=
  ∀ (ctx : TypeContext),
    ExternRegimeMatchesInputSpec s ctx →
    InitialContextTrusted tr e ctx →
    FaultRobustnessSpecForCtx (TrustedRegistry.toRuntimeRegistry tr) e s obs ctx

-- Main public fault-robustness theorem (trusted-registry-facing). Registry
-- agreement is required per initial context (`InitialContextTrusted`), so
-- concrete non-empty trusted registries can be used at the contexts where their
-- reachable extern declarations agree with the registry entries.
theorem TypeSystemEnforcesFaultRobustness
    (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpec tr e s obs := by
  intro ctx _hExternRegime hInitTrust
  exact TypeSystemEnforcesFaultRobustness_at tr e s obs ctx hInitTrust
