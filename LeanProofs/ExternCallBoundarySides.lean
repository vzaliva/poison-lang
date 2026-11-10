/-
  ExternCallBoundarySides.lean — parametrized extern-call boundary contracts.

  The Side / boundary-contract family for runtime extern dispatch. The module sits
  below `StepFRApp.lean` (which imports it) and above `StepFRClosureApply.lean` and
  `ExternBoundaryProofs.lean`. These contracts are PARAMETRIZED: they take the per-run
  results as hypotheses rather than referencing the application case proof, so the
  whole family is downward-closed.

  Contents: the `ExternCallBoundary{Fn,Pfn}StaticSource` provenance inductives and
  their navigation theorems, the `ExternCallBoundarySingle{Fn,Pfn}Contract` single-run
  contracts (+ `of_emptyExternRegistry`/`of_trustedRegistry`/`of_trustedProgram`/
  `of_trustedReachable`), the `ExternCallBoundaryFR{Fn,Pfn}{Run,Side0,Side1}` FR
  contracts/providers, the `ExternCall{No,Impossible,Trusted}EntryKey` discriminators,
  and `TrustedRegistryAgreesWithProgramLocal`.
-/

import LeanProofs.StepFR
import LeanProofs.StepFRClosureApply
import LeanProofs.ExternBoundaryProofs
import LeanProofs.JoinMemberTransport
import LeanProofs.VarEnvPreservation

open List
open List.Mem
open Std
open scoped MemoryTypeEnv


/-- Static provenance for a runtime impure extern dispatch from an arrow closure list.

A successful `externFn` call comes only from a static `FnTClosure.extern` member.
The regular-closure-with-bare-extern-body route is rejected at `typecheckFn` and
unreachable for well-typed values (the value relations carry
`¬ Expr.IsExternFnAst body`), mirroring the pure side (`ExternCallBoundaryPfnStaticSource`
below), whose regular bodies are restricted to `PExpr` and so exclude externs. -/
inductive ExternCallBoundaryFnStaticSource
    (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (id : ExternId) (x y : Name) (argTyp : Typ) (argPoison : Bool)
    (retSpec : ExternReturn) (eff : List Effect)
    (tenv : CapturedVarEnv)
    (memberCap : List Capture) : Prop where
  | externMember {declaredArgQt : QTyp} :
      argTyp = sourceArgTyp →
      declaredArgQt.poison = argPoison →
      FnTClosure.extern id x retSpec eff tenv declaredArgQt memberCap ∈ tcls →
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec eff tenv memberCap

/-- Static provenance for runtime pure extern dispatch from a parrow closure list.

Unlike impure extern dispatch, the pure closure invariant cannot use a regular
`Expr.externPfn` body: regular pure closures require `Expr.toPExpr? body = some ...`,
while extern declarations are not pure expressions. -/
inductive ExternCallBoundaryPfnStaticSource
    (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
    (id : ExternId) (x y : Name) (argTyp : Typ) (argPoison : Bool)
    (retSpec : ExternReturn)
    (tenv : CapturedVarEnv)
    (memberCap : List Capture) : Prop where
  | externMember {declaredArgQt : QTyp} :
      argTyp = sourceArgTyp →
      declaredArgQt.poison = argPoison →
      PFnTClosure.extern id x retSpec tenv declaredArgQt memberCap ∈ tcls →
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec tenv memberCap

lemma valueConsistentWithRegime_transport_normalizeAppResultByProvenance
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

lemma externBoundarySinglePost_of_singleRun_normalized_app
    {predSat : PredSat} {tm : TagMeaning}
    {bodyCtx : TypeContext} {body : Expr} {result3 first : TypeResult}
    {θ : RealizationMap} {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value}
    {registry : ExternRegistry} {a : Address} {pm : Bool}
    {hθwf : wfRealizationMap θ}
    {hwf : wfTypeContext bodyCtx}
    {hric : runtimeInstantiatesCtx bodyCtx μ ρ θ}
    {hreg : regimeConsistentWithCtx bodyCtx}
    {hcwr : consistentWithRegime predSat bodyCtx.regime bodyCtx μ ρ θ}
    {hwfcfg : wfConfig
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry }}
    {p p1 : Poison}
    (h_p1p : joinPoison p1 p = true)
    (hfirst_eq :
      first =
        { result3 with
          qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { result3.qualType with
                poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
          declared' := bodyCtx.declaredExternRefs })
    (hdecl3 : result3.declared' = bodyCtx.declaredExternRefs)
    (htag : StepFRSingleRunTagMeaningPost bodyCtx body result3 predSat tm)
    (hpost :
      StepFRSingleRunFinalCleanPcTruePost bodyCtx result3 predSat
        (registry := registry) μ ρ θ cf o hθwf hwf hric hreg hcwr a pm hwfcfg) :
    ExternBoundarySinglePost bodyCtx first predSat tm θ μ cf o := by
  rcases StepFRSingleRunTagMeaningPost.to_boundary htag with ⟨tm', htag_post⟩
  rcases htag_post with ⟨hext, hbounded, hwfCtx, hresTm, hpredlaws⟩
  rcases hpost with
    ⟨θ', hθext, hv, hric_final, hcwr_final, hval_final, hpres, hfresh, hrd⟩
  have hctxAfter_eq : ctxAfter bodyCtx first = ctxAfter bodyCtx result3 := by
    rw [hfirst_eq]
    simp [ctxAfter, hdecl3]
  have hfirst_memEnv : first.memEnv' = result3.memEnv' := by
    rw [hfirst_eq]
  have hfirst_regime : first.regime' = result3.regime' := by
    rw [hfirst_eq]
  have hfirst_etyp : first.qualType.etyp = result3.qualType.etyp := by
    rw [hfirst_eq]
    simp [normalizeAppResultByProvenance, h_p1p]
  have hfirst_no_guard : qtypGuardDesc? first.qualType = none := by
    rw [hfirst_eq]
    simp [normalizeAppResultByProvenance, h_p1p, qtypGuardDesc?]
  refine ⟨tm', ?_, θ', hθext, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hext, ?_, ?_, ?_, hpredlaws⟩
    · simpa [hfirst_eq, normalizeAppResultByProvenance] using hbounded
    · simpa [hctxAfter_eq] using hwfCtx
    · exact
        QTypRespectsTagMeaning_transport_etyp_noGuard
          tm' result3.qualType first.qualType hresTm hfirst_etyp hfirst_no_guard
  · simpa [hfirst_etyp] using hv
  · simpa [hctxAfter_eq] using hric_final
  · simpa [hctxAfter_eq] using hcwr_final
  · have hval_norm :
        valueConsistentWithRegime predSat result3.regime'
          (normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with
              poison := joinPoison p1 (joinPoison p result3.qualType.poison) })
          cf.memory θ' o :=
      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
        predSat result3.regime' p p1 result3.qualType cf.memory θ' o hval_final
    simpa [hfirst_eq, hctxAfter_eq] using hval_norm
  · refine PreservesInheritedFinalCleanLocsOneRun.intro ?_
    intro l qt_in qt_out hlookup_in hlookup_out hclean
    exact
      PreservesInheritedFinalCleanLocsOneRun.apply hpres hlookup_in
        (by simpa [hfirst_memEnv] using hlookup_out)
        (by simpa [hfirst_regime] using hclean)
  · intro l qt hnot hlookup hclean
    exact hfresh l qt hnot
      (by simpa [hfirst_memEnv] using hlookup)
      (by simpa [hfirst_regime] using hclean)
  · simpa [hfirst_eq, hdecl3.symm] using hrd

theorem ExternCallBoundaryFnStaticSource.callBoundaryRun
    {tr : TrustedRegistry} {sourceArgTyp argTyp : Typ} {tcls : List FnTClosure}
    (hagreesExtern : TrustedRegistryAgreesWithFnTClosures tr sourceArgTyp tcls)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hstatic :
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
        capturedEnv memberCap)
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
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  cases hstatic with
  | externMember harg _ hmem =>
      cases harg
      exact
        TrustedRegistryAgreesWithFnTClosures.callBoundaryRun
          hagreesExtern hmem hargName hregistry hpure hunified hGet hArg hImpl hValRet hcfg

theorem ExternCallBoundaryFnStaticSource.callBoundaryRun_of_program
    {tr : TrustedRegistry} {root : Expr} {sourceArgTyp argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (_hstatic :
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
        capturedEnv memberCap)
    (hprog :
      ExternDeclarationInProgram root id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := memberCap })
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
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.fn implFn) := by
    rw [← hregistry]
    exact hGet
  rcases
    TrustedRegistryAgreesWithProgram.resolveFnDeclaration
      hagrees hprog hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects memberCap := by
    simpa [hargName] using hmatch
  have hlookupRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl :=
    TrustedRegistry.lookup_toRuntimeRegistry hlookup
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hlookupRuntime
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem ExternCallBoundaryFnStaticSource.reachable_from_qtyp
    {root : Expr} {ctxRoot : TypeContext} {sourceArgTyp st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow sourceArgTyp st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x y : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hsource :
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
        capturedEnv memberCap) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .fn, typ := argTyp, argName := some x,
        retSpec := some retSpec, effects := effects,
        preds := collectExternPreds retSpec effects, argPoison := argPoison,
        captures := memberCap } := by
  cases hsource with
  | externMember harg hpoison hmem =>
      cases harg
      cases hpoison
      exact QTypReachableFrom.fn_extern_member hqt hmem

theorem ExternCallBoundaryFnStaticSource.reachable_from_app_typecheck
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 : Expr}
    {res : TypeResult} {tcls : List FnTClosure}
    (htyped : AppFnClosureListFromTypecheck ctx e1 e2 res tcls)
    (hqt : QTypReachableFrom root ctxRoot htyped.result1.qualType)
    {id : ExternId} {x y : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hsource :
      ExternCallBoundaryFnStaticSource tcls htyped.st1 id x y argTyp argPoison retSpec effects
        capturedEnv memberCap) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .fn, typ := argTyp, argName := some x,
        retSpec := some retSpec, effects := effects,
        preds := collectExternPreds retSpec effects, argPoison := argPoison,
        captures := memberCap } := by
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
  exact ExternCallBoundaryFnStaticSource.reachable_from_qtyp hqtArrow hsource

theorem ExternCallBoundaryFnStaticSource.callBoundaryRun_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {sourceArgTyp argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (_hstatic :
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
        capturedEnv memberCap)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := memberCap })
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
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v :=
  TrustedRegistryAgreesWithReachable.callBoundaryRunFn
    hagrees hreachable hargName hregistry hpure hunified hGet hArg hImpl hValRet hcfg

theorem ExternCallBoundaryPfnStaticSource.callBoundaryRun
    {tr : TrustedRegistry} {sourceArgTyp argTyp : Typ} {tcls : List PFnTClosure}
    (hagreesExtern : TrustedRegistryAgreesWithPFnTClosures tr sourceArgTyp tcls)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hstatic :
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec capturedEnv memberCap)
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
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  cases hstatic with
  | externMember harg _ hmem =>
      cases harg
      exact
        TrustedRegistryAgreesWithPFnTClosures.callBoundaryRun
          hagreesExtern hmem hargName hregistry hunified hGet hArg hImpl hValRet hcfg

theorem ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_program
    {tr : TrustedRegistry} {root : Expr} {sourceArgTyp argTyp : Typ}
    {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (_hstatic :
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec capturedEnv memberCap)
    (hprog :
      ExternDeclarationInProgram root id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := memberCap })
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
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.pfn implFn) := by
    rw [← hregistry]
    exact hGet
  rcases
    TrustedRegistryAgreesWithProgram.resolvePfnDeclaration
      hagrees hprog hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec memberCap := by
    simpa [hargName] using hmatch
  have hlookupRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl :=
    TrustedRegistry.lookup_toRuntimeRegistry hlookup
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hlookupRuntime
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem ExternCallBoundaryPfnStaticSource.reachable_from_qtyp
    {root : Expr} {ctxRoot : TypeContext} {sourceArgTyp st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow sourceArgTyp st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x y : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hsource :
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec capturedEnv memberCap) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .pfn, typ := argTyp, argName := some x,
        retSpec := some retSpec, effects := [],
        preds := collectExternPreds retSpec [], argPoison := argPoison,
        captures := memberCap } := by
  cases hsource with
  | externMember harg hpoison hmem =>
      cases harg
      cases hpoison
      exact QTypReachableFrom.pfn_extern_member hqt hmem

theorem ExternCallBoundaryPfnStaticSource.reachable_from_app_typecheck
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 : Expr}
    {res : TypeResult} {tcls : List PFnTClosure}
    (htyped : AppPfnClosureListFromTypecheck ctx e1 e2 res tcls)
    (hqt : QTypReachableFrom root ctxRoot htyped.result1.qualType)
    {id : ExternId} {x y : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (hsource :
      ExternCallBoundaryPfnStaticSource tcls htyped.st1 id x y argTyp argPoison retSpec
        capturedEnv memberCap) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .pfn, typ := argTyp, argName := some x,
        retSpec := some retSpec, effects := [],
        preds := collectExternPreds retSpec [], argPoison := argPoison,
        captures := memberCap } := by
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
  exact ExternCallBoundaryPfnStaticSource.reachable_from_qtyp hqtParrow hsource

theorem ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_reachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {sourceArgTyp argTyp : Typ} {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x y : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {memberCap : List Capture}
    (_hstatic :
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec capturedEnv memberCap)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := memberCap })
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
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v :=
  TrustedRegistryAgreesWithReachable.callBoundaryRunPfn
    hagrees hreachable hargName hregistry hunified hGet hArg hImpl hValRet hcfg

/-- The trusted entry resolved for a pure extern call boundary carries the
    declared argument poison of the applied closure member.  This threads the
    `entry.decl.argPoison = argQt.poison` pin already established by the
    closure-list agreement `TrustedRegistryAgreesWithPFnTClosures` out to the
    typing-provider consumption sites, so the `Call.pfnExternMember` witness can
    pin `declaredArgQt.poison = d.argPoison`. -/
private lemma pfnStaticSource_entry_argPoison
    {tr : TrustedRegistry} {sourceArgTyp argTyp agreeArgTyp : Typ} {tcls : List PFnTClosure}
    {id : ExternId} {x y : Name} {declaredArgPoison : Bool} {retSpec : ExternReturn}
    {tenv : CapturedVarEnv} {memberCap : List Capture} {entry : TrustedExternEntry}
    (hagrees : TrustedRegistryAgreesWithPFnTClosures tr agreeArgTyp tcls)
    (hstatic :
      ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec tenv memberCap)
    (hlookup : TrustedRegistry.lookup? tr id = some entry) :
    entry.decl.argPoison = declaredArgPoison := by
  cases hstatic with
  | externMember _harg hpoison hmem =>
      obtain ⟨entry', hlookup', _hmatch', hpoison'⟩ := hagrees hmem
      have hentry : entry' = entry := Option.some.inj (hlookup'.symm.trans hlookup)
      subst hentry
      exact hpoison'.trans hpoison

/-- Impure-extern mirror of `pfnStaticSource_entry_argPoison`: the trusted entry
    resolved for an impure extern call boundary carries the declared argument
    poison of the applied closure member, via the `entry.decl.argPoison =
    argQt.poison` pin from the closure-list agreement `TrustedRegistryAgreesWithFnTClosures`. -/
private lemma fnStaticSource_entry_argPoison
    {tr : TrustedRegistry} {sourceArgTyp argTyp agreeArgTyp : Typ} {tcls : List FnTClosure}
    {id : ExternId} {x y : Name} {declaredArgPoison : Bool} {retSpec : ExternReturn}
    {effects : List Effect} {tenv : CapturedVarEnv} {memberCap : List Capture}
    {entry : TrustedExternEntry}
    (hagrees : TrustedRegistryAgreesWithFnTClosures tr agreeArgTyp tcls)
    (hstatic :
      ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec effects tenv
        memberCap)
    (hlookup : TrustedRegistry.lookup? tr id = some entry) :
    entry.decl.argPoison = declaredArgPoison := by
  cases hstatic with
  | externMember _harg hpoison hmem =>
      obtain ⟨entry', hlookup', _hmatch', hpoison'⟩ := hagrees hmem
      have hentry : entry' = entry := Option.some.inj (hlookup'.symm.trans hlookup)
      subst hentry
      exact hpoison'.trans hpoison

def ExternCallFnTypingProvider
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect)
    (callEntry : ExternCallEntry) (res : TypeResult)
    (declaredArgPoison : Bool) (memberCap : List Capture) : Prop :=
  ∀ entry,
    TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects memberCap →
    entry.decl.argPoison = declaredArgPoison →
    ∃ argPoisonAst argPredAst captures,
      ExternBoundaryTyping.Call entry.decl
        (Expr.externFn id y argTyp argPoisonAst argPredAst retSpec effects captures) callEntry res

def ExternCallPfnTypingProvider
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (retSpec : ExternReturn)
    (callEntry : ExternCallEntry) (res : TypeResult)
    (declaredArgPoison : Bool) (memberCap : List Capture) : Prop :=
  ∀ entry,
    TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap →
    entry.decl.argPoison = declaredArgPoison →
    ∃ argPoisonAst argPredAst captures,
      ExternBoundaryTyping.Call entry.decl
        (Expr.externPfn id y argTyp argPoisonAst argPredAst retSpec captures) callEntry res

private theorem externCallBoundaryRun_singlePost
    {entry : TrustedExternEntry} {typedExpr : Expr} {result3 : TypeResult}
    {predSatBody : PredSat} {tmBody : TagMeaning}
    {θBody : RealizationMap} {callEntry : ExternCallEntry}
    {cf : Config} {o : Value}
    (htypedCall : ExternBoundaryTyping.Call entry.decl typedExpr callEntry result3)
    (hpredlawsBody : PredSatLaws predSatBody tmBody)
    (hwfTmBody : wfTagMeaningCtx tmBody callEntry.bodyCtx)
    (hTmBoundedBody : TagMeaningBounded tmBody callEntry.bodyCtx.nextTag)
    (hθBodyWf : wfRealizationMap θBody)
    (hwfBody : wfTypeContext callEntry.bodyCtx)
    (hricBody :
      runtimeInstantiatesCtx callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (htagRBody : regimeConsistentWithCtx callEntry.bodyCtx)
    (hcwrBody :
      consistentWithRegime predSatBody callEntry.bodyCtx.regime callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (hwfcfgBody : wfConfig callEntry.bodyConfig)
    (hrdBody : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody)
    (hrun : ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o)
    (hpcBody : callEntry.bodyCtx.pc = true) :
    ExternBoundarySinglePost callEntry.bodyCtx result3 predSatBody tmBody
      θBody callEntry.bodyConfig.memory (callEntry.bodyOutputConfig cf) o :=
  entry.spec.callSingle typedExpr result3 predSatBody tmBody callEntry
    htypedCall hpredlawsBody hwfTmBody hTmBoundedBody θBody cf o
    hθBodyWf hwfBody hricBody htagRBody hcwrBody hwfcfgBody hrdBody hrun hpcBody

/-- Body-local single-run contract for successful impure extern app dispatch.

    The contract deliberately returns an `ExternBoundarySinglePost` for the
    selected body/member result instead of the final surrounding `Expr.app`
    post.  App-specific transport from this body post to the outer app post is
    owned by the shared app helpers. -/
def ExternCallBoundarySingleFnContract
    (masked : Tag → Prop)
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (_ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (ctxᵢ : TypeContext) (_res : TypeResult)
    (e1 e2 : Expr)
    (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
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
    (_hrdBody : ReservedDiscipline callEntry.bodyConfig.registry bodyCtx.declaredExternRefs θBody)
    (_hpcBody : bodyCtx.pc = true)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (argPoison declaredArgPoison : Bool) (argPred : SyntaxPredicate) (retSpec : ExternReturn)
    (eff : List Effect) (tenv : CapturedVarEnv) (memberCap cap : List Capture) (env : VarEnv)
    (impl : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address))
    (vRaw : Value) (mem' : Memory) (addr' : Address),
    ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec eff tenv memberCap →
    ExternCallFnTypingProvider id x y argTyp retSpec eff callEntry result3 declaredArgPoison memberCap →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec eff cap) env) →
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
theorem ExternCallBoundarySingleFnContract.of_emptyExternRegistry
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ} :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      sourceArgTyp := by
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        _hpredlawsBody _hwfTmBody _hTmBoundedBody _hθBodyWf _hwfBody _hricBody
        _htagRBody _hcwrBody _hwfcfgBody _hrdBody _hpcBody
        c₂' v₂ c₁ id x y argTyp _argPoison _declaredArgPoison _argPred retSpec eff _tenv _memberCap _cap _env
        _impl _vRaw _mem' _addr' _hstatic _htypedCall ht_e2 ht_e1 _hpure hGet _hArg _hImpl
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

theorem ExternCallBoundarySingleFnContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls) :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec eff tenv memberCap cap env impl vRaw mem' addr'
        hstatic htypedCallProvider ht_e2 ht_e1 hpure hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
      (tr := tr) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp)
      (argPoison := declaredArgPoison) (tcls := tcls)
      (hagreesExtern (argTyp := sourceArgTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (effects := eff) (capturedEnv := tenv) (memberCap := memberCap)
      hstatic hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    fnStaticSource_entry_argPoison (hagreesExtern (argTyp := sourceArgTyp))
      hstatic _hlookup
  obtain ⟨_apaFn, _aprFn, _capFn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

theorem ExternCallBoundarySingleFnContract.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec eff tenv memberCap cap env impl vRaw mem' addr'
        hstatic htypedCallProvider ht_e2 ht_e1 hpure hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
    ExternCallBoundaryFnStaticSource.callBoundaryRun_of_program
      (tr := tr) (root := root) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp)
      (tcls := tcls)
      hagrees hstatic (hsourceProgram hstatic)
      hargName hregistryCall hpureCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceProgram hstatic) _hlookup)
  obtain ⟨_apaFn, _aprFn, _capFn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

theorem ExternCallBoundarySingleFnContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundarySingleFnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec eff tenv memberCap cap env impl vRaw mem' addr'
        hstatic htypedCallProvider ht_e2 ht_e1 hpure hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
    ExternCallBoundaryFnStaticSource.callBoundaryRun_of_reachable
      (tr := tr) (root := root) (ctxRoot := ctxRoot)
      (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      hagrees hstatic (hsourceReachable hstatic)
      hargName hregistryCall hpureCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceReachable hstatic) _hlookup)
  obtain ⟨_apaFn, _aprFn, _capFn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

/-- Body-local single-run contract for successful pure extern app dispatch. -/
def ExternCallBoundarySinglePfnContract
    (masked : Tag → Prop)
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (_ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (ctxᵢ : TypeContext) (_res : TypeResult)
    (e1 e2 : Expr)
    (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
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
    (_hrdBody : ReservedDiscipline callEntry.bodyConfig.registry bodyCtx.declaredExternRefs θBody)
    (_hpcBody : bodyCtx.pc = true)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (argPoison declaredArgPoison : Bool) (argPred : SyntaxPredicate) (retSpec : ExternReturn)
    (tenv : CapturedVarEnv) (memberCap cap : List Capture) (env : VarEnv)
    (impl : VarEnv → Value → Memory → Except ExternError Value)
    (vRaw : Value),
    ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec tenv memberCap →
    ExternCallPfnTypingProvider id x y argTyp retSpec callEntry result3 declaredArgPoison memberCap →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec cap) env) →
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

theorem ExternCallBoundarySinglePfnContract.of_emptyExternRegistry
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ} :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      sourceArgTyp := by
  intro μ ρ θ cf o hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        _hpredlawsBody _hwfTmBody _hTmBoundedBody _hθBodyWf _hwfBody _hricBody
        _htagRBody _hcwrBody _hwfcfgBody _hrdBody _hpcBody
        c₂' v₂ c₁ id x y argTyp _argPoison _declaredArgPoison _argPred retSpec _tenv _memberCap _cap _env _impl _vRaw
        _hstatic _htypedCall ht_e2 ht_e1 hGet _hArg _hImpl _hValRet _hcf
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg2' : c₂'.registry = emptyExternRegistry :=
    terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht_e1).trans hreg2'
  rw [hreg_c₁] at hGet
  simp [emptyExternRegistry] at hGet

theorem ExternCallBoundarySinglePfnContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec tenv memberCap cap env impl vRaw
        hstatic htypedCallProvider ht_e2 ht_e1 hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
      (tr := tr) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      (hagreesExtern (argTyp := sourceArgTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (capturedEnv := tenv)
      hstatic hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    pfnStaticSource_entry_argPoison (hagreesExtern (argTyp := sourceArgTyp)) hstatic _hlookup
  obtain ⟨_apaPfn, _aprPfn, _capPfn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

theorem ExternCallBoundarySinglePfnContract.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec tenv memberCap cap env impl vRaw
        hstatic htypedCallProvider ht_e2 ht_e1 hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
    ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_program
      (tr := tr) (root := root) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp)
      (tcls := tcls)
      hagrees hstatic (hsourceProgram hstatic)
      hargName hregistryCall hunified hGetCall hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceProgram hstatic) _hlookup)
  obtain ⟨_apaPfn, _aprPfn, _capPfn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

theorem ExternCallBoundarySinglePfnContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {masked : Tag → Prop}
    {CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop}
    {ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop}
    {ctxᵢ : TypeContext} {res : TypeResult}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundarySinglePfnContract masked CtxCons ValCons ctxᵢ res e1 e2 tcls
      sourceArgTyp
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro μ ρ θ cf o _hθwf _hwf _hric _hreg _hmasked_none _hctxCons a pm _hwfcfg
        bodyCtx result3 predSatBody tmBody θBody callEntry
        hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
        htagRBody hcwrBody hwfcfgBody hrdBody hpcBody
        c₂' v₂ c₁ id x y argTyp argPoison declaredArgPoison argPred retSpec tenv memberCap cap env impl vRaw
        hstatic htypedCallProvider ht_e2 ht_e1 hGet hArg hImpl hValRet hcf hbodyCtx hcallCfg
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
    ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_reachable
      (tr := tr) (root := root) (ctxRoot := ctxRoot)
      (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      hagrees hstatic (hsourceReachable hstatic)
      hargName hregistryCall hunified hGetCall hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceReachable hstatic) _hlookup)
  obtain ⟨_apaPfn, _aprPfn, _capPfn, htypedEntryCall⟩ := htypedCallProvider entry hmatch hentryPoison
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
  have hrdCall : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody := by
    simpa [hbodyCtx] using hrdBody
  simpa [hbodyCtx] using
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedEntryCall hpredlawsBody hwfTmCall hTmBoundedCall hθBodyWf hwfCall hricCall
      htagRCall hcwrCall hwfcfgBody hrdCall hrun hpcCall

/-- Keying evidence attached to a trusted extern entry returned by a local
    two-run app-call provider.  The empty-registry instance uses
    `ExternCallNoEntryKey`; populated trusted registries use
    `ExternCallTrustedEntryKey tr`, which lets the two sides prove they found
    the same trusted entry for the same extern id. -/
def ExternCallEntryKey : Type :=
  ExternId → TrustedExternEntry → Prop

def ExternCallNoEntryKey : ExternCallEntryKey :=
  fun _ _ => True

def ExternCallImpossibleEntryKey : ExternCallEntryKey :=
  fun _ _ => False

def ExternCallTrustedEntryKey (tr : TrustedRegistry) : ExternCallEntryKey :=
  fun id entry => TrustedRegistry.lookup? tr id = some entry

theorem ExternCallTrustedEntryKey_eq_of_same_id
    {tr : TrustedRegistry} {id : ExternId} {entry₀ entry₁ : TrustedExternEntry}
    (h₀ : ExternCallTrustedEntryKey tr id entry₀)
    (h₁ : ExternCallTrustedEntryKey tr id entry₁) :
    entry₀ = entry₁ :=
  Option.some.inj (h₀.symm.trans h₁)

theorem externCallBoundaryRunProvider_singlePost
    {entryKey : ExternCallEntryKey} {id : ExternId} {typedExpr : Expr}
    {result3 : TypeResult}
    {predSatBody : PredSat} {tmBody : TagMeaning}
    {θBody : RealizationMap} {callEntry : ExternCallEntry}
    {cf : Config} {o : Value}
    (hrunProvider :
      ∃ entry : TrustedExternEntry,
        entryKey id entry ∧
        ExternBoundaryTyping.Call entry.decl typedExpr callEntry result3 ∧
        ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o)
    (hpredlawsBody : PredSatLaws predSatBody tmBody)
    (hwfTmBody : wfTagMeaningCtx tmBody callEntry.bodyCtx)
    (hTmBoundedBody : TagMeaningBounded tmBody callEntry.bodyCtx.nextTag)
    (hθBodyWf : wfRealizationMap θBody)
    (hwfBody : wfTypeContext callEntry.bodyCtx)
    (hricBody :
      runtimeInstantiatesCtx callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (htagRBody : regimeConsistentWithCtx callEntry.bodyCtx)
    (hcwrBody :
      consistentWithRegime predSatBody callEntry.bodyCtx.regime callEntry.bodyCtx
        callEntry.bodyConfig.memory callEntry.bodyConfig.varEnv θBody)
    (hwfcfgBody : wfConfig callEntry.bodyConfig)
    (hrdBody : ReservedDiscipline callEntry.bodyConfig.registry callEntry.bodyCtx.declaredExternRefs θBody)
    (hpcBody : callEntry.bodyCtx.pc = true) :
    ExternBoundarySinglePost callEntry.bodyCtx result3 predSatBody tmBody
      θBody callEntry.bodyConfig.memory (callEntry.bodyOutputConfig cf) o := by
  rcases hrunProvider with ⟨entry, _hkey, htypedCall, hrun⟩
  exact
    externCallBoundaryRun_singlePost
      (entry := entry) (result3 := result3) (predSatBody := predSatBody)
      (tmBody := tmBody) (θBody := θBody) (callEntry := callEntry)
      (cf := cf) (o := o)
      htypedCall hpredlawsBody hwfTmBody hTmBoundedBody hθBodyWf hwfBody hricBody
      htagRBody hcwrBody hwfcfgBody hrdBody hrun hpcBody

/-- Single-run "tail" of the impure (`fn`) extern-call boundary contract.

    Both `Side0`/`Side1` two-run contracts share this tail verbatim, differing
    only in which run's `(μ ρ cf o a)` they project into it; factoring it here
    lets the four `of_*` discharge proofs be written once (run-generic) instead
    of mirrored across the two sides.  Each `SideKContract` is *definitionally*
    `∀ <two-run preamble>, RunContract … <runK projection>`. -/
private def ExternCallBoundaryFRFnRunContract
    (e1 e2 : Expr) (tcls : List FnTClosure) (sourceArgTyp : Typ)
    (μ : Memory) (ρ : VarEnv) (cf : Config) (o : Value) (a : Address) (pm : Bool)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (argPoison declaredArgPoison : Bool) (argPred : SyntaxPredicate) (retSpec : ExternReturn)
    (eff : List Effect) (tenv : CapturedVarEnv) (memberCap cap : List Capture) (env : VarEnv)
    (impl : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address))
    (vRaw : Value) (mem' : Memory) (addr' : Address),
    ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec
      eff tenv memberCap →
    ExternCallFnTypingProvider id x y argTyp retSpec eff callEntry result3 declaredArgPoison memberCap →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec eff cap) env) →
    c₁.pureMode = false →
    c₁.registry.get? id = some (ExternImpl.fn impl) →
    valueMatchesTyp v₂ argTyp = true →
    impl (VarEnv.update env x v₂) v₂ c₁.memory c₁.nextAddr =
      Except.ok (vRaw, mem', addr') →
    validateExternReturn id retSpec vRaw = Except.ok o →
    (cf =
      { memory := mem', varEnv := c₁.varEnv, nextAddr := addr',
        pureMode := c₁.pureMode, registry := c₁.registry }) →
    callEntry.bodyCtx = bodyCtx →
    callEntry.callConfig = c₁ →
    callEntry.argName = x →
    callEntry.argValue = v₂ →
    callEntry.capturedEnv = env →
    callEntry.unifiedEnv =
      VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue →
    ∃ entry : TrustedExternEntry,
      entryKey id entry ∧
      (∃ argPoisonAst argPredAst captures, ExternBoundaryTyping.Call entry.decl
        (Expr.externFn id y argTyp argPoisonAst argPredAst retSpec eff captures) callEntry result3) ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o

/-- Populated trusted-registry discharge for the single-run `fn` boundary tail. -/
private theorem ExternCallBoundaryFRFnRunContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec eff
        tenv memberCap cap env impl vRaw mem' addr' hstatic
        htypedCall ht_e2 ht_e1 hpure hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun
      (tr := tr) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      (hagreesExtern (argTyp := sourceArgTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (effects := eff) (capturedEnv := tenv) (memberCap := memberCap)
      hstatic hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch
        (fnStaticSource_entry_argPoison (hagreesExtern (argTyp := sourceArgTyp))
          hstatic _hlookup), hrun⟩

/-- Empty-registry discharge for the single-run `fn` boundary tail: an extern
    call against the empty registry cannot look up an implementation. -/
private theorem ExternCallBoundaryFRFnRunContract.of_emptyExternRegistry
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := entryKey) := by
  intro _bodyCtx _result3 _callEntry
        c₂' v₂ c₁ id x y argTyp _argPoison _declaredArgPoison _argPred retSpec eff
        _tenv _memberCap _cap _env _impl _vRaw _mem' _addr' _hstatic
        _htypedCall ht_e2 ht_e1 _hpure hGet _hArg _hImpl _hValRet _heq_cfg
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂' : c₂'.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht_e1).trans hreg_c₂'
  rw [hreg_c₁] at hGet
  simp [emptyExternRegistry] at hGet

/-- Program-level discharge for the single-run `fn` boundary tail. -/
private theorem ExternCallBoundaryFRFnRunContract.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec eff
        tenv memberCap cap env impl vRaw mem' addr' hstatic
        htypedCall ht_e2 ht_e1 hpure hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun_of_program
      (tr := tr) (root := root) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp)
      (tcls := tcls)
      hagrees hstatic (hsourceProgram hstatic)
      hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch
        (congrArg ExternDeclaration.argPoison (hagrees (hsourceProgram hstatic) _hlookup)), hrun⟩

/-- Reachable-declaration discharge for the single-run `fn` boundary tail. -/
private theorem ExternCallBoundaryFRFnRunContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {e1 e2 : Expr} {tcls : List FnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec eff
        tenv memberCap cap env impl vRaw mem' addr' hstatic
        htypedCall ht_e2 ht_e1 hpure hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryFnStaticSource.callBoundaryRun_of_reachable
      (tr := tr) (root := root) (ctxRoot := ctxRoot)
      (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      hagrees hstatic (hsourceReachable hstatic)
      hargName hregistryCall hpureCall hunified hGetCall
      hArgCall hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch
        (congrArg ExternDeclaration.argPoison (hagrees (hsourceReachable hstatic) _hlookup)), hrun⟩

/-- Body-local boundary-run contract for the side-0 impure extern arm. -/
private def ExternCallBoundaryFRFnSide0Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
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
        registry := registry } cf₁ o₁),
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ₀ ρ₀ cf₀ o₀ a₀ pm
      (entryKey := entryKey) (registry := registry)

/-- Provider-shaped adapter for the registry lookup: a static source of the
    arrow closure list produces the side-0 boundary contract.  The empty-registry
    variant discharges the key vacuously; the populated trusted-registry variants
    below use `FnTClosure.extern` membership to look up the matching per-id
    boundary spec. -/
private def ExternCallBoundaryFRFnSide0Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₀ : ExternId} {x₀ y₀ : Name} {argTyp₀ : Typ} {argPoison₀ : Bool}
    {retSpec₀ : ExternReturn} {eff₀ : List Effect}
    {tenv₀ : CapturedVarEnv} {memberCap₀ : List Capture},
    ExternCallBoundaryFnStaticSource tcls sourceArgTyp id₀ x₀ y₀ argTyp₀ argPoison₀ retSpec₀
      eff₀ tenv₀ memberCap₀ →
    ExternCallBoundaryFRFnSide0Contract ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) (registry := registry)

/-- Empty-registry provider: any static extern member maps to the vacuous
    side-0 boundary contract. -/
private theorem ExternCallBoundaryFRFnSide0Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _eff₀ _tenv₀ _memberCap₀ _hstatic
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_emptyExternRegistry (entryKey := entryKey)

private theorem ExternCallBoundaryFRFnSide0Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _eff₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedRegistry hagreesExtern

/-- Body-local boundary-run contract for the side-1 impure extern arm. -/
private def ExternCallBoundaryFRFnSide1Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
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
        registry := registry } cf₁ o₁),
    ExternCallBoundaryFRFnRunContract e1 e2 tcls sourceArgTyp μ₁ ρ₁ cf₁ o₁ a₁ pm
      (entryKey := entryKey) (registry := registry)

/-- Provider-shaped adapter for side 1, mirroring
    `ExternCallBoundaryFRFnSide0Provider`. -/
private def ExternCallBoundaryFRFnSide1Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₁ : ExternId} {x₁ y₁ : Name} {argTyp₁ : Typ} {argPoison₁ : Bool}
    {retSpec₁ : ExternReturn} {eff₁ : List Effect}
    {tenv₁ : CapturedVarEnv} {memberCap₁ : List Capture},
    ExternCallBoundaryFnStaticSource tcls sourceArgTyp id₁ x₁ y₁ argTyp₁ argPoison₁ retSpec₁
      eff₁ tenv₁ memberCap₁ →
    ExternCallBoundaryFRFnSide1Contract ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) (registry := registry)

/-- Empty-registry provider: any static extern member maps to the vacuous
    side-1 boundary contract. -/
private theorem ExternCallBoundaryFRFnSide1Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _eff₁ _tenv₁ _memberCap₁ _hstatic
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_emptyExternRegistry (entryKey := entryKey)

private theorem ExternCallBoundaryFRFnSide1Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _eff₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedRegistry hagreesExtern

private theorem ExternCallBoundaryFRFnSide0Provider.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _eff₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedProgram hagrees hsourceProgram

private theorem ExternCallBoundaryFRFnSide1Provider.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _eff₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedProgram hagrees hsourceProgram

private theorem ExternCallBoundaryFRFnSide0Provider.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _eff₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedReachable hagrees hsourceReachable

private theorem ExternCallBoundaryFRFnSide1Provider.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _eff₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRFnRunContract.of_trustedReachable hagrees hsourceReachable

/-- Run-generic single-run `pfn` boundary tail shared by both side-0/side-1
    two-run contracts.

    The pure-extern analogue of `ExternCallBoundaryFRFnRunContract`: no effects,
    a pure `impl` (no address threading), and `cf = c₁` rather than a record
    update.  Each `PfnSideKContract` is *definitionally*
    `∀ <two-run preamble>, RunContract … <runK projection>`, so the four `of_*`
    discharge proofs below are written once instead of mirrored across sides. -/
private def ExternCallBoundaryFRPfnRunContract
    (e1 e2 : Expr) (tcls : List PFnTClosure) (sourceArgTyp : Typ)
    (μ : Memory) (ρ : VarEnv) (cf : Config) (o : Value) (a : Address) (pm : Bool)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ (bodyCtx : TypeContext) (result3 : TypeResult) (callEntry : ExternCallEntry)
    (c₂' : Config) (v₂ : Value) (c₁ : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ)
    (argPoison declaredArgPoison : Bool) (argPred : SyntaxPredicate) (retSpec : ExternReturn)
    (tenv : CapturedVarEnv) (memberCap captures : List Capture) (env : VarEnv)
    (impl : VarEnv → Value → Memory → Except ExternError Value)
    (vRaw : Value),
    ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp declaredArgPoison retSpec
      tenv memberCap →
    ExternCallPfnTypingProvider id x y argTyp retSpec callEntry result3 declaredArgPoison memberCap →
    terminatesTo e2
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
        registry := registry } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec captures) env) →
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
    ∃ entry : TrustedExternEntry,
      entryKey id entry ∧
      (∃ argPoisonAst argPredAst captures, ExternBoundaryTyping.Call entry.decl
        (Expr.externPfn id y argTyp argPoisonAst argPredAst retSpec captures) callEntry result3) ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry result3 cf o

/-- Populated trusted-registry discharge for the single-run `pfn` boundary tail. -/
private theorem ExternCallBoundaryFRPfnRunContract.of_trustedRegistry
    {tr : TrustedRegistry}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec
        tenv memberCap captures env impl vRaw hstatic htypedCall ht_e2 ht_e1
        hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun
      (tr := tr) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      (hagreesExtern (argTyp := sourceArgTyp))
      (id := id) (x := x) (y := y) (retSpec := retSpec)
      (capturedEnv := tenv)
      hstatic hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    pfnStaticSource_entry_argPoison (hagreesExtern (argTyp := sourceArgTyp)) hstatic _hlookup
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch hentryPoison, hrun⟩

/-- Empty-registry discharge for the single-run `pfn` boundary tail: an extern
    call against the empty registry cannot look up an implementation. -/
private theorem ExternCallBoundaryFRPfnRunContract.of_emptyExternRegistry
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := entryKey) := by
  intro _bodyCtx _result3 _callEntry
        c₂' v₂ c₁ id x y argTyp _argPoison _declaredArgPoison _argPred retSpec
        _tenv _memberCap _captures _env _impl _vRaw _hstatic _htypedCall ht_e2 ht_e1
        hGet _hArg _hImpl _hValRet _heq_cfg
        _hbodyCtx _hcallCfg _hargName _hargValue _hcaptured _hunified
  exfalso
  have hreg_c₂' : c₂'.registry = emptyExternRegistry := by
    simpa using terminatesTo_preserves_registry ht_e2
  have hreg_c₁ : c₁.registry = emptyExternRegistry :=
    (terminatesTo_preserves_registry ht_e1).trans hreg_c₂'
  rw [hreg_c₁] at hGet
  simp [emptyExternRegistry] at hGet

/-- Program-level discharge for the single-run `pfn` boundary tail. -/
private theorem ExternCallBoundaryFRPfnRunContract.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec
        tenv memberCap captures env impl vRaw hstatic htypedCall ht_e2 ht_e1
        hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_program
      (tr := tr) (root := root) (sourceArgTyp := sourceArgTyp) (argTyp := argTyp)
      (tcls := tcls)
      hagrees hstatic (hsourceProgram hstatic)
      hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceProgram hstatic) _hlookup)
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch hentryPoison, hrun⟩

/-- Reachable-declaration discharge for the single-run `pfn` boundary tail. -/
private theorem ExternCallBoundaryFRPfnRunContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {e1 e2 : Expr} {tcls : List PFnTClosure} {sourceArgTyp : Typ}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value} {a : Address} {pm : Bool}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ ρ cf o a pm
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _bodyCtx result3 callEntry
        c₂' v₂ c₁ id x y argTyp argPoison _ argPred retSpec
        tenv memberCap captures env impl vRaw hstatic htypedCall ht_e2 ht_e1
        hGet hArg hImpl hValRet heq_cfg
        _hbodyCtx hcallCfg hargName hargValue hcaptured hunified
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
    simpa [hcallCfg] using heq_cfg
  rcases
    ExternCallBoundaryPfnStaticSource.callBoundaryRun_of_reachable
      (tr := tr) (root := root) (ctxRoot := ctxRoot)
      (sourceArgTyp := sourceArgTyp) (argTyp := argTyp) (tcls := tcls)
      hagrees hstatic (hsourceReachable hstatic)
      hargName hregistryCall hunified hGetCall hArgCall
      hImplCall hValRet hcfgCall with
    ⟨entry, _hlookup, hmatch, hrun⟩
  have hentryPoison :=
    congrArg ExternDeclaration.argPoison (hagrees (hsourceReachable hstatic) _hlookup)
  exact
    ⟨entry, by simpa [ExternCallTrustedEntryKey] using _hlookup,
      htypedCall entry hmatch hentryPoison, hrun⟩

/-- Body-local boundary-run contract for the side-0 pure extern arm. -/
private def ExternCallBoundaryFRPfnSide0Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
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
        registry := registry } cf₁ o₁),
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ₀ ρ₀ cf₀ o₀ a₀ pm
      (entryKey := entryKey) (registry := registry)

def ExternCallBoundaryFRPfnSide0Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₀ : ExternId} {x₀ y₀ : Name} {argTyp₀ : Typ} {argPoison₀ : Bool}
    {retSpec₀ : ExternReturn} {tenv₀ : CapturedVarEnv} {memberCap₀ : List Capture},
    ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id₀ x₀ y₀ argTyp₀ argPoison₀ retSpec₀
      tenv₀ memberCap₀ →
    ExternCallBoundaryFRPfnSide0Contract ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) (registry := registry)

theorem ExternCallBoundaryFRPfnSide0Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _tenv₀ _memberCap₀ _hstatic
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_emptyExternRegistry (entryKey := entryKey)

theorem ExternCallBoundaryFRPfnSide0Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedRegistry hagreesExtern

/-- Body-local boundary-run contract for the side-1 pure extern arm. -/
private def ExternCallBoundaryFRPfnSide1Contract
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (_res : TypeResult) (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
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
        registry := registry } cf₁ o₁),
    ExternCallBoundaryFRPfnRunContract e1 e2 tcls sourceArgTyp μ₁ ρ₁ cf₁ o₁ a₁ pm
      (entryKey := entryKey) (registry := registry)

def ExternCallBoundaryFRPfnSide1Provider
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List PFnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ∀ {id₁ : ExternId} {x₁ y₁ : Name} {argTyp₁ : Typ} {argPoison₁ : Bool}
    {retSpec₁ : ExternReturn} {tenv₁ : CapturedVarEnv} {memberCap₁ : List Capture},
    ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id₁ x₁ y₁ argTyp₁ argPoison₁ retSpec₁
      tenv₁ memberCap₁ →
    ExternCallBoundaryFRPfnSide1Contract ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) (registry := registry)

theorem ExternCallBoundaryFRPfnSide1Provider.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    {entryKey : ExternCallEntryKey} :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _tenv₁ _memberCap₁ _hstatic
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_emptyExternRegistry (entryKey := entryKey)

theorem ExternCallBoundaryFRPfnSide1Provider.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls) :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedRegistry hagreesExtern

theorem ExternCallBoundaryFRPfnSide0Provider.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedProgram hagrees hsourceProgram

theorem ExternCallBoundaryFRPfnSide1Provider.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedProgram hagrees hsourceProgram

theorem ExternCallBoundaryFRPfnSide0Provider.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₀ _x₀ _y₀ _argTyp₀ _argPoison₀ _retSpec₀ _tenv₀ _memberCap₀ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedReachable hagrees hsourceReachable

theorem ExternCallBoundaryFRPfnSide1Provider.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List PFnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryPfnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .pfn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := [],
            preds := collectExternPreds retSpec [], argPoison := argPoison,
            captures := memberCap }) :
    ExternCallBoundaryFRPfnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) := by
  intro _id₁ _x₁ _y₁ _argTyp₁ _argPoison₁ _retSpec₁ _tenv₁ _memberCap₁ _hstaticProvider
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ExternCallBoundaryFRPfnRunContract.of_trustedReachable hagrees hsourceReachable

/-- Local registry-agreement-shaped adapter for the two impure arrow sides.

    The keyed provider shape lets populated trusted-registry callers later show
    that both sides used the same trusted entry, while empty-registry callers
    discharge the contract vacuously. -/
def TrustedRegistryAgreesWithProgramLocal
    (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
    (e1 e2 : Expr) (res : TypeResult) (tcls : List FnTClosure)
    (sourceArgTyp : Typ)
    (entryKey : ExternCallEntryKey := ExternCallNoEntryKey)
    (registry : ExternRegistry := emptyExternRegistry) : Prop :=
  ExternCallBoundaryFRFnSide0Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
    (entryKey := entryKey) (registry := registry) ∧
  ExternCallBoundaryFRFnSide1Provider ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
    (entryKey := entryKey) (registry := registry)

/-- Empty-registry local agreement: every static extern member maps to the
    corresponding vacuous body-local side contract. -/
theorem TrustedRegistryAgreesWithProgramLocal.of_emptyExternRegistry
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    {entryKey : ExternCallEntryKey} :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := entryKey) :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_emptyExternRegistry (entryKey := entryKey),
   ExternCallBoundaryFRFnSide1Provider.of_emptyExternRegistry (entryKey := entryKey)⟩

theorem TrustedRegistryAgreesWithProgramLocal.of_trustedRegistry
    {tr : TrustedRegistry}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagreesExtern :
      ∀ {argTyp : Typ}, TrustedRegistryAgreesWithFnTClosures tr argTyp tcls) :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_trustedRegistry
      hagreesExtern,
   ExternCallBoundaryFRFnSide1Provider.of_trustedRegistry
      hagreesExtern⟩

theorem TrustedRegistryAgreesWithProgramLocal.of_trustedProgram
    {tr : TrustedRegistry} {root : Expr}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithProgram root tr)
    (hsourceProgram :
      ∀ {sourceArgTyp argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationInProgram root id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_trustedProgram hagrees hsourceProgram,
   ExternCallBoundaryFRFnSide1Provider.of_trustedProgram hagrees hsourceProgram⟩

theorem TrustedRegistryAgreesWithProgramLocal.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctxᵢ : TypeContext} {predSat : PredSat} {tm : TagMeaning}
    {e1 e2 : Expr} {res : TypeResult} {tcls : List FnTClosure}
    {sourceArgTyp : Typ}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hsourceReachable :
      ∀ {argTyp : Typ} {argPoison : Bool} {id : ExternId} {x y : Name}
        {retSpec : ExternReturn} {effects : List Effect}
        {capturedEnv : CapturedVarEnv} {memberCap : List Capture},
        ExternCallBoundaryFnStaticSource tcls sourceArgTyp id x y argTyp argPoison retSpec effects
          capturedEnv memberCap →
        ExternDeclarationReachableFromContext root ctxRoot id
          { id := id, kind := .fn, typ := argTyp, argName := some x,
            retSpec := some retSpec, effects := effects,
            preds := collectExternPreds retSpec effects, argPoison := argPoison,
            captures := memberCap }) :
    TrustedRegistryAgreesWithProgramLocal ctxᵢ predSat tm e1 e2 res tcls sourceArgTyp
      (entryKey := ExternCallTrustedEntryKey tr)
      (registry := TrustedRegistry.toRuntimeRegistry tr) :=
  ⟨ExternCallBoundaryFRFnSide0Provider.of_trustedReachable hagrees hsourceReachable,
   ExternCallBoundaryFRFnSide1Provider.of_trustedReachable hagrees hsourceReachable⟩

