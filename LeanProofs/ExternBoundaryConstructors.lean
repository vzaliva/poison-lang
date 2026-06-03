/-
  ExternBoundaryConstructors.lean - Reusable proof constructors for trusted externs.

  This module is the private helper layer for compact `ExternBoundarySpec`
  constructors.  Public constructor theorems are added in later stages; the
  declarations here keep raw `StepFRPost` and `ExternBoundarySinglePost`
  assembly out of driver-facing behavior predicates.
-/
import LeanProofs.ExternBoundaryProofs

open Std

namespace ExternBoundarySpec

private abbrev cleanIntQTyp : QTyp :=
  { etyp := ETyp.int, poison := false, pred := Predicate.noPred }

private theorem false_of_decl_val_kind_fn
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .fn)
    (hfacts : ExternDeclValFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.fn = ExternDeclarationKind.val :=
    hkind.symm.trans hfacts.kind_val
  cases h

private theorem false_of_decl_val_kind_pfn
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .pfn)
    (hfacts : ExternDeclValFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.pfn = ExternDeclarationKind.val :=
    hkind.symm.trans hfacts.kind_val
  cases h

private theorem false_of_decl_fn_kind_val
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .val)
    (hfacts : ExternDeclFnFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.val = ExternDeclarationKind.fn :=
    hkind.symm.trans hfacts.kind_fn
  cases h

private theorem false_of_decl_fn_kind_pfn
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .pfn)
    (hfacts : ExternDeclFnFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.pfn = ExternDeclarationKind.fn :=
    hkind.symm.trans hfacts.kind_fn
  cases h

private theorem false_of_decl_pfn_kind_val
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .val)
    (hfacts : ExternDeclPfnFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.val = ExternDeclarationKind.pfn :=
    hkind.symm.trans hfacts.kind_pfn
  cases h

private theorem false_of_decl_pfn_kind_fn
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .fn)
    (hfacts : ExternDeclPfnFacts d impl ctx res cᵢ cₒ v) : False := by
  have h : ExternDeclarationKind.fn = ExternDeclarationKind.pfn :=
    hkind.symm.trans hfacts.kind_pfn
  cases h

private theorem false_of_call_fn_kind_pfn
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cₒ : Config} {v : Value}
    (hkind : d.kind = .pfn)
    (hfacts : ExternCallFnFacts d impl entry res cₒ v) : False := by
  have h : ExternDeclarationKind.pfn = ExternDeclarationKind.fn :=
    hkind.symm.trans hfacts.kind_fn
  cases h

private theorem false_of_call_pfn_kind_fn
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cₒ : Config} {v : Value}
    (hkind : d.kind = .fn)
    (hfacts : ExternCallPfnFacts d impl entry res cₒ v) : False := by
  have h : ExternDeclarationKind.fn = ExternDeclarationKind.pfn :=
    hkind.symm.trans hfacts.kind_pfn
  cases h

private theorem false_of_call_run_kind_val
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cₒ : Config} {v : Value}
    (hkind : d.kind = .val)
    (hrun : ExternCallBoundaryRun d impl entry res cₒ v) : False := by
  cases hrun with
  | fn hfacts =>
      have h : ExternDeclarationKind.val = ExternDeclarationKind.fn :=
        hkind.symm.trans hfacts.kind_fn
      cases h
  | pfn hfacts =>
      have h : ExternDeclarationKind.val = ExternDeclarationKind.pfn :=
        hkind.symm.trans hfacts.kind_pfn
      cases h

private theorem false_of_impl_fn_eq_pfn
    {implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)}
    {implPfn : VarEnv → Value → Memory → Except ExternError Value} :
    ExternImpl.fn implFn = ExternImpl.pfn implPfn → False := by
  intro h
  cases h

private theorem false_of_impl_val_eq_pfn
    {v : Value} {implPfn : VarEnv → Value → Memory → Except ExternError Value} :
    ExternImpl.val v = ExternImpl.pfn implPfn → False := by
  intro h
  cases h

private theorem false_of_impl_pfn_eq_fn
    {implPfn : VarEnv → Value → Memory → Except ExternError Value}
    {implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)} :
    ExternImpl.pfn implPfn = ExternImpl.fn implFn → False := by
  intro h
  cases h

private theorem false_of_impl_val_eq_fn
    {v : Value}
    {implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)} :
    ExternImpl.val v = ExternImpl.fn implFn → False := by
  intro h
  cases h

private theorem false_of_impl_fn_eq_val
    {implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)}
    {v : Value} :
    ExternImpl.fn implFn = ExternImpl.val v → False := by
  intro h
  cases h

private theorem false_of_impl_pfn_eq_val
    {implPfn : VarEnv → Value → Memory → Except ExternError Value}
    {v : Value} :
    ExternImpl.pfn implPfn = ExternImpl.val v → False := by
  intro h
  cases h

private theorem declRun_output_config_eq_input
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult} {cᵢ cₒ : Config} {v : Value}
    (hrun : ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v) :
    cₒ = cᵢ := by
  cases hrun with
  | val hfacts => exact hfacts.output_config
  | fn hfacts => exact hfacts.output_config
  | pfn hfacts => exact hfacts.output_config

private theorem callPfn_bodyOutputConfig_eq_bodyConfig
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cₒ : Config} {v : Value}
    (hfacts : ExternCallPfnFacts d impl entry res cₒ v) :
    entry.bodyOutputConfig cₒ = entry.bodyConfig := by
  rw [hfacts.output_config]
  simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]

private theorem callRun_pfn_bodyOutputConfig_eq_bodyConfig
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cₒ : Config} {v : Value}
    (hkind : d.kind = .pfn)
    (hrun : ExternCallBoundaryRun d impl entry res cₒ v) :
    entry.bodyOutputConfig cₒ = entry.bodyConfig := by
  cases hrun with
  | fn hfacts => exact False.elim (false_of_call_fn_kind_pfn hkind hfacts)
  | pfn hfacts => exact callPfn_bodyOutputConfig_eq_bodyConfig hfacts

private theorem valueHasETyp_cleanInt
    {θ : RealizationMap} {n : Int} :
    valueHasETyp θ (Value.num n) cleanIntQTyp.etyp :=
  valueHasETyp.num n

private theorem valueConsistentWithRegime_cleanInt
    {predSat : PredSat} {R : Regime} {μ : Memory} {θ : RealizationMap} {n : Int} :
    valueConsistentWithRegime predSat R cleanIntQTyp μ θ (Value.num n) := by
  exact
    valueConsistentWithRegime.noTag (by rfl)
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (valueHasETyp_cleanInt (θ := θ) (n := n)) (by rfl))

private theorem agreeValueUnder_cleanInt_of_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (heq : n₀ = n₁) :
    agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ cleanIntQTyp
      (Value.num n₀) (Value.num n₁) := by
  cases heq
  exact
    agreeValueUnder.clean_eq_nonref_nonarrow (hpoison := rfl) (hnotfun := rfl)
      (hnotref := by
        intro href
        rcases href with ⟨ls, hls⟩
        cases hls)
      rfl

private theorem resultAgreesIfClean_cleanInt_of_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (heq : n₀ = n₁) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ cleanIntQTyp
      (Value.num n₀) (Value.num n₁) := by
  intro _hclean
  exact agreeValueUnder_cleanInt_of_eq heq

private theorem valueConsistentWithRegime_int_noPred
    {predSat : PredSat} {R : Regime} {qt : QTyp}
    {μ : Memory} {θ : RealizationMap} {n : Int}
    (hetyp : qt.etyp = ETyp.int)
    (hpred : qt.pred = Predicate.noPred) :
    valueConsistentWithRegime predSat R qt μ θ (Value.num n) := by
  refine valueConsistentWithRegime.noTag ?_ ?_
  · simp [qtypGuardTag, hpred]
  · exact
      closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by simpa [hetyp] using (valueHasETyp.num (θ := θ) n))
        (by rw [hetyp]; rfl)

private theorem resultAgreesIfClean_int_noPred_of_eq
    {predSat : PredSat} {R : Regime} {qt : QTyp}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (hetyp : qt.etyp = ETyp.int)
    (hpred : qt.pred = Predicate.noPred)
    (heq : n₀ = n₁) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt
      (Value.num n₀) (Value.num n₁) := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      cases heq
      exact
        agreeValueUnder.clean_eq_nonref_nonarrow hpoison
          (by rw [hetyp]; rfl)
          (by
            intro href
            rcases href with ⟨ls, hls⟩
            simp [hetyp] at hls)
          rfl
  | guard k htag _hregime _hnotfun =>
      have hnone : qtypGuardTag qt = none := by
        simp [qtypGuardTag, hpred]
      simp [hnone] at htag

/-- Compact behavior contract for pure unary integer extern implementations. -/
structure PureUnaryCleanIntSpec (d : ExternDeclaration) (impl : ExternImpl) where
  argName : Name
  implPfn : VarEnv → Value → Memory → Except ExternError Value
  compute : VarEnv → Int → Int
  kind_pfn : d.kind = .pfn
  typ_int : d.typ = Typ.int
  argName_eq : d.argName = some argName
  retSpec_eq : d.retSpec = some (.simple .int false .noPred)
  impl_eq : impl = ExternImpl.pfn implPfn
  success_num :
    ∀ {env : VarEnv} {vArg : Value} {mem : Memory} {vOut : Value},
      implPfn env vArg mem = .ok vOut →
      ∃ n, vArg = Value.num n ∧ vOut = Value.num (compute env n)
  clean_agree :
    ∀ {predSat : PredSat} {ctx : TypeContext}
      {entry₀ entry₁ : ExternCallEntry} {θ₀ θ₁ : RealizationMap}
      {n₀ n₁ : Int},
      BodyEntryInputsAgree predSat ctx entry₀ entry₁ θ₀ θ₁ →
      entry₀.argValue = Value.num n₀ →
      entry₁.argValue = Value.num n₁ →
      agreeValueUnder predSat ctx.regime
        entry₀.bodyConfig.memory entry₁.bodyConfig.memory θ₀ θ₁
        { etyp := ETyp.int, poison := false, pred := Predicate.noPred }
        (Value.num n₀) (Value.num n₁) →
      compute entry₀.unifiedEnv n₀ = compute entry₁.unifiedEnv n₁
  output_wf :
    ∀ {env : VarEnv} {vArg : Value} {mem : Memory} {addr : Address} {vRaw : Value},
      implPfn env vArg mem = .ok vRaw →
      (∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      wfValue addr vRaw

private theorem pureUnaryCleanInt_operational
    {d : ExternDeclaration} {impl : ExternImpl}
    (hspec : PureUnaryCleanIntSpec d impl) :
    ExternOperationalSafe d impl := by
  refine ⟨?_, ?_, ?_⟩
  · intro implFn himpl env vArg mem addr vRaw mem' addr' _hrun
    have hbad : ExternImpl.pfn hspec.implPfn = ExternImpl.fn implFn :=
      hspec.impl_eq.symm.trans himpl
    exact False.elim (false_of_impl_pfn_eq_fn hbad)
  · intro implPfn himpl env vArg mem addr vRaw hrun hmem henv harg
    have heq : ExternImpl.pfn hspec.implPfn = ExternImpl.pfn implPfn :=
      hspec.impl_eq.symm.trans himpl
    cases heq
    exact hspec.output_wf hrun hmem henv harg
  · intro v himpl cfg _hwf
    have hbad : ExternImpl.pfn hspec.implPfn = ExternImpl.val v :=
      hspec.impl_eq.symm.trans himpl
    exact False.elim (false_of_impl_pfn_eq_val hbad)

private theorem boundaryTagMeaningPost_of_parts
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat}
    {tm tm' : TagMeaning}
    (hext : tm ⊑ tm')
    (hbounded : TagMeaningBounded tm' res.nextTag')
    (hwf : wfTagMeaningCtx tm' (ctxAfter ctx res))
    (hrespects : QTypRespectsTagMeaning tm' res.qualType)
    (hlaws : PredSatLaws predSat tm') :
    BoundaryTagMeaningPost ctx res predSat tm tm' :=
  ⟨hext, hbounded, hwf, hrespects, hlaws⟩

private theorem stepFRPost_of_parts
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm tm' : TagMeaning}
    {θ₀ θ₁ θ₀' θ₁' : RealizationMap}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (htag : BoundaryTagMeaningPost ctx res predSat tm tm')
    (hθ₀ : wfExtendsMap θ₀ θ₀')
    (hθ₁ : wfExtendsMap θ₁ θ₁')
    (htyp₀ : valueHasETyp θ₀' o₀ res.qualType.etyp)
    (htyp₁ : valueHasETyp θ₁' o₁ res.qualType.etyp)
    (hwfCtx : wfTypeContext (ctxAfter ctx res))
    (hboundedCtx : TagBoundedCtx (ctxAfter ctx res))
    (hwfCfg₀ : wfConfig cf₀)
    (hwfCfg₁ : wfConfig cf₁)
    (hric₀ : runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀')
    (hric₁ : runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁')
    (hreg : regimeConsistentWithCtx (ctxAfter ctx res))
    (hcons₀ :
      consistentWithRegime predSat (ctxAfter ctx res).regime
        (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀')
    (hcons₁ :
      consistentWithRegime predSat (ctxAfter ctx res).regime
        (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁')
    (hagree :
      agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁')
    (hvalc₀ :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime
        res.qualType cf₀.memory θ₀' o₀)
    (hvalc₁ :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime
        res.qualType cf₁.memory θ₁' o₁)
    (hresult :
      resultAgreesIfClean predSat (ctxAfter ctx res).regime
        cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁) :
    StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
  refine ⟨tm', htag, htag.2.2.2.2, htag.2.2.2.1, θ₀', θ₁', ?_⟩
  exact
    ⟨hθ₀, hθ₁, htyp₀, htyp₁, htag.2.2.1, hwfCtx, hboundedCtx, hwfCfg₀, hwfCfg₁,
      hric₀, hric₁, hreg, hcons₀, hcons₁, hagree, hvalc₀, hvalc₁, hresult⟩

private theorem externBoundarySinglePost_of_parts
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat}
    {tm tm' : TagMeaning} {θ θ' : RealizationMap}
    {μ : Memory} {cf : Config} {o : Value}
    (htag : BoundaryTagMeaningPost ctx res predSat tm tm')
    (hθ : wfExtendsMap θ θ')
    (htyp : valueHasETyp θ' o res.qualType.etyp)
    (hric : runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ')
    (hcons :
      consistentWithRegime predSat (ctxAfter ctx res).regime
        (ctxAfter ctx res) cf.memory cf.varEnv θ')
    (hvalc :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime
        res.qualType cf.memory θ' o)
    (hpres : PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ')
    (hfresh : FreshCleanLocsUnrealizedOneRun ctx res θ') :
    ExternBoundarySinglePost ctx res predSat tm θ μ cf o := by
  exact ⟨tm', htag, θ', hθ, htyp, hric, hcons, hvalc, hpres, hfresh⟩

private theorem externBoundarySinglePost_of_same_state
    {ctx : TypeContext} {res : TypeResult} {predSat : PredSat}
    {tm tm' : TagMeaning} {θ : RealizationMap}
    {μ : Memory} {ρ : VarEnv} {cf : Config} {o : Value}
    {a : Address} {pm : Bool} {registry : ExternRegistry}
    (htag : BoundaryTagMeaningPost ctx res predSat tm tm')
    (hctxAfter : ctxAfter ctx res = ctx)
    (hcf : cf = { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
                  registry := registry })
    (htyp : valueHasETyp θ o res.qualType.etyp)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcons : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    (hvalc : valueConsistentWithRegime predSat ctx.regime res.qualType μ θ o) :
    ExternBoundarySinglePost ctx res predSat tm θ μ cf o := by
  refine
    externBoundarySinglePost_of_parts (ctx := ctx) (res := res) (predSat := predSat)
      (tm := tm) (tm' := tm') (θ := θ) (θ' := θ) (μ := μ) (cf := cf) (o := o)
      htag ?_ htyp ?_ ?_ ?_ ?_ ?_
  · exact ⟨fun _ _ hlookup => hlookup, fun hθwf => hθwf⟩
  · simpa [hctxAfter, hcf] using hric
  · simpa [hctxAfter, hcf] using hcons
  · simpa [hctxAfter, hcf] using hvalc
  · simpa [hcf] using (PreservesInheritedFinalCleanLocsOneRun.refl
      (ctx := ctx) (res := res) (ρ := ρ) hric)
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

private theorem collectAndAllocExternTags_noPred (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.noPred] nextTag = .ok ({}, nextTag) := by
  rfl

private theorem pureUnaryCleanInt_call_result_shape
    {d : ExternDeclaration} {impl : ExternImpl}
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (hspec : PureUnaryCleanIntSpec d impl)
    (htyped : ExternBoundaryTyping.Call d typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx := by
  cases htyped with
  | fnExternMember hid hkind htyp harg hret heff hbody happly =>
      have hbad : ExternDeclarationKind.pfn = ExternDeclarationKind.fn :=
        hspec.kind_pfn.symm.trans hkind
      cases hbad
  | fnRegularExternBody hid hkind htyp harg hret heff hbody htc hres =>
      have hbad : ExternDeclarationKind.pfn = ExternDeclarationKind.fn :=
        hspec.kind_pfn.symm.trans hkind
      cases hbad
  | pfnExternMember hid hkind htyp harg hret hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec tenv
      have hargTyp : argTyp = Typ.int :=
        htyp.symm.trans hspec.typ_int
      subst argTyp
      have hretSpec :
          retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have :
            some retSpec =
              some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) :=
          hret.symm.trans hspec.retSpec_eq
        exact Option.some.inj this
      subst retSpec
      cases fuel with
      | zero =>
          simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          -- Leading argument-condition gate: throw branch is impossible on .ok.
          split at happly
          · simp at happly
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_⟩
          · by_cases hprov : joinPoison p1 p = true
            · simp [normalizeAppResultByProvenance, hprov]
            · simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true
            · simp [normalizeAppResultByProvenance, hprov]
            · simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]
            simp only [ctxAfter, applyExternRegimePolicy]
            rfl

private theorem pureUnaryCleanInt_call_output
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hspec : PureUnaryCleanIntSpec d impl)
    (hfacts : ExternCallPfnFacts d impl entry res cf o) :
    ∃ n, entry.argValue = Value.num n ∧
      o = Value.num (hspec.compute entry.unifiedEnv n) ∧
      cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  have himplEq : ExternImpl.pfn hspec.implPfn = ExternImpl.pfn implPfn :=
    hspec.impl_eq.symm.trans himpl
  cases himplEq
  have hret :
      retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
    have :
        some retSpec =
          some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) :=
      hretSpec.symm.trans hspec.retSpec_eq
    exact Option.some.inj this
  subst retSpec
  rcases hspec.success_num hrun with ⟨n, harg, hraw⟩
  have hout : o = Value.num (hspec.compute entry.unifiedEnv n) := by
    rw [hraw] at hvalRet
    unfold validateExternReturn at hvalRet
    simp [valueMatchesTyp] at hvalRet
    exact hvalRet.symm
  exact ⟨n, harg, hout, hfacts.output_config⟩

end ExternBoundarySpec
