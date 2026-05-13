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

end ExternBoundarySpec
