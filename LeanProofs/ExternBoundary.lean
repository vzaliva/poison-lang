/-
  ExternBoundary.lean - Shared proof-side interfaces for trusted extern
  boundary evidence.

  The definitions here are intentionally declarative.  Concrete extern drivers
  will later prove these contracts for registered implementations; current
  empty-registry FR proofs only depend on the shape compiling.
-/
import LeanProofs.StepFR

open Std

inductive ExternDeclarationKind where
  | val
  | fn
  | pfn
  deriving Repr, BEq

inductive ExternBoundaryKind where
  | declVal
  | declFn
  | declPfn
  | callFn
  | callPfn
  deriving Repr, BEq

/-- Static declaration shape extracted from a source expression. -/
structure ExternDeclaration where
  id      : ExternId
  kind    : ExternDeclarationKind
  typ     : Typ
  argName : Option Name
  retSpec : Option ExternReturn
  effects : List Effect
  preds   : List SyntaxPredicate

/-- Runtime/typechecking facts for a successful `extern val` declaration step. -/
structure ExternDeclValFacts
    (d : ExternDeclaration) (impl : ExternImpl)
    (_ctx : TypeContext) (_res : TypeResult)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  kind_val : d.kind = .val
  lookup : cᵢ.registry.get? d.id = some impl
  impl_value : ∃ vImpl, impl = ExternImpl.val vImpl ∧ v = vImpl
  output_config : cₒ = cᵢ

/-- Runtime/typechecking facts for a successful `extern fn` declaration step. -/
structure ExternDeclFnFacts
    (d : ExternDeclaration) (impl : ExternImpl)
    (_ctx : TypeContext) (_res : TypeResult)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  kind_fn : d.kind = .fn
  lookup : cᵢ.registry.get? d.id = some impl
  argName_some : ∃ x, d.argName = some x
  retSpec_some : ∃ retSpec, d.retSpec = some retSpec
  impl_fn : ∃ implFn, impl = ExternImpl.fn implFn
  output_config : cₒ = cᵢ
  value_shape : ∃ x retSpec, d.argName = some x ∧ d.retSpec = some retSpec ∧
    v = Value.closure x (Expr.externFn d.id x d.typ retSpec d.effects) cᵢ.varEnv

/-- Runtime/typechecking facts for a successful `extern pfn` declaration step. -/
structure ExternDeclPfnFacts
    (d : ExternDeclaration) (impl : ExternImpl)
    (_ctx : TypeContext) (_res : TypeResult)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  kind_pfn : d.kind = .pfn
  lookup : cᵢ.registry.get? d.id = some impl
  argName_some : ∃ x, d.argName = some x
  retSpec_some : ∃ retSpec, d.retSpec = some retSpec
  impl_pfn : ∃ implFn, impl = ExternImpl.pfn implFn
  output_config : cₒ = cᵢ
  value_shape : ∃ x retSpec, d.argName = some x ∧ d.retSpec = some retSpec ∧
    v = Value.peClosure x (Expr.externPfn d.id x d.typ retSpec) cᵢ.varEnv

/-- Runtime/typechecking evidence for a successful extern declaration step. -/
inductive ExternDeclBoundaryRun
    (d : ExternDeclaration) (impl : ExternImpl)
    (ctx : TypeContext) (res : TypeResult)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  | val :
      ExternDeclValFacts d impl ctx res cᵢ cₒ v →
      ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v
  | fn :
      ExternDeclFnFacts d impl ctx res cᵢ cₒ v →
      ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v
  | pfn :
      ExternDeclPfnFacts d impl ctx res cᵢ cₒ v →
      ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v

namespace ExternDeclBoundaryRun

theorem val_of_runtime
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (hkind : d.kind = .val)
    (hlookup : cᵢ.registry.get? d.id = some impl)
    (himpl : impl = ExternImpl.val v)
    (hcfg : cₒ = cᵢ) :
    ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v := by
  refine ExternDeclBoundaryRun.val ?_
  exact
    { kind_val := hkind
      lookup := hlookup
      impl_value := ⟨v, himpl, rfl⟩
      output_config := hcfg }

theorem fn_of_runtime
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    {x : Name} {retSpec : ExternReturn}
    (hkind : d.kind = .fn)
    (hlookup : cᵢ.registry.get? d.id = some impl)
    (harg : d.argName = some x)
    (hret : d.retSpec = some retSpec)
    (himpl : ∃ implFn, impl = ExternImpl.fn implFn)
    (hcfg : cₒ = cᵢ)
    (hval :
      v = Value.closure x (Expr.externFn d.id x d.typ retSpec d.effects) cᵢ.varEnv) :
    ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v := by
  refine ExternDeclBoundaryRun.fn ?_
  exact
    { kind_fn := hkind
      lookup := hlookup
      argName_some := ⟨x, harg⟩
      retSpec_some := ⟨retSpec, hret⟩
      impl_fn := himpl
      output_config := hcfg
      value_shape := ⟨x, retSpec, harg, hret, hval⟩ }

theorem pfn_of_runtime
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    {x : Name} {retSpec : ExternReturn}
    (hkind : d.kind = .pfn)
    (hlookup : cᵢ.registry.get? d.id = some impl)
    (harg : d.argName = some x)
    (hret : d.retSpec = some retSpec)
    (himpl : ∃ implFn, impl = ExternImpl.pfn implFn)
    (hcfg : cₒ = cᵢ)
    (hval :
      v = Value.peClosure x (Expr.externPfn d.id x d.typ retSpec) cᵢ.varEnv) :
    ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v := by
  refine ExternDeclBoundaryRun.pfn ?_
  exact
    { kind_pfn := hkind
      lookup := hlookup
      argName_some := ⟨x, harg⟩
      retSpec_some := ⟨retSpec, hret⟩
      impl_pfn := himpl
      output_config := hcfg
      value_shape := ⟨x, retSpec, harg, hret, hval⟩ }

theorem lookup
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (h : ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v) :
    cᵢ.registry.get? d.id = some impl := by
  cases h with
  | val hfacts => exact hfacts.lookup
  | fn hfacts => exact hfacts.lookup
  | pfn hfacts => exact hfacts.lookup

theorem of_terminatesTo_externVal
    {id : ExternId} {typ : Typ} {poison : Bool} {pred : SyntaxPredicate}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (ht : terminatesTo (Expr.externVal id typ poison pred) cᵢ cₒ v) :
    ∃ impl,
      ExternDeclBoundaryRun
        { id := id, kind := .val, typ := typ, argName := none, retSpec := none,
          effects := [], preds := [pred] }
        impl ctx res cᵢ cₒ v := by
  rcases ht with ⟨fuel, verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      rw [← Std.HashMap.get?_eq_getElem?] at hbeval
      cases hlookup : cᵢ.registry.get? id with
      | none =>
          rw [hlookup] at hbeval
          simp at hbeval
      | some impl =>
          cases impl with
          | val vImpl =>
              by_cases hmatch : valueMatchesTyp vImpl typ = true
              · rw [hlookup] at hbeval
                simp [hmatch] at hbeval
                rcases hbeval with ⟨hcfg, hv⟩
                exact
                  ⟨ExternImpl.val vImpl,
                    ExternDeclBoundaryRun.val_of_runtime rfl hlookup
                      (by simp [hv]) hcfg.symm⟩
              · rw [hlookup] at hbeval
                simp [hmatch] at hbeval
          | pfn implPfn =>
              rw [hlookup] at hbeval
              simp at hbeval
          | fn implFn =>
              rw [hlookup] at hbeval
              simp at hbeval

theorem of_terminatesTo_externFn
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (ht : terminatesTo (Expr.externFn id x argTyp retSpec effects) cᵢ cₒ v) :
    ∃ impl,
      ExternDeclBoundaryRun
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
        impl ctx res cᵢ cₒ v := by
  rcases ht with ⟨fuel, verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      rw [← Std.HashMap.get?_eq_getElem?] at hbeval
      cases hlookup : cᵢ.registry.get? id with
      | none =>
          rw [hlookup] at hbeval
          simp at hbeval
      | some impl =>
          cases impl with
          | val vImpl =>
              rw [hlookup] at hbeval
              simp at hbeval
          | pfn implPfn =>
              rw [hlookup] at hbeval
              simp at hbeval
          | fn implFn =>
              rw [hlookup] at hbeval
              simp at hbeval
              rcases hbeval with ⟨hcfg, hv⟩
              exact
                ⟨ExternImpl.fn implFn,
                  ExternDeclBoundaryRun.fn_of_runtime rfl hlookup rfl rfl
                    ⟨implFn, rfl⟩ hcfg.symm (by simpa using hv.symm)⟩

theorem of_terminatesTo_externPfn
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (ht : terminatesTo (Expr.externPfn id x argTyp retSpec) cᵢ cₒ v) :
    ∃ impl,
      ExternDeclBoundaryRun
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] }
        impl ctx res cᵢ cₒ v := by
  rcases ht with ⟨fuel, verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      rw [← Std.HashMap.get?_eq_getElem?] at hbeval
      cases hlookup : cᵢ.registry.get? id with
      | none =>
          rw [hlookup] at hbeval
          simp at hbeval
      | some impl =>
          cases impl with
          | val vImpl =>
              rw [hlookup] at hbeval
              simp at hbeval
          | pfn implPfn =>
              rw [hlookup] at hbeval
              simp at hbeval
              rcases hbeval with ⟨hcfg, hv⟩
              exact
                ⟨ExternImpl.pfn implPfn,
                  ExternDeclBoundaryRun.pfn_of_runtime rfl hlookup rfl rfl
                    ⟨implPfn, rfl⟩ hcfg.symm (by simpa using hv.symm)⟩
          | fn implFn =>
              rw [hlookup] at hbeval
              simp at hbeval

end ExternDeclBoundaryRun

/-- The body-entry state for an extern call. -/
structure ExternCallEntry where
  bodyCtx      : TypeContext
  callConfig   : Config
  capturedEnv  : VarEnv
  argName      : Name
  argValue     : Value
  unifiedEnv   : VarEnv

namespace ExternCallEntry

def ofRuntime
    (bodyCtx : TypeContext) (callConfig : Config)
    (capturedEnv : VarEnv) (argName : Name) (argValue : Value) :
    ExternCallEntry :=
  { bodyCtx := bodyCtx
    callConfig := callConfig
    capturedEnv := capturedEnv
    argName := argName
    argValue := argValue
    unifiedEnv := VarEnv.update capturedEnv argName argValue }

@[simp] theorem ofRuntime_unifiedEnv
    (bodyCtx : TypeContext) (callConfig : Config)
    (capturedEnv : VarEnv) (argName : Name) (argValue : Value) :
    (ofRuntime bodyCtx callConfig capturedEnv argName argValue).unifiedEnv =
      VarEnv.update capturedEnv argName argValue :=
  rfl

/-- Synthetic body-input config for a call boundary.

Runtime extern dispatch happens from `callConfig`, but the body-local proof
boundary is typed under the closure environment extended with the argument. -/
def bodyConfig (entry : ExternCallEntry) : Config :=
  { entry.callConfig with varEnv := entry.unifiedEnv }

/-- Synthetic body-output config corresponding to a runtime extern result. -/
def bodyOutputConfig (entry : ExternCallEntry) (cf : Config) : Config :=
  { cf with varEnv := entry.unifiedEnv }

end ExternCallEntry

/-- Runtime facts for a successful impure extern dispatch. -/
structure ExternCallFnFacts
    (d : ExternDeclaration) (impl : ExternImpl)
    (entry : ExternCallEntry) (_res : TypeResult)
    (cₒ : Config) (v : Value) : Prop where
  kind_fn : d.kind = .fn
  argName : d.argName = some entry.argName
  retSpec : ∃ retSpec, d.retSpec = some retSpec
  pureMode_false : entry.callConfig.pureMode = false
  unifiedEnv_eq : entry.unifiedEnv = VarEnv.update entry.capturedEnv entry.argName entry.argValue
  lookup : entry.callConfig.registry.get? d.id = some impl
  impl_success :
    ∃ implFn retSpec vRaw,
      impl = ExternImpl.fn implFn ∧
      d.retSpec = some retSpec ∧
      valueMatchesTyp entry.argValue d.typ = true ∧
      implFn entry.unifiedEnv entry.argValue entry.callConfig.memory entry.callConfig.nextAddr =
        .ok (vRaw, cₒ.memory, cₒ.nextAddr) ∧
      validateExternReturn d.id retSpec vRaw = .ok v
  output_config :
    cₒ = { entry.callConfig with memory := cₒ.memory, nextAddr := cₒ.nextAddr }

/-- Runtime facts for a successful pure extern dispatch. -/
structure ExternCallPfnFacts
    (d : ExternDeclaration) (impl : ExternImpl)
    (entry : ExternCallEntry) (_res : TypeResult)
    (cₒ : Config) (v : Value) : Prop where
  kind_pfn : d.kind = .pfn
  argName : d.argName = some entry.argName
  retSpec : ∃ retSpec, d.retSpec = some retSpec
  unifiedEnv_eq : entry.unifiedEnv = VarEnv.update entry.capturedEnv entry.argName entry.argValue
  lookup : entry.callConfig.registry.get? d.id = some impl
  impl_success :
    ∃ implFn retSpec vRaw,
      impl = ExternImpl.pfn implFn ∧
      d.retSpec = some retSpec ∧
      valueMatchesTyp entry.argValue d.typ = true ∧
      implFn entry.unifiedEnv entry.argValue entry.callConfig.memory = .ok vRaw ∧
      validateExternReturn d.id retSpec vRaw = .ok v
  output_config : cₒ = entry.callConfig

/-- Runtime/typechecking evidence for a successful extern dispatch step. -/
inductive ExternCallBoundaryRun
    (d : ExternDeclaration) (impl : ExternImpl)
    (entry : ExternCallEntry) (res : TypeResult)
    (cₒ : Config) (v : Value) : Prop where
  | fn :
      ExternCallFnFacts d impl entry res cₒ v →
      ExternCallBoundaryRun d impl entry res cₒ v
  | pfn :
      ExternCallPfnFacts d impl entry res cₒ v →
      ExternCallBoundaryRun d impl entry res cₒ v

namespace ExternCallBoundaryRun

theorem lookup
    {d : ExternDeclaration} {impl : ExternImpl}
    {entry : ExternCallEntry} {res : TypeResult}
    {cₒ : Config} {v : Value}
    (h : ExternCallBoundaryRun d impl entry res cₒ v) :
    entry.callConfig.registry.get? d.id = some impl := by
  cases h with
  | fn hfacts => exact hfacts.lookup
  | pfn hfacts => exact hfacts.lookup

end ExternCallBoundaryRun

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

/-- Paired extern-declaration boundary runs produce the same post as `StepFR`.

    `postExpr` is explicit because the current `StepFRPost` remains indexed by
    the expression whose typechecking produced the result. -/
def ExternDeclBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (postExpr : Expr) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning),
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
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
            registry := registry } cf₀ o₀ →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
            registry := registry } cf₁ o₁ →
        StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

/-- Paired extern-call boundary runs produce the same post as the surrounding
    expression step. -/
def ExternCallBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (postExpr : Expr) (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (entry₀ entry₁ : ExternCallEntry),
    let ctx := entry₀.bodyCtx
    entry₁.bodyCtx = ctx →
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

theorem to_singleRunPost
    {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {θ : RealizationMap} {μ : Memory} {ρ : VarEnv}
    {cf : Config} {o : Value} {registry : ExternRegistry}
    (hθwf : wfRealizationMap θ)
    (hwf : wfTypeContext ctx)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hreg : regimeConsistentWithCtx ctx)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    (a : Address) (pm : Bool)
    (hwfcfg :
      wfConfig ({ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm, registry := registry } : Config))
    (h : ExternBoundarySinglePost ctx res predSat tm θ μ cf o) :
    StepFRSingleRunFinalCleanPcTruePost ctx res predSat
      (registry := registry) μ ρ θ cf o
      hθwf hwf hric hreg hcwr a pm hwfcfg := by
  rcases h with ⟨_tm', _htag, θ', hθext, hvtyp, hric', hcwr', hvalc', hpres, hfresh⟩
  exact ⟨θ', hθext, hvtyp, hric', hcwr', hvalc', hpres, hfresh⟩

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
      hθwf hwf hric hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg := by
  rcases h with ⟨_tm', _htag, θ', hθext, hvtyp, hric', hcwr', hvalc', hpres, hfresh⟩
  exact
    ⟨θ', hθext, hvtyp, hric', consistentWithRegime_to_masked hcwr',
      valueConsistentWithRegime_to_masked hvalc', hpres, hfresh⟩

end ExternBoundarySinglePost

def ExternDeclBoundarySingle
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning),
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
  ∀ (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (entry : ExternCallEntry),
    let ctx := entry.bodyCtx
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

/-- Forgetful view of either declaration or call boundary runs for operational
    well-formedness consumers. -/
inductive ExternBoundaryWFRun
    (d : ExternDeclaration) (impl : ExternImpl)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  | decl {ctx res} :
      ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v →
      ExternBoundaryWFRun d impl cᵢ cₒ v
  | call {entry res} :
      ExternCallBoundaryRun d impl entry res cₒ v →
      cᵢ = entry.callConfig →
      ExternBoundaryWFRun d impl cᵢ cₒ v

def ExternBoundaryPreservesWF
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (cᵢ cₒ : Config) (v : Value),
    ExternBoundaryWFRun d impl cᵢ cₒ v →
    wfConfig cᵢ →
    wfConfig cₒ ∧ wfValue cₒ.nextAddr v

structure ExternBoundarySpec
    (d : ExternDeclaration) (impl : ExternImpl) : Prop where
  declFR : ExternDeclBoundaryFR d impl
  callFR : ExternCallBoundaryFR d impl
  declSingle : ExternDeclBoundarySingle d impl
  callSingle : ExternCallBoundarySingle d impl
  wf : ExternBoundaryPreservesWF d impl

/-- Registry-parametric masked single-run declaration-boundary adapter used by
    the step proof. -/
def ExternDeclBoundarySingleMaskedContract
    (masked : Tag → Prop) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning) (registry : ExternRegistry)
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  PredSatLaws predSat tm →
  ExternTypingAssumptions →
  wfTagMeaningCtx tm ctx →
  TagMeaningBounded tm ctx.nextTag →
  ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value),
    (hθwf : wfRealizationMap θ) →
    (hwf : wfTypeContext ctx) →
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) →
    (hreg : regimeConsistentWithCtxMasked masked ctx) →
    (hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none) →
    (hmasked_absent : MaskedTagsAbsentFromTrueTagEnv masked ctx) →
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
        hθwf hwf hric hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg

theorem ExternDeclBoundarySingleMaskedContract.of_emptyExternRegistry
    {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl : ExternImpl} :
    ExternDeclBoundarySingleMaskedContract masked ctx res predSat tm
      emptyExternRegistry d impl := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded μ ρ θ cf o _hθwf _hwf _hric
    _hreg _hmasked_none _hmasked_absent _hctxCons a pm _hwfcfg hrun _hpc
  exfalso
  have hlookup := ExternDeclBoundaryRun.lookup hrun
  simp [emptyExternRegistry] at hlookup

theorem ExternDeclBoundarySingleMaskedContract.of_spec
    {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning} {registry : ExternRegistry}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hspec : ExternBoundarySpec d impl) :
    ExternDeclBoundarySingleMaskedContract masked ctx res predSat tm registry d impl := by
  intro hpredlaws _hExtTyping hwfTm hTmBounded μ ρ θ cf o hθwf hwf hric
    hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hrun hpc
  have hregOrd : regimeConsistentWithCtx ctx :=
    regimeConsistentWithCtxMasked_unmask hreg hmasked_absent
  have hctxConsOrd :
      consistentWithRegime predSat ctx.regime ctx μ ρ θ :=
    consistentWithRegimeMasked_unmask hmasked_none hctxCons
  have hsingle :
      ExternBoundarySinglePost ctx res predSat tm θ μ cf o :=
    hspec.declSingle ctx res predSat tm hpredlaws hwfTm hTmBounded
      μ ρ θ cf o hθwf hwf hric hregOrd hctxConsOrd a pm registry hwfcfg hrun hpc
  exact
    ExternBoundarySinglePost.to_maskedRegParamPost
      (masked := masked) (ctx := ctx) (res := res) (predSat := predSat)
      (tm := tm) (θ := θ) (μ := μ) (ρ := ρ) (cf := cf) (o := o)
      (registry := registry)
      hθwf hwf hric hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hsingle

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
      ExternDeclBoundaryRun d impl₀ ctx res
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
          registry := registry } cf₀ o₀ →
      ExternDeclBoundaryRun d impl₁ ctx res
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
  intro hpredlaws _hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  exact
    hspec.declFR postExpr ctx res predSat tm hpredlaws hwfTm hTmBounded
      μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded
      hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree a₀ a₁ pm
      registry hwfcfg₀ hwfcfg₁ hrun₀ hrun₁

theorem ExternDeclBoundaryFRContract.of_emptyExternRegistry
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl₀ impl₁ : ExternImpl} :
    ExternDeclBoundaryFRContract ctx postExpr res predSat tm emptyExternRegistry
      d impl₀ impl₁ := by
  intro _hpredlaws _hExtTyping _hwfTm _hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ _hθ₀ _hθ₁ _hwf _htagBounded _hric₀ _hric₁ _hreg _hcwr₀ _hcwr₁
    _hagree a₀ a₁ pm _hwfcfg₀ _hwfcfg₁ hrun₀ _hrun₁
  exfalso
  have hlookup := ExternDeclBoundaryRun.lookup hrun₀
  simp [emptyExternRegistry] at hlookup

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

end TrustedRegistry

/-- `d` is an extern declaration synthetically exposed by an extern return
    descriptor.  This is what makes nested returned callables visible to the
    trusted-registry agreement layer. -/
inductive ExternDeclarationInReturn : ExternReturn → ExternId → ExternDeclaration → Prop where
  | nestedFn_here {innerId innerArg innerArgTyp innerRet innerEffects} :
      ExternDeclarationInReturn
        (ExternReturn.nestedFn innerId innerArg innerArgTyp innerRet innerEffects)
        innerId
        { id := innerId, kind := .fn, typ := innerArgTyp, argName := some innerArg,
          retSpec := some innerRet, effects := innerEffects,
          preds := collectExternPreds innerRet innerEffects }
  | nestedFn_inner {innerId innerArg innerArgTyp innerRet innerEffects id d} :
      ExternDeclarationInReturn innerRet id d →
      ExternDeclarationInReturn
        (ExternReturn.nestedFn innerId innerArg innerArgTyp innerRet innerEffects) id d
  | nestedPfn_here {innerId innerArg innerArgTyp innerRet} :
      ExternDeclarationInReturn
        (ExternReturn.nestedPfn innerId innerArg innerArgTyp innerRet)
        innerId
        { id := innerId, kind := .pfn, typ := innerArgTyp, argName := some innerArg,
          retSpec := some innerRet, effects := [], preds := collectExternPreds innerRet [] }
  | nestedPfn_inner {innerId innerArg innerArgTyp innerRet id d} :
      ExternDeclarationInReturn innerRet id d →
      ExternDeclarationInReturn
        (ExternReturn.nestedPfn innerId innerArg innerArgTyp innerRet) id d

/-- `d` is an extern declaration syntactically present in `e`. -/
inductive ExternDeclarationInProgram : Expr → ExternId → ExternDeclaration → Prop where
  | externVal {id typ poison pred} :
      ExternDeclarationInProgram (Expr.externVal id typ poison pred) id
        { id := id, kind := .val, typ := typ, argName := none, retSpec := none,
          effects := [], preds := [pred] }
  | externFn {id x argTyp retSpec eff} :
      ExternDeclarationInProgram (Expr.externFn id x argTyp retSpec eff) id
        { id := id, kind := .fn, typ := argTyp, argName := some x, retSpec := some retSpec,
          effects := eff, preds := collectExternPreds retSpec eff }
  | externFn_return {id x argTyp retSpec eff nestedId d} :
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationInProgram (Expr.externFn id x argTyp retSpec eff) nestedId d
  | externPfn {id x argTyp retSpec} :
      ExternDeclarationInProgram (Expr.externPfn id x argTyp retSpec) id
        { id := id, kind := .pfn, typ := argTyp, argName := some x, retSpec := some retSpec,
          effects := [], preds := collectExternPreds retSpec [] }
  | externPfn_return {id x argTyp retSpec nestedId d} :
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationInProgram (Expr.externPfn id x argTyp retSpec) nestedId d
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

theorem id_eq
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
  | pfn_body _ ih => exact ih
  | app_fun _ ih => exact ih
  | app_arg _ ih => exact ih

end ExternDeclarationInProgram

/-- Every extern declaration visible from `current` is also visible from
    `root`.  This is the root-program provenance relation used when local
    step proofs consume trusted-registry agreement for the top-level program. -/
def ExternDeclLift (root current : Expr) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationInProgram current id d →
    ExternDeclarationInProgram root id d

/-- Trusted entries may only implement declarations with the same id and
    declaration shape as the program. -/
def TrustedRegistryAgreesWithProgram (e : Expr) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationInProgram e id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d

theorem TrustedRegistryAgreesWithProgram.resolveDeclaration
    {e : Expr} {tr : TrustedRegistry} {id : ExternId}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog : ExternDeclarationInProgram e id d)
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      entry.decl = d := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  exact ⟨entry, hlookup, himpl, hagrees hprog hlookup⟩

def TrustedRegistryEntryMatchesFn
    (entry : TrustedExternEntry) (id : ExternId) (x : Name)
    (argTyp : Typ) (retSpec : ExternReturn) (effects : List Effect) : Prop :=
  entry.decl.id = id ∧
  entry.decl.kind = .fn ∧
  entry.decl.typ = argTyp ∧
  entry.decl.argName = some x ∧
  entry.decl.retSpec = some retSpec ∧
  entry.decl.effects = effects

def TrustedRegistryEntryMatchesPfn
    (entry : TrustedExternEntry) (id : ExternId) (x : Name)
    (argTyp : Typ) (retSpec : ExternReturn) : Prop :=
  entry.decl.id = id ∧
  entry.decl.kind = .pfn ∧
  entry.decl.typ = argTyp ∧
  entry.decl.argName = some x ∧
  entry.decl.retSpec = some retSpec

theorem TrustedRegistryAgreesWithProgram.resolveFnDeclaration
    {e : Expr} {tr : TrustedRegistry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hprog hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesFn, hdecl]

theorem TrustedRegistryAgreesWithProgram.resolvePfnDeclaration
    {e : Expr} {tr : TrustedRegistry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hprog hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesPfn, hdecl]

theorem ExternDeclBoundarySingleMaskedContract.of_trustedRegistry
    {tr : TrustedRegistry} {e : Expr} {id : ExternId}
    {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog : ExternDeclarationInProgram e id d) :
    ExternDeclBoundarySingleMaskedContract masked ctx res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl := by
  intro hpredlaws hExtTyping hwfTm hTmBounded μ ρ θ cf o hθwf hwf hric
    hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hrun hpc
  have hdid : d.id = id := ExternDeclarationInProgram.id_eq hprog
  have hlookupRun := ExternDeclBoundaryRun.lookup hrun
  have hlookupRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl := by
    simpa [hdid] using hlookupRun
  rcases
      TrustedRegistryAgreesWithProgram.resolveDeclaration hagrees hprog hlookupRuntime
    with ⟨entry, _hlookupEntry, himpl, hdecl⟩
  have hrunEntry :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf o := by
    simpa [hdecl, himpl] using hrun
  exact
    ExternDeclBoundarySingleMaskedContract.of_spec
      (masked := masked) (ctx := ctx) (res := res) (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded μ ρ θ cf o hθwf hwf hric
      hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hrunEntry hpc

theorem ExternDeclBoundaryFRContract.of_trustedRegistry
    {tr : TrustedRegistry} {e : Expr} {id : ExternId}
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl₀ impl₁ : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    (hprog : ExternDeclarationInProgram e id d) :
    ExternDeclBoundaryFRContract ctx postExpr res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl₀ impl₁ := by
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  have hdid : d.id = id := ExternDeclarationInProgram.id_eq hprog
  have hlookupRun₀ := ExternDeclBoundaryRun.lookup hrun₀
  have hlookupRun₁ := ExternDeclBoundaryRun.lookup hrun₁
  have hlookupRuntime₀ :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl₀ := by
    simpa [hdid] using hlookupRun₀
  have hlookupRuntime₁ :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl₁ := by
    simpa [hdid] using hlookupRun₁
  have himpl₁₀ : impl₁ = impl₀ :=
    Option.some.inj (hlookupRuntime₁.symm.trans hlookupRuntime₀)
  rcases
      TrustedRegistryAgreesWithProgram.resolveDeclaration hagrees hprog hlookupRuntime₀
    with ⟨entry, _hlookupEntry, himpl₀, hdecl⟩
  have hrunEntry₀ :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₀ o₀ := by
    simpa [hdecl, himpl₀] using hrun₀
  have hrunEntry₁ :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₁ o₁ := by
    simpa [hdecl, himpl₀, himpl₁₀] using hrun₁
  exact
    ExternDeclBoundaryFRContract.of_spec
      (ctx := ctx) (postExpr := postExpr) (res := res) (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
      o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrunEntry₀ hrunEntry₁

namespace TrustedRegistryEntryMatchesFn

theorem id_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.id = id :=
  h.1

theorem kind_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.kind = .fn :=
  h.2.1

theorem typ_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.typ = argTyp :=
  h.2.2.1

theorem argName_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.argName = some x :=
  h.2.2.2.1

theorem retSpec_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.retSpec = some retSpec :=
  h.2.2.2.2.1

theorem effects_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
    (h : TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects) :
    entry.decl.effects = effects :=
  h.2.2.2.2.2

end TrustedRegistryEntryMatchesFn

namespace TrustedRegistryEntryMatchesPfn

theorem id_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec) :
    entry.decl.id = id :=
  h.1

theorem kind_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec) :
    entry.decl.kind = .pfn :=
  h.2.1

theorem typ_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec) :
    entry.decl.typ = argTyp :=
  h.2.2.1

theorem argName_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec) :
    entry.decl.argName = some x :=
  h.2.2.2.1

theorem retSpec_eq
    {entry : TrustedExternEntry} {id : ExternId} {x : Name}
    {argTyp : Typ} {retSpec : ExternReturn}
    (h : TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec) :
    entry.decl.retSpec = some retSpec :=
  h.2.2.2.2

end TrustedRegistryEntryMatchesPfn

theorem ExternCallBoundaryRun.fn_of_match
    {entry : TrustedExternEntry} {id : ExternId} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect}
    {implFn : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address)}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value} {mem' : Memory} {addr' : Address}
    (hmatch :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects)
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
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec)
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

theorem TrustedRegistryAgreesWithProgram.callBoundaryRunFn
    {e : Expr} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {retSpec : ExternReturn}
    {effects : List Effect}
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects })
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
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.fn implFn) := by
    simpa [hregistry] using hGet
  rcases TrustedRegistryAgreesWithProgram.resolveFnDeclaration hagrees hprog hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem TrustedRegistryAgreesWithProgram.callBoundaryRunPfn
    {e : Expr} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithProgram e tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {retSpec : ExternReturn}
    (hprog :
      ExternDeclarationInProgram e id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] })
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
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.pfn implFn) := by
    simpa [hregistry] using hGet
  rcases TrustedRegistryAgreesWithProgram.resolvePfnDeclaration hagrees hprog hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

/-- Static impure closure-list members can be resolved to trusted entries.
    This is the bridge needed between `valueHasETyp.closure_extern` membership
    and future registry lookup. -/
def TrustedRegistryAgreesWithFnTClosures
    (tr : TrustedRegistry) (argTyp : Typ) (tcls : List FnTClosure) : Prop :=
  ∀ {id x retSpec effects capturedEnv},
    FnTClosure.extern id x retSpec effects capturedEnv ∈ tcls →
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects

/-- Static pure closure-list members can be resolved to trusted entries. -/
def TrustedRegistryAgreesWithPFnTClosures
    (tr : TrustedRegistry) (argTyp : Typ) (tcls : List PFnTClosure) : Prop :=
  ∀ {id x retSpec capturedEnv},
    PFnTClosure.extern id x retSpec capturedEnv ∈ tcls →
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec

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
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv} :
      FnTClosure.extern id x retSpec effects σcap ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .fn, typ := st1, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
  | arrow_extern_return {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {outerId nestedId : ExternId} {x : Name}
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv}
      {d : ExternDeclaration} :
      FnTClosure.extern outerId x retSpec effects σcap ∈ tcls →
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } nestedId d
  | arrow_extern_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {outerId : ExternId} {x : Name}
      {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      FnTClosure.extern outerId x retSpec effects σcap ∈ tcls →
      ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id d
  | arrow_regular_extern_body {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List FnTClosure} {id : ExternId} {x y : Name}
      {argTyp : Typ} {retSpec : ExternReturn} {effects : List Effect}
      {σcap : CapturedVarEnv} :
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
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
      {retSpec : ExternReturn} {σcap : CapturedVarEnv} :
      PFnTClosure.extern id x retSpec σcap ∈ tcls →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } id
        { id := id, kind := .pfn, typ := st1, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] }
  | parrow_extern_return {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {outerId nestedId : ExternId} {x : Name}
      {retSpec : ExternReturn} {σcap : CapturedVarEnv} {d : ExternDeclaration} :
      PFnTClosure.extern outerId x retSpec σcap ∈ tcls →
      ExternDeclarationInReturn retSpec nestedId d →
      ExternDeclarationReachableFromQTyp root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred } nestedId d
  | parrow_extern_captured {st1 st2 : Typ} {p qpoison : Poison} {qpred : Predicate}
      {tcls : List PFnTClosure} {outerId : ExternId} {x : Name}
      {retSpec : ExternReturn} {σcap : CapturedVarEnv}
      {id : ExternId} {d : ExternDeclaration} :
      PFnTClosure.extern outerId x retSpec σcap ∈ tcls →
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

theorem TrustedRegistryAgreesWithReachable.resolveDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry} {id : ExternId}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot id d)
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      entry.decl = d := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  exact ⟨entry, hlookup, himpl, hagrees hreachable hlookup⟩

theorem TrustedRegistryAgreesWithReachable.resolveFnDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hreachable hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesFn, hdecl]

theorem TrustedRegistryAgreesWithReachable.resolvePfnDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hreachable hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesPfn, hdecl]

theorem ExternDeclBoundarySingleMaskedContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {masked : Tag → Prop} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot d.id d) :
    ExternDeclBoundarySingleMaskedContract masked ctx res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl := by
  intro hpredlaws hExtTyping hwfTm hTmBounded μ ρ θ cf o hθwf hwf hric
    hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hrun hpc
  have hlookupRun := ExternDeclBoundaryRun.lookup hrun
  have hlookupRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl := hlookupRun
  rcases
      TrustedRegistryAgreesWithReachable.resolveDeclaration hagrees hreachable hlookupRuntime
    with ⟨entry, _hlookupEntry, himpl, hdecl⟩
  have hrunEntry :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf o := by
    simpa [hdecl, himpl] using hrun
  exact
    ExternDeclBoundarySingleMaskedContract.of_spec
      (masked := masked) (ctx := ctx) (res := res) (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded μ ρ θ cf o hθwf hwf hric
      hreg hmasked_none hmasked_absent hctxCons a pm hwfcfg hrunEntry hpc

theorem ExternDeclBoundaryFRContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl₀ impl₁ : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot d.id d) :
    ExternDeclBoundaryFRContract ctx postExpr res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl₀ impl₁ := by
  intro hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  have hlookupRun₀ := ExternDeclBoundaryRun.lookup hrun₀
  have hlookupRun₁ := ExternDeclBoundaryRun.lookup hrun₁
  have hlookupRuntime₀ :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl₀ := hlookupRun₀
  have hlookupRuntime₁ :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl₁ := hlookupRun₁
  have himpl₁₀ : impl₁ = impl₀ :=
    Option.some.inj (hlookupRuntime₁.symm.trans hlookupRuntime₀)
  rcases
      TrustedRegistryAgreesWithReachable.resolveDeclaration hagrees hreachable hlookupRuntime₀
    with ⟨entry, _hlookupEntry, himpl₀, hdecl⟩
  have hrunEntry₀ :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₀ o₀ := by
    simpa [hdecl, himpl₀] using hrun₀
  have hrunEntry₁ :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₁ o₁ := by
    simpa [hdecl, himpl₀, himpl₁₀] using hrun₁
  exact
    ExternDeclBoundaryFRContract.of_spec
      (ctx := ctx) (postExpr := postExpr) (res := res) (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
      o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hrunEntry₀ hrunEntry₁

theorem TrustedRegistryAgreesWithReachable.callBoundaryRunFn
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {retSpec : ExternReturn}
    {effects : List Effect}
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects })
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
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.fn implFn) := by
    simpa [hregistry] using hGet
  rcases
      TrustedRegistryAgreesWithReachable.resolveFnDeclaration
        hagrees hreachable hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem TrustedRegistryAgreesWithReachable.callBoundaryRunPfn
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {retSpec : ExternReturn}
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] })
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
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.pfn implFn) := by
    simpa [hregistry] using hGet
  rcases
      TrustedRegistryAgreesWithReachable.resolvePfnDeclaration
        hagrees hreachable hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

/-- Every extern declaration exposed by a qualified type is already in the
    initial reachable trust domain.  This is intentionally a lemma-level
    postcondition for typechecking, not an invariant threaded through the FR
    spine. -/
def QTypReachableFrom (root : Expr) (ctxRoot : TypeContext) (qt : QTyp) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot qt id d →
    ExternDeclarationReachableFromContext root ctxRoot id d

/-- Every extern declaration exposed by a captured type environment is already
    in the initial reachable trust domain. -/
def CapturedEnvReachableFrom
    (root : Expr) (ctxRoot : TypeContext) (σcap : CapturedVarEnv) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
    ExternDeclarationReachableFromContext root ctxRoot id d

/-- Context-level monotonicity invariant for reachable extern declarations.
    Every closure-bearing qualified type in the current variable type
    environment is covered by the initial `(root, ctxRoot)` reachable domain. -/
def ContextReachableFrom (root : Expr) (ctxRoot ctx : TypeContext) : Prop :=
  ∀ {x : Name} {qt : QTyp},
    ctx.varEnv.lookup x = some qt →
    QTypReachableFrom root ctxRoot qt

namespace ContextReachableFrom

theorem refl (root : Expr) (ctxRoot : TypeContext) :
    ContextReachableFrom root ctxRoot ctxRoot := by
  intro _x _qt hlookup _id _d hqt
  exact ExternDeclarationReachableFromContext.var hlookup hqt

theorem ctxAfter
    {root : Expr} {ctxRoot ctx : TypeContext} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx) :
    ContextReachableFrom root ctxRoot (ctxAfter ctx res) := by
  intro x qt hlookup
  exact hctx (by simpa [ctxAfter] using hlookup)

theorem lookup
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    {x : Name} {qt : QTyp}
    (hlookup : ctx.varEnv.lookup x = some qt) :
    QTypReachableFrom root ctxRoot qt :=
  hctx hlookup

theorem update
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    {x : Name} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ContextReachableFrom root ctxRoot { ctx with varEnv := VarTypeEnv.update ctx.varEnv x qt } := by
  intro y qt' hlookup
  by_cases hyx : y = x
  · subst y
    have hlookup_self :
        (VarTypeEnv.update ctx.varEnv x qt).lookup x = some qt :=
      VarTypeEnv_lookup_update_eq ctx.varEnv x qt
    have hqt_eq : qt' = qt := by
      rw [hlookup_self] at hlookup
      exact Eq.symm (Option.some.inj hlookup)
    subst qt'
    exact hqt
  · have hlookup_old : ctx.varEnv.lookup y = some qt' := by
      simpa [VarTypeEnv_lookup_update_ne ctx.varEnv x y qt hyx] using hlookup
    exact hctx hlookup_old

end ContextReachableFrom

namespace ExternDeclarationReachableFromCapturedEnv

private lemma list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) :
    l.lookup k = some v → (k, v) ∈ l := by
  intro hlookup
  induction l with
  | nil =>
      simp [List.lookup] at hlookup
  | cons hd tl ih =>
      cases hd with
      | mk k' v' =>
          by_cases hEq : k == k'
          · have hk : k = k' := LawfulBEq.eq_of_beq hEq
            simp [List.lookup, hEq] at hlookup
            subst hk
            subst hlookup
            simp
          · simp [List.lookup, hEq] at hlookup
            exact List.mem_cons_of_mem _ (ih hlookup)

theorem of_mem
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {x : Name} {qt : QTyp} {id : ExternId} {d : ExternDeclaration}
    (hmem : (x, qt) ∈ σcap)
    (hqt : ExternDeclarationReachableFromQTyp root ctxRoot qt id d) :
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d := by
  induction σcap with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk y qt' =>
          cases hmem with
          | head =>
              exact ExternDeclarationReachableFromCapturedEnv.head hqt
          | tail _ htail =>
              exact ExternDeclarationReachableFromCapturedEnv.tail (ih htail)

theorem of_list_lookup
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {x : Name} {qt : QTyp} {id : ExternId} {d : ExternDeclaration}
    (hlookup : σcap.lookup x = some qt)
    (hqt : ExternDeclarationReachableFromQTyp root ctxRoot qt id d) :
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d :=
  of_mem (list_lookup_mem σcap x qt hlookup) hqt

theorem exists_mem
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {id : ExternId} {d : ExternDeclaration}
    (hcap : ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d) :
    ∃ x qt,
      (x, qt) ∈ σcap ∧
      ExternDeclarationReachableFromQTyp root ctxRoot qt id d := by
  induction σcap with
  | nil =>
      cases hcap
  | cons hd tl ih =>
      cases hd with
      | mk x qt =>
          cases hcap with
          | head hqt =>
              exact ⟨x, qt, by simp, hqt⟩
          | tail htail =>
              rcases ih htail with ⟨y, qty, hmem, hqt⟩
              exact ⟨y, qty, by simp [hmem], hqt⟩

end ExternDeclarationReachableFromCapturedEnv

namespace CapturedEnvReachableFrom

theorem of_toCaptured
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx) :
    CapturedEnvReachableFrom root ctxRoot (VarTypeEnv.toCaptured ctx.varEnv) := by
  intro _id _d hcap
  rcases ExternDeclarationReachableFromCapturedEnv.exists_mem hcap with
    ⟨x, qt, hmem, hqt⟩
  have hlookup := VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv x qt hmem
  exact hctx hlookup hqt

theorem qtyp_of_ofCaptured_lookup
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    {x : Name} {qt : QTyp}
    (hlookup : (VarTypeEnv.ofCaptured σcap).lookup x = some qt) :
    QTypReachableFrom root ctxRoot qt := by
  intro _id _d hqt
  have hlist := list_lookup_of_ofCaptured_lookup σcap x qt hlookup
  exact hcap (ExternDeclarationReachableFromCapturedEnv.of_list_lookup hlist hqt)

theorem context_ofCaptured
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    (ctx : TypeContext) :
    ContextReachableFrom root ctxRoot { ctx with varEnv := VarTypeEnv.ofCaptured σcap } := by
  intro _x _qt hlookup
  exact qtyp_of_ofCaptured_lookup hcap (by simpa using hlookup)

end CapturedEnvReachableFrom

namespace QTypReachableFrom

theorem arrow_redecorate
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison₁, pred := qpred₁ } := by
  intro _id _d hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_body hmem hprog)
  | arrow_regular_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmem hcap)
  | arrow_extern_member hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_member hmem)
  | arrow_extern_return hmem hret =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_return hmem hret)
  | arrow_extern_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmem hcap)
  | arrow_regular_extern_body hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmem)

theorem parrow_redecorate
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison₁, pred := qpred₁ } := by
  intro _id _d hreach
  cases hreach with
  | parrow_regular_body hmem hprog =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_body hmem hprog)
  | parrow_regular_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmem hcap)
  | parrow_extern_member hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_member hmem)
  | parrow_extern_return hmem hret =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_return hmem hret)
  | parrow_extern_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmem hcap)

theorem fn_regular_body
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : Expr} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.regular x body σcap ∈ tcls)
    {id : ExternId} {d : ExternDeclaration}
    (hprog : ExternDeclarationInProgram body id d) :
    ExternDeclarationReachableFromContext root ctxRoot id d :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_regular_body hmem hprog)

theorem fn_regular_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : Expr} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.regular x body σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmem hcap)

theorem fn_extern_member
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.extern id x retSpec effects σcap ∈ tcls) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .fn, typ := st1, argName := some x,
        retSpec := some retSpec, effects := effects,
        preds := collectExternPreds retSpec effects } :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_extern_member hmem)

theorem fn_extern_return
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId nestedId : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.extern outerId x retSpec effects σcap ∈ tcls)
    {d : ExternDeclaration}
    (hret : ExternDeclarationInReturn retSpec nestedId d) :
    ExternDeclarationReachableFromContext root ctxRoot nestedId d :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_extern_return hmem hret)

theorem fn_extern_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.extern outerId x retSpec effects σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmem hcap)

theorem fn_regular_extern_body
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x y : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect} {σcap : CapturedVarEnv}
    (hmem :
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .fn, typ := argTyp, argName := some x,
        retSpec := some retSpec, effects := effects,
        preds := collectExternPreds retSpec effects } :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmem)

theorem pfn_regular_body
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.regular x body σcap ∈ tcls)
    {id : ExternId} {d : ExternDeclaration}
    (hprog : ExternDeclarationInProgram (PExpr.toExpr body) id d) :
    ExternDeclarationReachableFromContext root ctxRoot id d :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_regular_body hmem hprog)

theorem pfn_regular_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.regular x body σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmem hcap)

theorem pfn_extern_member
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x : Name} {retSpec : ExternReturn} {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.extern id x retSpec σcap ∈ tcls) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .pfn, typ := st1, argName := some x,
        retSpec := some retSpec, effects := [],
        preds := collectExternPreds retSpec [] } :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_extern_member hmem)

theorem pfn_extern_return
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId nestedId : ExternId} {x : Name} {retSpec : ExternReturn}
    {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.extern outerId x retSpec σcap ∈ tcls)
    {d : ExternDeclaration}
    (hret : ExternDeclarationInReturn retSpec nestedId d) :
    ExternDeclarationReachableFromContext root ctxRoot nestedId d :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_extern_return hmem hret)

theorem pfn_extern_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId : ExternId} {x : Name} {retSpec : ExternReturn}
    {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.extern outerId x retSpec σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmem hcap)

end QTypReachableFrom

/-- Root-scoped provenance needed to turn app closure-list membership into
    trusted extern-call providers.  This is intentionally separate from the
    boundary contract: concrete extern boundaries stay body-local, while the
    app proof supplies the source/typechecking provenance that says which
    registry entries can be used. -/
structure TrustedRegistryAppClosureProvenance
    (root : Expr) (tr : TrustedRegistry) : Prop where
  fnBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {x : Name}
      {body : Expr} {σcap : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      FnTClosure.regular x body σcap ∈ tcls →
      ExternDeclLift root body
  pfnBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List PFnTClosure} {x : Name}
      {body : PExpr} {σcap : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppPfnClosureListFromTypecheck ctx e1 e2 res tcls →
      PFnTClosure.regular x body σcap ∈ tcls →
      ExternDeclLift root (PExpr.toExpr body)
  fnExternMember :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {argTyp : Typ}
      {id : ExternId} {x : Name} {retSpec : ExternReturn}
      {effects : List Effect} {capturedEnv : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      FnTClosure.extern id x retSpec effects capturedEnv ∈ tcls →
      ExternDeclarationInProgram root id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
  fnRegularExternBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {argTyp : Typ}
      {id : ExternId} {x y : Name} {retSpec : ExternReturn}
      {effects : List Effect} {capturedEnv : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
      ExternDeclarationInProgram root id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
  pfnExternMember :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List PFnTClosure} {argTyp : Typ}
      {id : ExternId} {x : Name} {retSpec : ExternReturn}
      {capturedEnv : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppPfnClosureListFromTypecheck ctx e1 e2 res tcls →
      PFnTClosure.extern id x retSpec capturedEnv ∈ tcls →
      ExternDeclarationInProgram root id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [] }

theorem TrustedRegistryAgreesWithFnTClosures.resolve
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv}
    (hmem : FnTClosure.extern id x retSpec effects capturedEnv ∈ tcls) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects := by
  rcases hagrees hmem with ⟨entry, hlookup, hmatch⟩
  exact ⟨entry, hlookup, TrustedRegistry.lookup_toRuntimeRegistry hlookup, hmatch⟩

theorem TrustedRegistryAgreesWithPFnTClosures.resolve
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv}
    (hmem : PFnTClosure.extern id x retSpec capturedEnv ∈ tcls) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec := by
  rcases hagrees hmem with ⟨entry, hlookup, hmatch⟩
  exact ⟨entry, hlookup, TrustedRegistry.lookup_toRuntimeRegistry hlookup, hmatch⟩

theorem TrustedRegistryAgreesWithFnTClosures.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {capturedEnv : CapturedVarEnv}
    (hmem : FnTClosure.extern id x retSpec effects capturedEnv ∈ tcls)
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
  rcases TrustedRegistryAgreesWithFnTClosures.resolve hagrees hmem with
    ⟨entry, hlookup, hlookupRuntime, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hlookupRuntime
  have hGetDecl : callEntry.callConfig.registry.get? entry.decl.id =
      some (ExternImpl.fn implFn) := by
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hGet
  have himpl : entry.impl = ExternImpl.fn implFn := by
    exact Option.some.inj (hlookupCall.symm.trans hGetDecl)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem TrustedRegistryAgreesWithPFnTClosures.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv}
    (hmem : PFnTClosure.extern id x retSpec capturedEnv ∈ tcls)
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
  rcases TrustedRegistryAgreesWithPFnTClosures.resolve hagrees hmem with
    ⟨entry, hlookup, hlookupRuntime, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hlookupRuntime
  have hGetDecl : callEntry.callConfig.registry.get? entry.decl.id =
      some (ExternImpl.pfn implFn) := by
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hGet
  have himpl : entry.impl = ExternImpl.pfn implFn := by
    exact Option.some.inj (hlookupCall.symm.trans hGetDecl)
  exact
    ⟨entry, hlookup,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩
