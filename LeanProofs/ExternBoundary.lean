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
  | fn_extern_body_runtime {x argTyp retTyp id y bodyArgTyp retSpec effects} :
      ExternDeclarationInProgram
        (Expr.fn x argTyp (Expr.externFn id y bodyArgTyp retSpec effects) retTyp) id
        { id := id, kind := .fn, typ := bodyArgTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects }
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
  | fn_extern_body_runtime => rfl
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

theorem of_same_varEnv
    {root : Expr} {ctxRoot ctx ctx' : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hvar : ctx'.varEnv = ctx.varEnv) :
    ContextReachableFrom root ctxRoot ctx' := by
  intro x qt hlookup
  exact hctx (by simpa [hvar] using hlookup)

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

namespace ContextReachableFrom

theorem ofCaptured_update
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    (ctx : TypeContext)
    {x : Name} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ContextReachableFrom root ctxRoot
      { ctx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x qt } := by
  exact ContextReachableFrom.update
    (CapturedEnvReachableFrom.context_ofCaptured hcap ctx) hqt

end ContextReachableFrom

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

theorem etyp_redecorate
    {root : Expr} {ctxRoot : TypeContext} {etyp : ETyp}
    {qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := etyp, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := etyp, poison := qpoison₁, pred := qpred₁ } := by
  cases etyp with
  | int =>
      intro _id _d hreach
      cases hreach
  | bool =>
      intro _id _d hreach
      cases hreach
  | unit =>
      intro _id _d hreach
      cases hreach
  | string =>
      intro _id _d hreach
      cases hreach
  | ref _ls =>
      intro _id _d hreach
      cases hreach
  | arrow st1 st2 p tcls =>
      exact arrow_redecorate hqt
  | parrow st1 st2 p tcls =>
      exact parrow_redecorate hqt

theorem of_eq_redecorate
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {etyp : ETyp} {qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (heq : qt = { etyp := etyp, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
      { etyp := etyp, poison := qpoison₁, pred := qpred₁ } := by
  subst qt
  exact etyp_redecorate hqt

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

theorem of_fn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.fn x st1 body st2)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.arrow st1 st2 ctx.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _id _d hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.fn_body hprog)
      | tail _ htail => cases htail
  | arrow_regular_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | arrow_extern_member hmem =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_return hmem _hret =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_regular_extern_body hmem =>
      cases hmem with
      | head => exact hcurrent ExternDeclarationInProgram.fn_extern_body_runtime
      | tail _ htail => cases htail

theorem of_pfn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : PExpr}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.pfn x st1 (PExpr.toExpr body) st2)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.parrow st1 st2 ctx.pc
            [PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _id _d hreach
  cases hreach with
  | parrow_regular_body hmem hprog =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.pfn_body hprog)
      | tail _ htail => cases htail
  | parrow_regular_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | parrow_extern_member hmem =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_return hmem _hret =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail

theorem of_externFn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externFn id x argTyp retSpec effects)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.arrow argTyp (parseReturnType retSpec) ctx.pc
            [FnTClosure.extern id x retSpec effects
              (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _nestedId _d hreach
  cases hreach with
  | arrow_regular_body hmem _hprog =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_regular_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_member hmem =>
      cases hmem with
      | head => exact hcurrent ExternDeclarationInProgram.externFn
      | tail _ htail => cases htail
  | arrow_extern_return hmem hret =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.externFn_return hret)
      | tail _ htail => cases htail
  | arrow_extern_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | arrow_regular_extern_body hmem =>
      cases hmem with
      | tail _ htail => cases htail

theorem of_externPfn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externPfn id x argTyp retSpec)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.parrow argTyp (parseReturnType retSpec) ctx.pc
            [PFnTClosure.extern id x retSpec
              (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _nestedId _d hreach
  cases hreach with
  | parrow_regular_body hmem _hprog =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_regular_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_member hmem =>
      cases hmem with
      | head => exact hcurrent ExternDeclarationInProgram.externPfn
      | tail _ htail => cases htail
  | parrow_extern_return hmem hret =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.externPfn_return hret)
      | tail _ htail => cases htail
  | parrow_extern_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail

theorem of_typecheckFn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.fn x st1 body st2))
    (htc : typecheckFn ctx x st1 body st2 = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  simp [typecheckFn, pure, Except.pure] at htc
  cases htc
  exact of_fn_result hctx hcurrent

theorem of_typecheckPfn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.pfn x st1 body st2))
    (htc : typecheckPfn ctx x st1 body st2 = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody, bind, Except.bind] at htc
  | ok pbody =>
      simp [typecheckPfn, hbody, bind, Except.bind, pure, Except.pure] at htc
      cases htc
      have hsome : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hbody_eq : PExpr.toExpr pbody = body :=
        PExpr_toExpr_of_toPExpr?_some body pbody hsome
      rw [← hbody_eq] at hcurrent
      change ∀ {id : ExternId} {d : ExternDeclaration},
        ExternDeclarationReachableFromQTyp root ctxRoot
          { etyp := ETyp.parrow st1 st2 ctx.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctx.varEnv)],
            poison := ctx.pc, pred := Predicate.noPred } id d →
        ExternDeclarationReachableFromContext root ctxRoot id d
      exact of_pfn_result hctx hcurrent

theorem of_typecheckExternFn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {effects : List Effect} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externFn id x argTyp retSpec effects))
    (htc : typecheckExternFn ctx id x argTyp retSpec effects = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  have hres :=
    typecheckExternFn_ok_res_eq ctx id x argTyp retSpec effects res htc
  subst res
  change ∀ {nestedId : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot
      { etyp := ETyp.arrow argTyp (parseReturnType retSpec) ctx.pc
          [FnTClosure.extern id x retSpec effects
            (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc, pred := Predicate.noPred } nestedId d →
    ExternDeclarationReachableFromContext root ctxRoot nestedId d
  exact of_externFn_result hctx hcurrent

theorem of_typecheckExternPfn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {retSpec : ExternReturn} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externPfn id x argTyp retSpec))
    (htc : typecheckExternPfn ctx id x argTyp retSpec = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  have hres :=
    typecheckExternPfn_ok_res_eq ctx id x argTyp retSpec res htc
  subst res
  change ∀ {nestedId : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot
      { etyp := ETyp.parrow argTyp (parseReturnType retSpec) ctx.pc
          [PFnTClosure.extern id x retSpec
            (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc, pred := Predicate.noPred } nestedId d →
    ExternDeclarationReachableFromContext root ctxRoot nestedId d
  exact of_externPfn_result hctx hcurrent

theorem of_non_function_etyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    (hfun : qt.etyp.isFunctionType = false) :
    QTypReachableFrom root ctxRoot qt := by
  intro _id _d hreach
  cases qt with
  | mk etyp poison pred =>
      cases etyp <;> simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hfun
      all_goals cases hreach

private def ETypReachableFrom (root : Expr) (ctxRoot : TypeContext) (etyp : ETyp) : Prop :=
  ∀ {qpoison : Poison} {qpred : Predicate},
    QTypReachableFrom root ctxRoot { etyp := etyp, poison := qpoison, pred := qpred }

private theorem ETypReachableFrom.of_qtyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ETypReachableFrom root ctxRoot qt.etyp := by
  cases qt with
  | mk etyp qpoison qpred =>
      intro _qpoison' _qpred'
      exact QTypReachableFrom.etyp_redecorate hqt

private theorem fnArrowSource
    {st1a st2a st1 st2 : Typ} {pa : Poison}
    {tcls1 : List FnTClosure} {tcl : FnTClosure}
    (hst1 : st1a = st1) (hst2 : st2a = st2)
    (hmem : tcl ∈ tcls1) :
    ∃ psrc tclsSrc,
      ETyp.arrow st1a st2a pa tcls1 = ETyp.arrow st1 st2 psrc tclsSrc ∧
      tcl ∈ tclsSrc := by
  refine ⟨pa, tcls1, ?_, hmem⟩
  rw [hst1, hst2]

private theorem pfnArrowSource
    {st1a st2a st1 st2 : Typ} {pa : Poison}
    {tcls1 : List PFnTClosure} {tcl : PFnTClosure}
    (hst1 : st1a = st1) (hst2 : st2a = st2)
    (hmem : tcl ∈ tcls1) :
    ∃ psrc tclsSrc,
      ETyp.parrow st1a st2a pa tcls1 = ETyp.parrow st1 st2 psrc tclsSrc ∧
      tcl ∈ tclsSrc := by
  refine ⟨pa, tcls1, ?_, hmem⟩
  rw [hst1, hst2]

private theorem typPair_eq_of_and_beq
    {st1a st1b st2a st2b : Typ}
    (hshape : (st1a == st1b && st2a == st2b) = true) :
    st1a = st1b ∧ st2a = st2b := by
  rw [Bool.and_eq_true] at hshape
  rcases hshape with ⟨h1, h2⟩
  exact ⟨LawfulBEq.eq_of_beq h1, LawfulBEq.eq_of_beq h2⟩

private theorem joinETyps_arrow_member_source
    {etyp1 etyp2 : ETyp} {p1 p2 : Poison}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure} {tcl : FnTClosure}
    (heq : joinETyps etyp1 etyp2 p1 p2 = ETyp.arrow st1 st2 p tcls)
    (hmem : tcl ∈ tcls) :
    (∃ psrc tclsSrc,
      etyp1 = ETyp.arrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) ∨
    (∃ psrc tclsSrc,
      etyp2 = ETyp.arrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) := by
  cases etyp1 with
  | int => cases etyp2 <;> simp [joinETyps] at heq
  | bool => cases etyp2 <;> simp [joinETyps] at heq
  | unit => cases etyp2 <;> simp [joinETyps] at heq
  | string => cases etyp2 <;> simp [joinETyps] at heq
  | ref ls1 => cases etyp2 <;> simp [joinETyps] at heq
  | parrow st1p st2p pp tclsp =>
      cases etyp2 with
      | parrow st1b st2b pb tcls2 =>
          by_cases hshape : st1p == st1b && st2p == st2b
          · simp [joinETyps, hshape] at heq
          · simp [joinETyps, hshape] at heq
      | int => simp [joinETyps] at heq
      | bool => simp [joinETyps] at heq
      | unit => simp [joinETyps] at heq
      | string => simp [joinETyps] at heq
      | ref ls => simp [joinETyps] at heq
      | arrow st1f st2f pf tclsf => simp [joinETyps] at heq
  | arrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | arrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : mergeFnTClosures tcls1 tcls2 = tcls := heq.2.2.2
            have hmemMerge : tcl ∈ mergeFnTClosures tcls1 tcls2 := by
              simpa [htcls] using hmem
            rcases mem_mergeFnTClosures_inv tcls1 tcls2 tcl hmemMerge with hleft | hright
            · exact Or.inl (fnArrowSource hst1 hst2 hleft)
            · rcases typPair_eq_of_and_beq hshape with ⟨hst1ab, hst2ab⟩
              have hst1b : st1b = st1 := by rw [← hst1ab, hst1]
              have hst2b : st2b = st2 := by rw [← hst2ab, hst2]
              exact Or.inr (fnArrowSource hst1b hst2b hright)
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : tcls1 = tcls := heq.2.2.2
            have hmem1 : tcl ∈ tcls1 := by simpa [htcls] using hmem
            exact Or.inl (fnArrowSource hst1 hst2 hmem1)
      | int =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | bool =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | unit =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | string =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | ref ls =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | parrow st1p st2p pp tclsp =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)

private theorem joinETyps_parrow_member_source
    {etyp1 etyp2 : ETyp} {p1 p2 : Poison}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure} {tcl : PFnTClosure}
    (heq : joinETyps etyp1 etyp2 p1 p2 = ETyp.parrow st1 st2 p tcls)
    (hmem : tcl ∈ tcls) :
    (∃ psrc tclsSrc,
      etyp1 = ETyp.parrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) ∨
    (∃ psrc tclsSrc,
      etyp2 = ETyp.parrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) := by
  cases etyp1 with
  | int => cases etyp2 <;> simp [joinETyps] at heq
  | bool => cases etyp2 <;> simp [joinETyps] at heq
  | unit => cases etyp2 <;> simp [joinETyps] at heq
  | string => cases etyp2 <;> simp [joinETyps] at heq
  | ref ls1 => cases etyp2 <;> simp [joinETyps] at heq
  | arrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | arrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
          · simp [joinETyps, hshape] at heq
      | int => simp [joinETyps] at heq
      | bool => simp [joinETyps] at heq
      | unit => simp [joinETyps] at heq
      | string => simp [joinETyps] at heq
      | ref ls => simp [joinETyps] at heq
      | parrow st1p st2p pp tclsp => simp [joinETyps] at heq
  | parrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | parrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : mergePFnTClosures tcls1 tcls2 = tcls := heq.2.2.2
            have hmemMerge : tcl ∈ mergePFnTClosures tcls1 tcls2 := by
              simpa [htcls] using hmem
            rcases mem_mergePFnTClosures_inv tcls1 tcls2 tcl hmemMerge with hleft | hright
            · exact Or.inl (pfnArrowSource hst1 hst2 hleft)
            · rcases typPair_eq_of_and_beq hshape with ⟨hst1ab, hst2ab⟩
              have hst1b : st1b = st1 := by rw [← hst1ab, hst1]
              have hst2b : st2b = st2 := by rw [← hst2ab, hst2]
              exact Or.inr (pfnArrowSource hst1b hst2b hright)
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : tcls1 = tcls := heq.2.2.2
            have hmem1 : tcl ∈ tcls1 := by simpa [htcls] using hmem
            exact Or.inl (pfnArrowSource hst1 hst2 hmem1)
      | int =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | bool =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | unit =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | string =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | ref ls =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | arrow st1f st2f pf tclsf =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)

private theorem ETypReachableFrom.of_joinETyps
    {root : Expr} {ctxRoot : TypeContext} {etyp1 etyp2 : ETyp}
    {p1 p2 : Poison}
    (h1 : ETypReachableFrom root ctxRoot etyp1)
    (h2 : ETypReachableFrom root ctxRoot etyp2) :
    ETypReachableFrom root ctxRoot (_root_.joinETyps etyp1 etyp2 p1 p2) := by
  intro qpoison qpred id d hreach
  generalize hetyp : _root_.joinETyps etyp1 etyp2 p1 p2 = etyp at hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_body hmemSrc hprog)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_body hmemSrc hprog)
  | arrow_regular_captured hmem hcap =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmemSrc hcap)
  | arrow_extern_member hmem =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_member hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_member hmemSrc)
  | arrow_extern_return hmem hret =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_return hmemSrc hret)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_return hmemSrc hret)
  | arrow_extern_captured hmem hcap =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmemSrc hcap)
  | arrow_regular_extern_body hmem =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmemSrc)
  | parrow_regular_body hmem hprog =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_body hmemSrc hprog)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_body hmemSrc hprog)
  | parrow_regular_captured hmem hcap =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmemSrc hcap)
  | parrow_extern_member hmem =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_member hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_member hmemSrc)
  | parrow_extern_return hmem hret =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_return hmemSrc hret)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_return hmemSrc hret)
  | parrow_extern_captured hmem hcap =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmemSrc hcap)

theorem of_joinETyps
    {root : Expr} {ctxRoot : TypeContext} {qt1 qt2 : QTyp}
    (h1 : QTypReachableFrom root ctxRoot qt1)
    (h2 : QTypReachableFrom root ctxRoot qt2) :
    QTypReachableFrom root ctxRoot
      { etyp := _root_.joinETyps qt1.etyp qt2.etyp qt1.poison qt2.poison,
        poison := joinPoison qt1.poison qt2.poison,
        pred := joinPredicates qt1.pred qt2.pred } := by
  exact ETypReachableFrom.of_joinETyps
    (ETypReachableFrom.of_qtyp h1) (ETypReachableFrom.of_qtyp h2)

theorem of_joinTypeResults
    {root : Expr} {ctxRoot : TypeContext} {ctx : TypeContext}
    {first res : TypeResult} {rest : List TypeResult}
    (hfirst : QTypReachableFrom root ctxRoot first.qualType)
    (hrest : ∀ result ∈ rest,
      QTypReachableFrom root ctxRoot result.qualType)
    (hjoin : joinTypeResults ctx first rest = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult →
        Except String
          (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (_root_.joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have hfoldReach :
      ∀ (rs : List TypeResult)
        (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs = .ok acc' →
        ETypReachableFrom root ctxRoot acc.1 →
        (∀ result ∈ rs, QTypReachableFrom root ctxRoot result.qualType) →
        ETypReachableFrom root ctxRoot acc'.1 := by
    intro rs
    induction rs with
    | nil =>
        intro acc acc' hfold hacc _hrest
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        intro qpoison qpred id d hreach
        exact hacc (qpoison := qpoison) (qpred := qpred) hreach
    | cons result rs ih =>
        intro acc acc' hfold hacc hrest'
        cases hqt : result.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqt, bind, Except.bind] at hfold
            have hresReachRaw : QTypReachableFrom root ctxRoot result.qualType :=
              hrest' result (by simp)
            have hresReach :
                QTypReachableFrom root ctxRoot
                  { etyp := resEtyp, poison := resPoison, pred := resPred } := by
              intro id d hreach
              exact hresReachRaw (by simpa [hqt] using hreach)
            have hresEtypReach : ETypReachableFrom root ctxRoot resEtyp := by
              intro qpoison qpred id d hreach
              exact (QTypReachableFrom.etyp_redecorate hresReach) hreach
            have hstepReach :
                ETypReachableFrom root ctxRoot
                  (_root_.joinETyps acc.1 resEtyp acc.2.2.1 resPoison) :=
              ETypReachableFrom.of_joinETyps hacc hresEtypReach
            have htail :
                ∀ tailResult ∈ rs,
                  QTypReachableFrom root ctxRoot tailResult.qualType := by
              intro tailResult hmem
              exact hrest' tailResult (by simp [hmem])
            intro qpoison qpred id d hreach
            exact (ih _ _ hfold hstepReach htail) hreach
  cases hqtFirst : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqtFirst, bind, Except.bind, pure, Except.pure] at hjoin
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++
                      toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv',
                  first.regime', first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok acc =>
              erw [hfold] at hjoin
              simp at hjoin
              cases hjoin
              have hfirstE : ETypReachableFrom root ctxRoot etyp := by
                have hfirst' :
                    QTypReachableFrom root ctxRoot
                      { etyp := etyp, poison := poison, pred := pred } := by
                  intro id d hreach
                  exact hfirst (by simpa [hqtFirst] using hreach)
                intro qpoison qpred id d hreach
                exact (QTypReachableFrom.etyp_redecorate hfirst') hreach
              have haccReach : ETypReachableFrom root ctxRoot acc.1 :=
                hfoldReach rest
                (etyp, first.memEnv', poison, pred, first.tagEnv',
                  first.regime', first.nextLoc', first.nextTag')
                acc hfold
                hfirstE
                hrest
              intro id d hreach
              exact haccReach hreach

theorem with_etyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {qpoison : Poison} {qpred : Predicate}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    QTypReachableFrom root ctxRoot
      { etyp := qt.etyp, poison := qpoison, pred := qpred } :=
  ETypReachableFrom.of_qtyp hqt

theorem of_arrow_etyp_eq
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls) :
    QTypReachableFrom root ctxRoot
      { etyp := ETyp.arrow st1 st2 p tcls,
        poison := qt.poison, pred := qt.pred } := by
  cases hres : qt with
  | mk etyp qpoison qpred =>
      have harrow : etyp = ETyp.arrow st1 st2 p tcls := by
        simpa [hres] using hetyp
      subst etyp
      intro id d hreach
      exact hqt (by simpa [hres] using hreach)

theorem of_parrow_etyp_eq
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls) :
    QTypReachableFrom root ctxRoot
      { etyp := ETyp.parrow st1 st2 p tcls,
        poison := qt.poison, pred := qt.pred } := by
  cases hres : qt with
  | mk etyp qpoison qpred =>
      have hparrow : etyp = ETyp.parrow st1 st2 p tcls := by
        simpa [hres] using hetyp
      subst etyp
      intro id d hreach
      exact hqt (by simpa [hres] using hreach)

theorem of_typecheckVar
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (htc : typecheckVar ctx x = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  unfold typecheckVar at htc
  cases hlookup : ctx.varEnv.lookup x with
  | none =>
      simp [hlookup] at htc
  | some qt =>
      have hqt : QTypReachableFrom root ctxRoot qt :=
        ContextReachableFrom.lookup hctx hlookup
      cases qt with
      | mk etyp poison pred =>
          have hred (qpoison : Poison) (qpred : Predicate) :
              QTypReachableFrom root ctxRoot
                { etyp := etyp, poison := qpoison, pred := qpred } := by
            unfold QTypReachableFrom
            intro id d hreach
            exact (QTypReachableFrom.etyp_redecorate hqt) hreach
          cases pred with
          | noPred =>
              simp [hlookup, pure, Except.pure] at htc
              cases htc
              change QTypReachableFrom root ctxRoot
                { etyp := etyp, poison := joinPoison ctx.pc poison, pred := Predicate.noPred }
              exact hred (joinPoison ctx.pc poison) Predicate.noPred
          | guardOnly k =>
              show QTypReachableFrom root ctxRoot res.qualType
              by_cases hfun : etyp.isFunctionType = true
              · simp [hlookup, hfun] at htc
                cases htc
              · have hfunFalse : etyp.isFunctionType = false := by
                  cases hif : etyp.isFunctionType <;> simp [hif] at hfun ⊢
                cases htag : ctx.tagEnv[k]? with
                | none =>
                    simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                    cases htc
                    intro hreach
                    exact (hred (joinPoison ctx.pc poison) (Predicate.guardOnly k)) hreach
                | some tv =>
                    cases tv with
                    | mk b deps =>
                        cases b
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred true Predicate.noPred) hreach
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred ctx.pc Predicate.noPred) hreach
          | guardClosure k arg body env =>
              show QTypReachableFrom root ctxRoot res.qualType
              by_cases hfun : etyp.isFunctionType = true
              · simp [hlookup, hfun] at htc
                cases htc
              · have hfunFalse : etyp.isFunctionType = false := by
                  cases hif : etyp.isFunctionType <;> simp [hif] at hfun ⊢
                cases htag : ctx.tagEnv[k]? with
                | none =>
                    simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                    cases htc
                    intro hreach
                    exact
                      (hred (joinPoison ctx.pc poison)
                        (Predicate.guardClosure k arg body env)) hreach
                | some tv =>
                    cases tv with
                    | mk b deps =>
                        cases b
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred true Predicate.noPred) hreach
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred ctx.pc Predicate.noPred) hreach

end QTypReachableFrom

namespace ContextReachableFrom

theorem fnBody_of_arrow_member
    {root : Expr} {ctxRoot bodyCtx : TypeContext}
    {result1 : TypeResult} {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    {x : Name} {body : Expr} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hqtFn : QTypReachableFrom root ctxRoot result1.qualType)
    (hetyp : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
    (hmem : FnTClosure.regular x body σcap ∈ tcls)
    (harg : QTypReachableFrom root ctxRoot argQt)
    (hvar :
      bodyCtx.varEnv = VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt) :
    ContextReachableFrom root ctxRoot bodyCtx := by
  have hqtArrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } := by
    cases hres : result1.qualType with
    | mk etyp qpoison qpred =>
        have harrow : etyp = ETyp.arrow st1 st2 p tcls := by
          simpa [hres] using hetyp
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              result1.qualType id d := by
          simpa [hres] using hreach
        exact hqtFn hreach'
  have hcap : CapturedEnvReachableFrom root ctxRoot σcap :=
    QTypReachableFrom.fn_regular_captured hqtArrow hmem
  have hctx :
      ContextReachableFrom root ctxRoot
        { bodyCtx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } :=
    ContextReachableFrom.ofCaptured_update hcap bodyCtx harg
  intro y qt hlookup
  exact hctx (by simpa [hvar] using hlookup)

theorem pfnBody_of_parrow_member
    {root : Expr} {ctxRoot bodyCtx : TypeContext}
    {result1 : TypeResult} {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hqtPfn : QTypReachableFrom root ctxRoot result1.qualType)
    (hetyp : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
    (hmem : PFnTClosure.regular x body σcap ∈ tcls)
    (harg : QTypReachableFrom root ctxRoot argQt)
    (hvar :
      bodyCtx.varEnv = VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt) :
    ContextReachableFrom root ctxRoot bodyCtx := by
  have hqtParrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } := by
    cases hres : result1.qualType with
    | mk etyp qpoison qpred =>
        have hparrow : etyp = ETyp.parrow st1 st2 p tcls := by
          simpa [hres] using hetyp
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              result1.qualType id d := by
          simpa [hres] using hreach
        exact hqtPfn hreach'
  have hcap : CapturedEnvReachableFrom root ctxRoot σcap :=
    QTypReachableFrom.pfn_regular_captured hqtParrow hmem
  have hctx :
      ContextReachableFrom root ctxRoot
        { bodyCtx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } :=
    ContextReachableFrom.ofCaptured_update hcap bodyCtx harg
  intro y qt hlookup
  exact hctx (by simpa [hvar] using hlookup)

end ContextReachableFrom

namespace QTypReachableFrom

private theorem applyClosuresThreaded_forall_reachable
    {α : Type} {root : Expr} {ctxRoot : TypeContext}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (items : List α) (cursor : Tag × Loc) (results : List TypeResult)
    (hOne :
      ∀ item cursor result,
        applyOne item cursor = .ok result →
        QTypReachableFrom root ctxRoot result.qualType)
    (hthread : applyClosuresThreaded applyOne items cursor = .ok results) :
    ∀ result ∈ results, QTypReachableFrom root ctxRoot result.qualType := by
  induction items generalizing cursor results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      intro result hmem
      cases hmem
  | cons item rest ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _err =>
          simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest
              (first.nextTag', first.nextLoc') with
          | error _err =>
              simp [hrest] at hthread
          | ok restResults =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              intro result hmem
              simp at hmem
              cases hmem with
              | inl hfirstEq =>
                  subst result
                  exact hOne item cursor first hfirst
              | inr htail =>
                  exact ih _ _ hrest result htail

private theorem applyClosuresThreaded_forall_reachable_mem
    {α : Type} {root : Expr} {ctxRoot : TypeContext}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (items : List α) (cursor : Tag × Loc) (results : List TypeResult)
    (hOne :
      ∀ item, item ∈ items → ∀ cursor result,
        applyOne item cursor = .ok result →
        QTypReachableFrom root ctxRoot result.qualType)
    (hthread : applyClosuresThreaded applyOne items cursor = .ok results) :
    ∀ result ∈ results, QTypReachableFrom root ctxRoot result.qualType := by
  induction items generalizing cursor results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      intro result hmem
      cases hmem
  | cons item rest ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _err =>
          simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest
              (first.nextTag', first.nextLoc') with
          | error _err =>
              simp [hrest] at hthread
          | ok restResults =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              intro result hmem
              simp at hmem
              cases hmem with
              | inl hfirstEq =>
                  subst result
                  exact hOne item (by simp) cursor first hfirst
              | inr htail =>
                  exact
                    ih (first.nextTag', first.nextLoc') restResults
                      (fun tailItem htailMem cursor result happly =>
                        hOne tailItem (List.mem_cons_of_mem item htailMem)
                          cursor result happly)
                      hrest result htail

private def fnExternFinishAtCursor
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc)
    (p p1 : Poison) (unifiedEnv : VarTypeEnv)
    (tagMapping : ExtTreeMap TagIndex Tag compare) (nextTag' : Tag)
    (retSpec : ExternReturn) (memEnv : MemoryTypeEnv) : TypecheckM TypeResult :=
  match retSpec with
  | ExternReturn.simple typ poison pred =>
      match resolveSyntaxPred pred unifiedEnv tagMapping with
      | Except.error err => Except.error err
      | Except.ok v_1 =>
          match returnSpecToQTyp typ poison v_1 cursor.2 with
          | Except.error err => Except.error err
          | Except.ok v_2 =>
              Except.ok
                { qualType :=
                    normalizeAppResultByProvenance (joinPoison p1 p)
                      { etyp := v_2.1.etyp,
                        poison :=
                          joinPoison p1 (joinPoison p (joinPoison ctx.pc v_2.1.poison)),
                        pred := v_2.1.pred },
                  memEnv' := memEnv,
                  tagEnv' := result2.tagEnv',
                  nextLoc' := v_2.2,
                  nextTag' := nextTag',
                  regime' := result2.regime' }
  | ExternReturn.nestedFn innerId innerArg innerArgTyp innerRet innerEffects =>
      Except.ok
        { qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { etyp :=
                  ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                    [FnTClosure.extern innerId innerArg innerRet innerEffects
                      (VarTypeEnv.toCaptured unifiedEnv)],
                poison := joinPoison p1 (joinPoison p ctx.pc),
                pred := Predicate.noPred },
          memEnv' := memEnv,
          tagEnv' := result2.tagEnv',
          nextLoc' := cursor.2,
          nextTag' := nextTag',
          regime' := result2.regime' }
  | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerRet =>
      Except.ok
        { qualType :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              { etyp :=
                  ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                    [PFnTClosure.extern innerId innerArg innerRet
                      (VarTypeEnv.toCaptured unifiedEnv)],
                poison := joinPoison p1 (joinPoison p ctx.pc),
                pred := Predicate.noPred },
          memEnv' := memEnv,
          tagEnv' := result2.tagEnv',
          nextLoc' := cursor.2,
          nextTag' := nextTag',
          regime' := result2.regime' }

private theorem of_applyFnTClosureAtCursor
    {root : Expr} {ctxRoot ctx : TypeContext}
    {tcl : FnTClosure} {st1 st2 : Typ} {p p1 : Poison}
    {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {result1 result : TypeResult} {cursor : Tag × Loc}
    {fuel : Nat} {tcls : List FnTClosure}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (_hctx : ContextReachableFrom root ctxRoot ctx)
    (hqtFn : QTypReachableFrom root ctxRoot result1.qualType)
    (hfnEtyp : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
    (harg :
      QTypReachableFrom root ctxRoot
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
          pred := argPred })
    (hmem : tcl ∈ tcls)
    (happly :
      applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx result1 cursor fuel = .ok result) :
    QTypReachableFrom root ctxRoot result.qualType := by
  have hqtArrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } :=
    QTypReachableFrom.of_arrow_etyp_eq hqtFn hfnEtyp
  unfold applyFnTClosureAtCursor at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body σcap =>
          simp [bind, Except.bind] at happly
          cases htcBody :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison p1 ctx.pc),
                  memEnv := result1.memEnv',
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred },
                  tagEnv := result1.tagEnv',
                  nextTag := cursor.1,
                  nextLoc := cursor.2,
                  regime := result1.regime' } body fuel' with
          | error _err =>
              rw [htcBody] at happly
              simp at happly
          | ok bodyResult =>
              rw [htcBody] at happly
              simp at happly
              cases hbodyQt : bodyResult.qualType with
              | mk bodyEtyp bodyPoison bodyPred =>
                  simp [hbodyQt] at happly
                  cases hsub :
                      isSubtype st2
                        { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred }
                  · simp [hsub] at happly
                  · simp [hsub, pure, Except.pure] at happly
                    cases happly
                    have hbodyCtx :
                        ContextReachableFrom root ctxRoot
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                              { etyp := argEtyp,
                                poison := joinPoison ctx.pc argPoison,
                                pred := argPred },
                            tagEnv := result1.tagEnv',
                            nextTag := cursor.1,
                            nextLoc := cursor.2,
                            regime := result1.regime' } :=
                      ContextReachableFrom.fnBody_of_arrow_member
                        hqtFn hfnEtyp hmem harg rfl
                    have hbodyReach :
                        ExternDeclarationReachableFromExpr root ctxRoot body := by
                      intro id d hprog
                      exact QTypReachableFrom.fn_regular_body hqtArrow hmem hprog
                    have hbodyResultReach :
                        QTypReachableFrom root ctxRoot bodyResult.qualType :=
                      IH fuel' (Nat.lt_succ_self fuel') hbodyCtx hbodyReach htcBody
                    have hbodyBaseReach :
                        QTypReachableFrom root ctxRoot
                          { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred } := by
                      intro id d hreach
                      exact hbodyResultReach (by simpa [hbodyQt] using hreach)
                    intro id d hreach
                    cases hgate : joinPoison p1 p
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := joinPoison p1 (joinPoison p bodyPoison))
                          (qpred := bodyPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := true) (qpred := Predicate.noPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
      | extern id x retSpec effects capturedEnv =>
          have hcap : CapturedEnvReachableFrom root ctxRoot capturedEnv :=
            QTypReachableFrom.fn_extern_captured hqtArrow hmem
          have hargQt :
              QTypReachableFrom root ctxRoot
                { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
                  pred := argPred } := harg
          have hunifiedCtx :
              ContextReachableFrom root ctxRoot
                { ctx with
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred } } :=
            ContextReachableFrom.ofCaptured_update hcap ctx hargQt
          let unifiedEnv : VarTypeEnv :=
            VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              { etyp := argEtyp,
                poison := joinPoison ctx.pc argPoison,
                pred := argPred }
          simp [bind, Except.bind] at happly
          cases htag :
              collectAndAllocExternTags (collectExternPreds retSpec effects) cursor.1 with
          | error _err =>
              simp [htag] at happly
          | ok tagResult =>
              cases tagResult with
              | mk tagMapping nextTag' =>
                  simp [htag] at happly
                  let effectRun : TypecheckM MemoryTypeEnv :=
                    forIn effects result1.memEnv' fun effect r =>
                      match applyExternEffect effect unifiedEnv tagMapping
                          (joinPoison p (joinPoison p1 ctx.pc)) r with
                      | Except.error err => Except.error err
                      | Except.ok v => Except.ok (ForInStep.yield v)
                  let finish : MemoryTypeEnv → TypecheckM TypeResult :=
                    fnExternFinishAtCursor ctx result1 cursor p p1 unifiedEnv tagMapping
                      nextTag' retSpec
                  have hwholeOk :
                      (match effectRun with
                      | Except.error err => Except.error err
                      | Except.ok v => finish v) = Except.ok result := by
                    convert happly
                    · funext _motive scrut _err _ok
                      cases scrut <;> rfl
                    · funext _motive scrut _err _ok
                      cases scrut <;> rfl
                    · rename_i memEnvArg
                      cases retSpec <;> simp [finish, fnExternFinishAtCursor, unifiedEnv,
                        pure, Except.pure]
                      · rename_i typ poison pred
                        cases resolveSyntaxPred pred unifiedEnv tagMapping <;> simp
                        · rename_i resolvedPred
                          cases returnSpecToQTyp typ poison resolvedPred cursor.2 <;> rfl
                  cases hfor : effectRun with
                  | error _err =>
                      have hbad : (Except.error _err : TypecheckM TypeResult) =
                          Except.ok result := by
                        have hcongr := congrArg
                          (fun z : TypecheckM MemoryTypeEnv =>
                            match z with
                            | Except.error err => (Except.error err : TypecheckM TypeResult)
                            | Except.ok memEnv => finish memEnv) hfor
                        simpa [finish] using Eq.trans (Eq.symm hcongr) hwholeOk
                      cases hbad
                  | ok memEnv =>
                      have hfinishOk : finish memEnv = Except.ok result := by
                        have hcongr := congrArg
                          (fun z : TypecheckM MemoryTypeEnv =>
                            match z with
                            | Except.error err => (Except.error err : TypecheckM TypeResult)
                            | Except.ok memEnv => finish memEnv) hfor
                        simpa [finish] using Eq.trans (Eq.symm hcongr) hwholeOk
                      cases retSpec with
                      | simple typ poison pred =>
                          simp [finish, fnExternFinishAtCursor] at hfinishOk
                          cases hresPred :
                              resolveSyntaxPred pred unifiedEnv tagMapping with
                          | error _err =>
                              simp [hresPred] at hfinishOk
                          | ok resolvedPred =>
                              simp [hresPred] at hfinishOk
                              cases hret :
                                  returnSpecToQTyp typ poison resolvedPred cursor.2 with
                              | error _err =>
                                  simp [hret] at hfinishOk
                              | ok retPair =>
                                  cases retPair with
                                  | mk retQt nextLoc' =>
                                      simp [hret] at hfinishOk
                                      cases hfinishOk
                                      apply QTypReachableFrom.of_non_function_etyp
                                      rw [normalizeAppResultByProvenance_etyp]
                                      cases typ with
                                      | int =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | bool =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | unit =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | ref _ =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                      | arrow _ _ =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                      | string =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                      | nestedFn innerId innerArg innerArgTyp innerRet innerEffects =>
                          simp [finish, fnExternFinishAtCursor] at hfinishOk
                          cases hfinishOk
                          have hcurrent :
                              ExternDeclarationReachableFromExpr root ctxRoot
                                (Expr.externFn innerId innerArg innerArgTyp innerRet innerEffects) := by
                            intro nestedId d hprog
                            cases hprog with
                            | externFn =>
                                exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                  ExternDeclarationInReturn.nestedFn_here
                            | externFn_return hret =>
                                exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                  (ExternDeclarationInReturn.nestedFn_inner hret)
                          have hnestedBase :
                              QTypReachableFrom root ctxRoot
                                { etyp :=
                                    ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                                      [FnTClosure.extern innerId innerArg innerRet innerEffects
                                        (VarTypeEnv.toCaptured unifiedEnv)],
                                  poison := ctx.pc,
                                  pred := Predicate.noPred } := by
                            intro nestedId d hreach
                            exact (QTypReachableFrom.of_externFn_result hunifiedCtx hcurrent)
                              (by simpa [unifiedEnv] using hreach)
                          intro nestedId d hreach
                          cases hgate : joinPoison p1 p
                          · exact
                              (QTypReachableFrom.with_etyp
                                (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                                (qpred := Predicate.noPred) hnestedBase)
                                (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                          · exact
                              (QTypReachableFrom.with_etyp
                                (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                                (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                      | nestedPfn innerId innerArg innerArgTyp innerRet =>
                          simp [finish, fnExternFinishAtCursor] at hfinishOk
                          cases hfinishOk
                          have hcurrent :
                              ExternDeclarationReachableFromExpr root ctxRoot
                                (Expr.externPfn innerId innerArg innerArgTyp innerRet) := by
                            intro nestedId d hprog
                            cases hprog with
                            | externPfn =>
                                exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                  ExternDeclarationInReturn.nestedPfn_here
                            | externPfn_return hret =>
                                exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                  (ExternDeclarationInReturn.nestedPfn_inner hret)
                          have hnestedBase :
                              QTypReachableFrom root ctxRoot
                                { etyp :=
                                    ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                                      [PFnTClosure.extern innerId innerArg innerRet
                                        (VarTypeEnv.toCaptured unifiedEnv)],
                                  poison := ctx.pc,
                                  pred := Predicate.noPred } := by
                            intro nestedId d hreach
                            exact (QTypReachableFrom.of_externPfn_result hunifiedCtx hcurrent)
                              (by simpa [unifiedEnv] using hreach)
                          intro nestedId d hreach
                          cases hgate : joinPoison p1 p
                          · exact
                              (QTypReachableFrom.with_etyp
                                (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                                (qpred := Predicate.noPred) hnestedBase)
                                (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                          · exact
                              (QTypReachableFrom.with_etyp
                                (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                                (by simpa [normalizeAppResultByProvenance, hgate] using hreach)

private theorem of_applyPFnTClosureAtCursor
    {root : Expr} {ctxRoot ctx : TypeContext}
    {tcl : PFnTClosure} {st1 st2 : Typ} {p p1 : Poison}
    {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {result1 result : TypeResult} {cursor : Tag × Loc}
    {fuel : Nat} {tcls : List PFnTClosure}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (_hctx : ContextReachableFrom root ctxRoot ctx)
    (hqtPfn : QTypReachableFrom root ctxRoot result1.qualType)
    (hpfnEtyp : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
    (harg :
      QTypReachableFrom root ctxRoot
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
          pred := argPred })
    (hmem : tcl ∈ tcls)
    (happly :
      applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx result1 cursor fuel = .ok result) :
    QTypReachableFrom root ctxRoot result.qualType := by
  have hqtParrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } :=
    QTypReachableFrom.of_parrow_etyp_eq hqtPfn hpfnEtyp
  unfold applyPFnTClosureAtCursor at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body σcap =>
          simp [bind, Except.bind] at happly
          cases htcBody :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc p1),
                  memEnv := result1.memEnv',
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred },
                  tagEnv := result1.tagEnv',
                  pureCtx := true,
                  nextLoc := cursor.2,
                  nextTag := cursor.1,
                  regime := result1.regime' } (PExpr.toExpr body) fuel' with
          | error _err =>
              rw [htcBody] at happly
              simp at happly
          | ok bodyResult =>
              rw [htcBody] at happly
              simp at happly
              cases hbodyQt : bodyResult.qualType with
              | mk bodyEtyp bodyPoison bodyPred =>
                  simp [hbodyQt] at happly
                  cases hsub :
                      isSubtype st2
                        { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred }
                  · simp [hsub] at happly
                  · simp [hsub, pure, Except.pure] at happly
                    cases happly
                    have hbodyCtx :
                        ContextReachableFrom root ctxRoot
                          { ctx with
                            pc := joinPoison p (joinPoison ctx.pc p1),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                              { etyp := argEtyp,
                                poison := joinPoison ctx.pc argPoison,
                                pred := argPred },
                            tagEnv := result1.tagEnv',
                            pureCtx := true,
                            nextLoc := cursor.2,
                            nextTag := cursor.1,
                            regime := result1.regime' } :=
                      ContextReachableFrom.pfnBody_of_parrow_member
                        hqtPfn hpfnEtyp hmem harg rfl
                    have hbodyReach :
                        ExternDeclarationReachableFromExpr root ctxRoot
                          (PExpr.toExpr body) := by
                      intro id d hprog
                      exact QTypReachableFrom.pfn_regular_body hqtParrow hmem hprog
                    have hbodyResultReach :
                        QTypReachableFrom root ctxRoot bodyResult.qualType :=
                      IH fuel' (Nat.lt_succ_self fuel') hbodyCtx hbodyReach htcBody
                    have hbodyBaseReach :
                        QTypReachableFrom root ctxRoot
                          { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred } := by
                      intro id d hreach
                      exact hbodyResultReach (by simpa [hbodyQt] using hreach)
                    intro id d hreach
                    cases hgate : joinPoison p1 p
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := joinPoison p1 (joinPoison p bodyPoison))
                          (qpred := bodyPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := true) (qpred := Predicate.noPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
      | extern id x retSpec capturedEnv =>
          have hcap : CapturedEnvReachableFrom root ctxRoot capturedEnv :=
            QTypReachableFrom.pfn_extern_captured hqtParrow hmem
          have hargQt :
              QTypReachableFrom root ctxRoot
                { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
                  pred := argPred } := harg
          have hunifiedCtx :
              ContextReachableFrom root ctxRoot
                { ctx with
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred } } :=
            ContextReachableFrom.ofCaptured_update hcap ctx hargQt
          let unifiedEnv : VarTypeEnv :=
            VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              { etyp := argEtyp,
                poison := joinPoison ctx.pc argPoison,
                pred := argPred }
          cases retSpec with
          | simple typ poison pred =>
              simp [bind, Except.bind] at happly
              cases htag : collectAndAllocExternTags [pred] cursor.1 with
              | error _err =>
                  simp [htag] at happly
              | ok tagResult =>
                  cases tagResult with
                  | mk tagMapping nextTag' =>
                      simp [htag] at happly
                      cases hresPred :
                          resolveSyntaxPred pred unifiedEnv tagMapping with
                      | error _err =>
                          rw [hresPred] at happly
                          simp at happly
                      | ok resolvedPred =>
                          rw [hresPred] at happly
                          simp at happly
                          cases hret :
                              returnSpecToQTyp typ poison resolvedPred cursor.2 with
                          | error _err =>
                              simp [hret] at happly
                          | ok retPair =>
                              cases retPair with
                              | mk retQt nextLoc' =>
                                  simp [hret, pure, Except.pure] at happly
                                  cases happly
                                  apply QTypReachableFrom.of_non_function_etyp
                                  rw [normalizeAppResultByProvenance_etyp]
                                  cases typ with
                                  | int =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | bool =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | unit =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | ref _ =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                  | arrow _ _ =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                  | string =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | nestedFn innerId innerArg innerArgTyp innerRet innerEffects =>
              simp [pure, Except.pure] at happly
              cases happly
              have hcurrent :
                  ExternDeclarationReachableFromExpr root ctxRoot
                    (Expr.externFn innerId innerArg innerArgTyp innerRet innerEffects) := by
                intro nestedId d hprog
                cases hprog with
                | externFn =>
                    exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                      ExternDeclarationInReturn.nestedFn_here
                | externFn_return hret =>
                    exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                      (ExternDeclarationInReturn.nestedFn_inner hret)
              have hnestedBase :
                  QTypReachableFrom root ctxRoot
                    { etyp :=
                        ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                          [FnTClosure.extern innerId innerArg innerRet innerEffects
                            (VarTypeEnv.toCaptured unifiedEnv)],
                      poison := ctx.pc,
                      pred := Predicate.noPred } := by
                intro nestedId d hreach
                exact (QTypReachableFrom.of_externFn_result hunifiedCtx hcurrent)
                  (by simpa [unifiedEnv] using hreach)
              intro nestedId d hreach
              cases hgate : joinPoison p1 p
              · exact
                  (QTypReachableFrom.with_etyp
                    (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                    (qpred := Predicate.noPred) hnestedBase)
                    (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
              · exact
                  (QTypReachableFrom.with_etyp
                    (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                    (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
          | nestedPfn innerId innerArg innerArgTyp innerRet =>
              simp [pure, Except.pure] at happly
              cases happly
              have hcurrent :
                  ExternDeclarationReachableFromExpr root ctxRoot
                    (Expr.externPfn innerId innerArg innerArgTyp innerRet) := by
                intro nestedId d hprog
                cases hprog with
                | externPfn =>
                    exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                      ExternDeclarationInReturn.nestedPfn_here
                | externPfn_return hret =>
                    exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                      (ExternDeclarationInReturn.nestedPfn_inner hret)
              have hnestedBase :
                  QTypReachableFrom root ctxRoot
                    { etyp :=
                        ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                          [PFnTClosure.extern innerId innerArg innerRet
                            (VarTypeEnv.toCaptured unifiedEnv)],
                      poison := ctx.pc,
                      pred := Predicate.noPred } := by
                intro nestedId d hreach
                exact (QTypReachableFrom.of_externPfn_result hunifiedCtx hcurrent)
                  (by simpa [unifiedEnv] using hreach)
              intro nestedId d hreach
              cases hgate : joinPoison p1 p
              · exact
                  (QTypReachableFrom.with_etyp
                    (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                    (qpred := Predicate.noPred) hnestedBase)
                    (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
              · exact
                  (QTypReachableFrom.with_etyp
                    (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                    (by simpa [normalizeAppResultByProvenance, hgate] using hreach)

private theorem of_typecheckApp
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 : Expr}
    {fuel : Nat} {res : TypeResult}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot (Expr.app e1 e2))
    (htc : typecheckApp ctx e1 e2 fuel = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheckApp] at htc
  | succ fuel' =>
      rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel' res htc with
        ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, hcases⟩
      have IH' :
          ∀ m < fuel', ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
            ContextReachableFrom root ctxRoot ctx →
            ExternDeclarationReachableFromExpr root ctxRoot e →
            typecheck ctx e m = .ok res →
            QTypReachableFrom root ctxRoot res.qualType := by
        intro m hm ctx e res hctxm hcanm htcm
        exact IH m (Nat.lt_trans hm (Nat.lt_succ_self fuel')) hctxm hcanm htcm
      have hargRaw : QTypReachableFrom root ctxRoot result2.qualType :=
        IH fuel' (Nat.lt_succ_self fuel') hctx
          (ExternDeclarationReachableFromExpr.app_arg hcurrent)
          (by simpa [typecheck] using htc2)
      have harg :
          QTypReachableFrom root ctxRoot
            { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } :=
        QTypReachableFrom.of_eq_redecorate hargRaw hqt2
      let ctxFun : TypeContext :=
        { ctx with
          memEnv := result2.memEnv',
          tagEnv := result2.tagEnv',
          nextLoc := result2.nextLoc',
          nextTag := result2.nextTag',
          regime := result2.regime' }
      have hctxFun : ContextReachableFrom root ctxRoot ctxFun := by
        intro x qt hlookup
        exact hctx (by simpa [ctxFun] using hlookup)
      have hfnReach : QTypReachableFrom root ctxRoot result1.qualType :=
        IH fuel' (Nat.lt_succ_self fuel') hctxFun
          (ExternDeclarationReachableFromExpr.app_fun hcurrent)
          (by simpa [typecheck, ctxFun] using htc1)
      cases hcases with
      | inl harrow =>
          rcases harrow with
            ⟨st1, st2, p, p1, tcls, results, first, rest, hfnEtyp, _hp1,
              _hnpure, _hnempty, _hsub, hthread, hresults, hjoin⟩
          have hresultsReach :
              ∀ result ∈ results,
                QTypReachableFrom root ctxRoot result.qualType :=
            applyClosuresThreaded_forall_reachable_mem
              (fun tcl cursor =>
                applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                  ctx result1 cursor fuel')
              tcls (result1.nextTag', result1.nextLoc') results
              (fun tcl hmem cursor result happly =>
                of_applyFnTClosureAtCursor IH' hctx hfnReach hfnEtyp harg hmem happly)
              hthread
          have hfirstReach : QTypReachableFrom root ctxRoot first.qualType :=
            hresultsReach first (by simp [hresults])
          have hrestReach :
              ∀ result ∈ rest,
                QTypReachableFrom root ctxRoot result.qualType := by
            intro result hmem
            exact hresultsReach result (by simp [hresults, hmem])
          intro id d hreach
          exact (QTypReachableFrom.of_joinTypeResults hfirstReach hrestReach hjoin) hreach
      | inr hparrow =>
          rcases hparrow with
            ⟨st1, st2, p, p1, tcls, results, first, rest, hpfnEtyp, _hp1,
              _hnempty, _hsub, hthread, hresults, hjoin⟩
          have hresultsReach :
              ∀ result ∈ results,
                QTypReachableFrom root ctxRoot result.qualType :=
            applyClosuresThreaded_forall_reachable_mem
              (fun tcl cursor =>
                applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                  ctx result1 cursor fuel')
              tcls (result1.nextTag', result1.nextLoc') results
              (fun tcl hmem cursor result happly =>
                of_applyPFnTClosureAtCursor IH' hctx hfnReach hpfnEtyp harg hmem happly)
              hthread
          have hfirstReach : QTypReachableFrom root ctxRoot first.qualType :=
            hresultsReach first (by simp [hresults])
          have hrestReach :
              ∀ result ∈ rest,
                QTypReachableFrom root ctxRoot result.qualType := by
            intro result hmem
            exact hresultsReach result (by simp [hresults, hmem])
          intro id d hreach
          exact (QTypReachableFrom.of_joinTypeResults hfirstReach hrestReach hjoin) hreach

set_option linter.unnecessarySeqFocus false in
private theorem opEType?_nonFunction
    {op : Op} {etyp₁ etyp₂ result : ETyp}
    (hop : opEType? op etyp₁ etyp₂ = some result) :
    result.isFunctionType = false := by
  cases op <;> cases etyp₁ <;> cases etyp₂ <;> simp [opEType?] at hop
  all_goals cases hop <;> rfl

set_option linter.unnecessarySeqFocus false in
private theorem opUnaryEType?_nonFunction
    {op : UnaryOp} {etyp result : ETyp}
    (hop : opUnaryEType? op etyp = some result) :
    result.isFunctionType = false := by
  cases op <;> cases etyp <;> simp [opUnaryEType?] at hop
  all_goals cases hop <;> rfl

private theorem surfaceSpecToQTyp_nonFunction
    {typ : Typ} {poison : Poison} {pred : Predicate}
    {ctx ctx' : TypeContext} {qt : QTyp}
    (hsurf : surfaceSpecToQTyp typ poison pred ctx = .ok (qt, ctx')) :
    qt.etyp.isFunctionType = false := by
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure] at hsurf
  cases typ with
  | int | bool | unit | string =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsurf
      rw [← hsurf.1]
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  | ref t =>
      cases t with
      | int =>
          simp only [freshTLoc, show (Typ.int != Typ.int) = false from by decide,
            Bool.false_eq_true, ite_false, Except.ok.injEq, Prod.mk.injEq] at hsurf
          rw [← hsurf.1]
          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
      | bool | unit | ref _ | arrow _ _ | string =>
          simp [bne] at hsurf
  | arrow _ _ =>
      simp at hsurf

private theorem of_typecheckExternVal
    {root : Expr} {ctxRoot ctx : TypeContext}
    {typ : Typ} {poison : Poison} {pred : SyntaxPredicate} {res : TypeResult}
    (htc : typecheckExternVal ctx typ poison pred = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  apply QTypReachableFrom.of_non_function_etyp
  have hOkPath :
      ∀ pred',
        (do
          let (tagMapping, nextTag') ← collectAndAllocExternTags [pred'] ctx.nextTag
          let resolvedPred ← resolveSyntaxPred pred' ctx.varEnv tagMapping
          let (qt, ctx') ← surfaceSpecToQTyp typ poison resolvedPred ctx
          let out : TypeResult :=
            { qualType := qt, memEnv' := ctx'.memEnv, tagEnv' := ctx.tagEnv,
              nextLoc' := ctx'.nextLoc, nextTag' := nextTag', regime' := ctx.regime }
          pure out) =
            (.ok res : TypecheckM TypeResult) →
        res.qualType.etyp.isFunctionType = false := by
    intro pred' hpath
    simp [bind, Except.bind] at hpath
    cases htag : collectAndAllocExternTags [pred'] ctx.nextTag with
    | error _err =>
        simp [htag] at hpath
    | ok tagResult =>
        cases tagResult with
        | mk tagMapping nextTag' =>
            simp [htag] at hpath
            cases hresolved : resolveSyntaxPred pred' ctx.varEnv tagMapping with
            | error _err =>
                rw [hresolved] at hpath
                simp at hpath
            | ok resolvedPred =>
                rw [hresolved] at hpath
                simp at hpath
                cases hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx with
                | error _err =>
                    simp [hsurf] at hpath
                | ok surfPair =>
                    cases surfPair with
                    | mk qt ctx' =>
                        simp [hsurf, pure, Except.pure] at hpath
                        cases hpath
                        exact surfaceSpecToQTyp_nonFunction hsurf
  cases poison with
  | false =>
      cases pred with
      | guardClosure idx arg body =>
          simp [typecheckExternVal] at htc
      | guardOnly idx =>
          simp [typecheckExternVal] at htc
      | noPred =>
          exact hOkPath SyntaxPredicate.noPred (by simpa [typecheckExternVal] using htc)
  | true =>
      cases pred with
      | guardClosure idx arg body =>
          exact
            hOkPath (SyntaxPredicate.guardClosure idx arg body)
              (by simpa [typecheckExternVal] using htc)
      | guardOnly idx =>
          exact
            hOkPath (SyntaxPredicate.guardOnly idx)
              (by simpa [typecheckExternVal] using htc)
      | noPred =>
          exact hOkPath SyntaxPredicate.noPred (by simpa [typecheckExternVal] using htc)

theorem of_typecheck
    {root : Expr} {ctxRoot ctx : TypeContext} {e : Expr}
    {fuel : Nat} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent : ExternDeclarationReachableFromExpr root ctxRoot e)
    (htc : typecheck ctx e fuel = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  revert ctx e res
  induction fuel using Nat.strongRecOn with
  | ind fuel IH =>
      intro ctx e res hctx hcurrent htc
      unfold typecheck at htc
      cases fuel with
      | zero =>
          simp [typecheckExpr] at htc
      | succ fuel' =>
          cases e with
          | num n =>
              simp [typecheckExpr, typecheckInt, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | bool b =>
              simp [typecheckExpr, typecheckBool, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | unit =>
              simp [typecheckExpr, typecheckUnit, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | str s =>
              simp [typecheckExpr, typecheckString, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | var x =>
              exact QTypReachableFrom.of_typecheckVar hctx (by simpa [typecheckExpr] using htc)
          | op e1 op e2 =>
              have htcOp : typecheckOp ctx e1 e2 fuel' op = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckOp_structure ctx e1 e2 op fuel' res htcOp with
                ⟨_result1, _result2, resultEtyp, _htc1, _htc2, hop,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              exact opEType?_nonFunction hop
          | newRef e1 =>
              have htcNew : typecheckNewRef ctx e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckNewRef_structure ctx e1 fuel' res htcNew with
                ⟨_result1, _l, _htc1, _hl, _hint, hetyp, _hpoison, _hpred,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | assign e1 e2 =>
              have htcAssign : typecheckAssign ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckAssign_structure ctx e1 e2 fuel' res htcAssign with
                ⟨_result1, _result2, _ls, _htc1, _href, _htc2, _hint,
                  _hnextLoc, _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | deref e1 =>
              apply QTypReachableFrom.of_non_function_etyp
              have het : res.qualType.etyp = ETyp.int :=
                typecheckDeref_etyp_int ctx e1 fuel' res (by simpa [typecheckExpr] using htc)
              rw [het]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | seq e1 e2 =>
              have htcSeq : typecheckSeq ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
                ⟨result1, ctx', _htc1, hctx', htc2⟩
              have hctxSeq : ContextReachableFrom root ctxRoot ctx' := by
                subst ctx'
                exact ContextReachableFrom.ctxAfter hctx
              intro id d hreach
              exact
                (IH (fuel' - 1) (by omega) hctxSeq
                  (ExternDeclarationReachableFromExpr.seq_right hcurrent)
                  (by simpa [typecheck] using htc2)) hreach
          | vlet x e1 e2 =>
              have htcVlet : typecheckVlet ctx x e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
                ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime, _hpoison, _hpred⟩
              have hqt1 : QTypReachableFrom root ctxRoot result1.qualType :=
                IH (fuel' - 1) (by omega) hctx
                  (ExternDeclarationReachableFromExpr.vlet_bound hcurrent)
                  (by simpa [typecheck] using htc1)
              have hctxUpdate :
                  ContextReachableFrom root ctxRoot
                    { ctx with varEnv := VarTypeEnv.update ctx.varEnv x result1.qualType } :=
                ContextReachableFrom.update hctx hqt1
              have hctxVlet : ContextReachableFrom root ctxRoot ctx' := by
                intro y qt hlookup
                exact hctxUpdate (by simpa [hctx'] using hlookup)
              have hqt2 : QTypReachableFrom root ctxRoot result2.qualType :=
                IH (fuel' - 1) (by omega) hctxVlet
                  (ExternDeclarationReachableFromExpr.vlet_body hcurrent)
                  (by simpa [typecheck] using htc2)
              cases hresQt : res.qualType with
              | mk resEtyp resPoison resPred =>
                  cases hqt2Qt : result2.qualType with
                  | mk etyp poison pred =>
                      have hqt2' :
                          QTypReachableFrom root ctxRoot
                            { etyp := etyp, poison := poison, pred := pred } := by
                        intro id d hreach
                        exact hqt2 (by simpa [hqt2Qt] using hreach)
                      have het : resEtyp = etyp := by
                        simpa [hresQt, hqt2Qt] using hetyp
                      subst resEtyp
                      intro id d hreach
                      exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := resPoison) (qpred := resPred) hqt2') hreach
          | fn x argTyp body retTyp =>
              exact
                QTypReachableFrom.of_typecheckFn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | pfn x argTyp body retTyp =>
              exact
                QTypReachableFrom.of_typecheckPfn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | app e1 e2 =>
              exact
                QTypReachableFrom.of_typecheckApp (fuel := fuel')
                  (fun m hm {ctx} {e} {res} hctxm hcanm htcm =>
                    IH m (by omega) hctxm hcanm htcm)
                  hctx hcurrent (by simpa [typecheckExpr] using htc)
          | ite e1 e2 e3 =>
              have htcIf : typecheckIf ctx e1 e2 e3 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htcIf with htrue | hfalse | hstd
              · rcases htrue with
                  ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool,
                    res2, _res3, htc2, _htc3, _hmem, _htag, _hnextLoc,
                    _hnextTag, _hregime, _hpoison, hetyp⟩
                let ctxTrue : TypeContext :=
                  { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
                have hctxTrue : ContextReachableFrom root ctxRoot ctxTrue := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctxTrue] using hlookup)
                have hqt2 : QTypReachableFrom root ctxRoot res2.qualType :=
                  IH (fuel' - 1) (by omega) hctxTrue
                    (ExternDeclarationReachableFromExpr.ite_then hcurrent)
                    (by simpa [typecheck, ctxTrue] using htc2)
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    cases hqt2Qt : res2.qualType with
                    | mk etyp poison pred =>
                        have hqt2' :
                            QTypReachableFrom root ctxRoot
                              { etyp := etyp, poison := poison, pred := pred } := by
                          intro id d hreach
                          exact hqt2 (by simpa [hqt2Qt] using hreach)
                        have het : resEtyp = etyp := by
                          simpa [hresQt, hqt2Qt] using hetyp
                        subst resEtyp
                        intro id d hreach
                        exact
                          (QTypReachableFrom.with_etyp
                            (qpoison := resPoison) (qpred := resPred) hqt2') hreach
              · rcases hfalse with
                  ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool,
                    res2, res3, _htc2, htc3, _hmem, _htag, _hnextLoc,
                    _hnextTag, _hregime, _hpoison, hetyp⟩
                let ctxFalse : TypeContext :=
                  { pc := ctx.pc, regime := ctx.regime, memEnv := ctx.memEnv,
                    varEnv := ctx.varEnv,
                    tagEnv := ctx.tagEnv.insert k { value := false, deps := deps },
                    nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                    pureCtx := ctx.pureCtx }
                have hctxFalse : ContextReachableFrom root ctxRoot ctxFalse := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctxFalse] using hlookup)
                have hqt3 : QTypReachableFrom root ctxRoot res3.qualType :=
                  IH (fuel' - 1) (by omega) hctxFalse
                    (ExternDeclarationReachableFromExpr.ite_else hcurrent)
                    (by simpa [typecheck, ctxFalse] using htc3)
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    cases hqt3Qt : res3.qualType with
                    | mk etyp poison pred =>
                        have hqt3' :
                            QTypReachableFrom root ctxRoot
                              { etyp := etyp, poison := poison, pred := pred } := by
                          intro id d hreach
                          exact hqt3 (by simpa [hqt3Qt] using hreach)
                        have het : resEtyp = etyp := by
                          simpa [hresQt, hqt3Qt] using hetyp
                        subst resEtyp
                        intro id d hreach
                        exact
                          (QTypReachableFrom.with_etyp
                            (qpoison := resPoison) (qpred := resPred) hqt3') hreach
              · rcases hstd with
                  ⟨_hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3,
                    _hmem, _htag, _hnextLoc, _hnextTag, _hregime, _hpoison,
                    hetyp, _hpred⟩
                have hqt1 : QTypReachableFrom root ctxRoot res1.qualType :=
                  IH (fuel' - 1) (by omega) hctx
                    (ExternDeclarationReachableFromExpr.ite_cond hcurrent)
                    (by simpa [typecheck] using htc1)
                let ctx' : TypeContext :=
                  { pc := ctx.pc, regime := res1.regime', memEnv := res1.memEnv',
                    varEnv := ctx.varEnv, tagEnv := res1.tagEnv',
                    nextLoc := res1.nextLoc', nextTag := res1.nextTag',
                    pureCtx := ctx.pureCtx }
                let ctx'' : TypeContext :=
                  { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
                have hctx'' : ContextReachableFrom root ctxRoot ctx'' := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctx'', ctx'] using hlookup)
                have hqt2 : QTypReachableFrom root ctxRoot res2.qualType :=
                  IH (fuel' - 1) (by omega) hctx''
                    (ExternDeclarationReachableFromExpr.ite_then hcurrent)
                    (by simpa [typecheck, ctx'', ctx'] using htc2)
                let ctxForE3 : TypeContext :=
                  { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                have hctxE3 : ContextReachableFrom root ctxRoot ctxForE3 := by
                  intro x qt hlookup
                  exact hctx'' (by simpa [ctxForE3] using hlookup)
                have hqt3 : QTypReachableFrom root ctxRoot res3.qualType :=
                  IH (fuel' - 1) (by omega) hctxE3
                    (ExternDeclarationReachableFromExpr.ite_else hcurrent)
                    (by simpa [typecheck, ctxForE3, ctx'', ctx'] using htc3)
                have hjoined :
                    QTypReachableFrom root ctxRoot
                      { etyp := joinETyps res2.qualType.etyp res3.qualType.etyp
                          res2.qualType.poison res3.qualType.poison,
                        poison := joinPoison res2.qualType.poison res3.qualType.poison,
                        pred := joinPredicates res2.qualType.pred res3.qualType.pred } :=
                  QTypReachableFrom.of_joinETyps hqt2 hqt3
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    have het :
                        resEtyp =
                          joinETyps res2.qualType.etyp res3.qualType.etyp
                            res2.qualType.poison res3.qualType.poison := by
                      simpa [hresQt] using hetyp
                    subst resEtyp
                    intro id d hreach
                    exact
                      (QTypReachableFrom.with_etyp
                        (qpoison := resPoison) (qpred := resPred) hjoined) hreach
          | unaryop op e1 =>
              have htcUnary : typecheckUnaryOp ctx op e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckUnaryOp_structure ctx op e1 fuel' res htcUnary with
                ⟨_result1, resultEtyp, _htc1, hop, _hmem, _htag, _hnextLoc,
                  _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              exact opUnaryEType?_nonFunction hop
          | externVal id typ poison pred =>
              exact QTypReachableFrom.of_typecheckExternVal (by simpa [typecheckExpr] using htc)
          | externFn id arg argTyp retSpec effects =>
              exact
                QTypReachableFrom.of_typecheckExternFn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | externPfn id arg argTyp retSpec =>
              exact
                QTypReachableFrom.of_typecheckExternPfn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
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
