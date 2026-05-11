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
  fnClosures :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {argTyp : Typ},
      ExternDeclLift root (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      TrustedRegistryAgreesWithFnTClosures tr argTyp tcls
  fnRegularExternBody :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List FnTClosure} {argTyp : Typ}
      {id : ExternId} {x y : Name} {retSpec : ExternReturn}
      {effects : List Effect} {capturedEnv : CapturedVarEnv},
      ExternDeclLift root (Expr.app e1 e2) →
      AppFnClosureListFromTypecheck ctx e1 e2 res tcls →
      FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) capturedEnv ∈ tcls →
      ∃ entry,
        TrustedRegistry.lookup? tr id = some entry ∧
        TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects
  pfnClosures :
    ∀ {ctx : TypeContext} {e1 e2 : Expr} {res : TypeResult}
      {tcls : List PFnTClosure} {argTyp : Typ},
      ExternDeclLift root (Expr.app e1 e2) →
      AppPfnClosureListFromTypecheck ctx e1 e2 res tcls →
      TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls

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
