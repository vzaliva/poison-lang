/-
  ExternRuntime.lean — Implementation-facing runtime extern boundary data.

  This module holds the runtime-event predicates and the strengthened
  operational safety contract used to discharge `SemanticsProperties.lean`
  obligations.  It is intentionally below the FR boundary contract layer
  (`ExternBoundary.lean`) so that `SemanticsProperties.lean` can talk about
  raw extern runtime safety without importing FR-shaped machinery.

  Definitions here do not depend on `StepFRPost`, `BoundaryTagMeaningPost`,
  or any other FR proof concept.
-/

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Aux
import LeanProofs.Semantics

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

/-- Static declaration shape extracted from a source expression.

    `typ`, `argPoison`, `argPred` are the surface form of the declared argument
    condition (precondition): base type, poison flag, and symbolic predicate
    (doc/extern-argument-conditions.md).  `argPoison` (the clean/poisoned flag) is
    populated FAITHFULLY at every construction site — from the source AST at
    syntactic sites and from the applied closure's `argQTyp.poison` at the
    arrow-reachability site — so the reachable `entry.decl = d` agreement binds the
    declared argument's poison flag: a clean-argument trusted proof only covers a
    clean-argument program declaration.  `argPred` keeps a `noPred` default: a
    stronger (predicated) program precondition is sound to differ from a trusted
    no-predicate entry, and the surface predicate is not recoverable at the
    arrow-reachability site (where only the resolved closure predicate is available). -/
structure ExternDeclaration where
  id        : ExternId
  kind      : ExternDeclarationKind
  typ       : Typ
  argName   : Option Name
  retSpec   : Option ExternReturn
  effects   : List Effect
  preds     : List SyntaxPredicate
  argPoison : Bool
  argPred   : SyntaxPredicate := .noPred

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
  value_shape : ∃ x argPred retSpec, d.argName = some x ∧ d.retSpec = some retSpec ∧
    v = Value.closure x (Expr.externFn d.id x d.typ d.argPoison argPred retSpec d.effects) cᵢ.varEnv

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
  value_shape : ∃ x argPred retSpec, d.argName = some x ∧ d.retSpec = some retSpec ∧
    v = Value.peClosure x (Expr.externPfn d.id x d.typ d.argPoison argPred retSpec) cᵢ.varEnv

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

private theorem val_of_runtime
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

private theorem fn_of_runtime
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    {x : Name} {argPred : SyntaxPredicate} {retSpec : ExternReturn}
    (hkind : d.kind = .fn)
    (hlookup : cᵢ.registry.get? d.id = some impl)
    (harg : d.argName = some x)
    (hret : d.retSpec = some retSpec)
    (himpl : ∃ implFn, impl = ExternImpl.fn implFn)
    (hcfg : cₒ = cᵢ)
    (hval :
      v = Value.closure x (Expr.externFn d.id x d.typ d.argPoison argPred retSpec d.effects) cᵢ.varEnv) :
    ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v := by
  refine ExternDeclBoundaryRun.fn ?_
  exact
    { kind_fn := hkind
      lookup := hlookup
      argName_some := ⟨x, harg⟩
      retSpec_some := ⟨retSpec, hret⟩
      impl_fn := himpl
      output_config := hcfg
      value_shape := ⟨x, argPred, retSpec, harg, hret, hval⟩ }

private theorem pfn_of_runtime
    {d : ExternDeclaration} {impl : ExternImpl}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    {x : Name} {argPred : SyntaxPredicate} {retSpec : ExternReturn}
    (hkind : d.kind = .pfn)
    (hlookup : cᵢ.registry.get? d.id = some impl)
    (harg : d.argName = some x)
    (hret : d.retSpec = some retSpec)
    (himpl : ∃ implFn, impl = ExternImpl.pfn implFn)
    (hcfg : cₒ = cᵢ)
    (hval :
      v = Value.peClosure x (Expr.externPfn d.id x d.typ d.argPoison argPred retSpec) cᵢ.varEnv) :
    ExternDeclBoundaryRun d impl ctx res cᵢ cₒ v := by
  refine ExternDeclBoundaryRun.pfn ?_
  exact
    { kind_pfn := hkind
      lookup := hlookup
      argName_some := ⟨x, harg⟩
      retSpec_some := ⟨retSpec, hret⟩
      impl_pfn := himpl
      output_config := hcfg
      value_shape := ⟨x, argPred, retSpec, harg, hret, hval⟩ }

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
          effects := [], preds := [pred], argPoison := false }
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
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool} {argPred : SyntaxPredicate}
    {retSpec : ExternReturn} {effects : List Effect}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (ht : terminatesTo (Expr.externFn id x argTyp argPoison argPred retSpec effects) cᵢ cₒ v) :
    ∃ impl,
      ExternDeclBoundaryRun
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison }
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
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool} {argPred : SyntaxPredicate}
    {retSpec : ExternReturn}
    {ctx : TypeContext} {res : TypeResult}
    {cᵢ cₒ : Config} {v : Value}
    (ht : terminatesTo (Expr.externPfn id x argTyp argPoison argPred retSpec) cᵢ cₒ v) :
    ∃ impl,
      ExternDeclBoundaryRun
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison }
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

/-- Operational safety contract for a single trusted extern entry.

    Per-kind shape mirroring `RegistryOperationalSafe`'s clauses, so the
    bridge `TrustedRegistry.operationalSafe` is a direct unpacking.  The `d`
    parameter is retained for signature continuity with
    `ExternBoundarySpec.operational : ExternOperationalSafe d impl`, but the
    contract is determined entirely by `impl`'s constructor.

    Three clauses, one per `ExternImpl` constructor:

    * `fn` (impure): unconditional `nextAddr` monotonicity plus conditional
      memory/value well-formedness preservation.
    * `pfn` (pure): unchanged memory/`nextAddr`; well-formed return value
      under wf input.
    * `val`: stored value is `wfValue` at the consumer config's `nextAddr`. -/
def ExternOperationalSafe
    (_d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  (∀ (implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)),
      impl = ExternImpl.fn implFn →
    ∀ (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
      (vRaw : Value) (mem' : Memory) (addr' : Address),
      implFn env vArg mem addr = .ok (vRaw, mem', addr') →
      addr ≤ addr' ∧
      ((∀ a, mem.contains a → a < addr) →
        wfVarEnv addr env →
        wfValue addr vArg →
        (∀ a, mem'.contains a → a < addr') ∧ wfValue addr' vRaw))
  ∧
  (∀ (implPfn : VarEnv → Value → Memory → Except ExternError Value),
      impl = ExternImpl.pfn implPfn →
    ∀ (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
      (vRaw : Value),
      implPfn env vArg mem = .ok vRaw →
      (∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      wfValue addr vRaw)
  ∧
  (∀ (v : Value), impl = ExternImpl.val v →
    ∀ (cfg : Config), wfConfig cfg → wfValue cfg.nextAddr v)

/-- Registry-level operational safety contract.

    Consumed by the `_safe` variants of `beval_nextAddr_mono` and
    `wfConfig_preserved` in `SemanticsProperties.lean`.  The predicate is
    stated over raw `ExternImpl` payloads (`VarEnv → Value → Memory → ...`)
    rather than `ExternDeclaration` shapes, because `beval` exposes only the
    registry lookup `reg.get? id = some impl` — it does not have a
    syntactic declaration in scope.

    Three clauses, one per `ExternImpl` constructor:

    * `fn` — successful impure dispatch preserves the memory address bound,
      pushes `nextAddr` forward (monotonicity), and returns a `wfValue` at
      the new address cursor.
    * `pfn` — successful pure dispatch returns a `wfValue` at the unchanged
      address cursor.  Memory and `nextAddr` do not change.
    * `val` — a stored `Value` is `wfValue` at the `nextAddr` of any
      well-formed config that carries this registry.  The bound is the
      consumer's current `nextAddr`, not an absolute address. -/
def RegistryOperationalSafe (reg : ExternRegistry) : Prop :=
  -- (1) fn monotonicity (unconditional on input wfness): a trusted impure
  --     dispatch always pushes `nextAddr` forward.  Discharges
  --     `beval_nextAddr_mono` without needing a wf-input hypothesis.
  (∀ (id : ExternId)
      (implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)),
      reg.get? id = some (ExternImpl.fn implFn) →
    ∀ (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
      (vRaw : Value) (mem' : Memory) (addr' : Address),
      implFn env vArg mem addr = .ok (vRaw, mem', addr') →
      addr ≤ addr')
  ∧
  -- (2) fn wf preservation (conditional on wf input): output memory and
  --     return value are wf at the new `nextAddr`.  Discharges the impure
  --     branch of `wfConfig_preserved`.
  (∀ (id : ExternId)
      (implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)),
      reg.get? id = some (ExternImpl.fn implFn) →
    ∀ (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
      (vRaw : Value) (mem' : Memory) (addr' : Address),
      implFn env vArg mem addr = .ok (vRaw, mem', addr') →
      (∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      (∀ a, mem'.contains a → a < addr') ∧ wfValue addr' vRaw)
  ∧
  -- (3) pfn wf preservation: pure dispatch returns a wf value at the
  --     unchanged address cursor.
  (∀ (id : ExternId)
      (implPfn : VarEnv → Value → Memory → Except ExternError Value),
      reg.get? id = some (ExternImpl.pfn implPfn) →
    ∀ (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
      (vRaw : Value),
      implPfn env vArg mem = .ok vRaw →
      (∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      wfValue addr vRaw)
  ∧
  -- (4) val: a stored extern value is wf at the consumer's `nextAddr`.
  (∀ (cfg : Config), wfConfig cfg → cfg.registry = reg →
    ∀ (id : ExternId) (v : Value),
      reg.get? id = some (ExternImpl.val v) →
      wfValue cfg.nextAddr v)
