# FFI Axioms: Externs as FR-Preserving Boundary Steps

Status: the registry-aware extern-boundary path is in place. The next proof
work is concrete boundary validation for the built-in externs, starting with
`abs` and then curried `max`.

The public fault-robustness theorem is relative to trusted extern boundary
evidence under a populated registry. The remaining work is to prove that the
concrete builtins can supply that evidence, tightening the boundary or the
builtin declarations if those direct proofs expose a mismatch. Reusable helper
machinery is secondary and should be extracted only from proof patterns that
actually repeat.

This document covers two pieces of the FFI trust story:

1. The `ExternTypingAssumptions` structure (in
   `LeanProofs/ExternTypingAssumptions.lean`), which packages the typing-side
   assumption extern typechecking depends on. The fault-robustness theorem is
   relative to a witness of this structure: every consumer threads it through
   the proof, and the public API requires callers to supply (or postulate) one.

2. The extern-boundary contract framework, which extends the same pattern to
   runtime extern dispatch by replacing per-implementation reasoning with a
   single FR-shaped property at every successful extern boundary. This hides
   frame, address, initialization, and non-leakage details behind a per-extern
   witness rather than exposing them to the core language theorem.

The current top-level theorem is relative:

> The Poison type system enforces fault-robustness for programs whose
> registered externs satisfy the extern-boundary FR contract.

This keeps the core language proof focused on Poison semantics and
typechecking, while making the FFI trust boundary explicit.

## Current Goal and Non-Goals

The immediate goal is to validate the extern boundary on the builtins that
motivated it:

- prove `ExternBoundarySpec` for the built-in `abs` extern, or identify the
  exact declaration/boundary reason it cannot be proved;
- prove `ExternBoundarySpec` for the two curried `max` extern entries, or
  identify the exact nested-callable boundary gap;
- preserve the public fault-robustness theorem shape: no new public
  precondition should be added to `TypeSystemEnforcesFaultRobustness`;
- keep executable semantics unchanged unless a concrete proof exposes that an
  extern declaration overclaims what the typechecker can justify.

This is not a framework-building exercise. The non-goals are:

- building a general library for proving arbitrary externs;
- proving every plausible extern pattern;
- factoring public constructor APIs before `abs` and `max` demonstrate a
  repeated proof shape;
- making concrete drivers avoid every occurrence of `StepFRPost` if the direct
  proof is tractable;
- accepting extern-specific shortcuts that native Poison code with the same
  typing summary could not justify.

Private local helpers are still useful when they reduce noise in the concrete
proofs, but they should be extracted only when a second builtin proof needs
the same shape. The likely lasting outcome of this exercise is either concrete
`abs` / `max` trusted entries, or a tightened `ExternBoundarySpec` /
declaration discipline discovered by trying to prove them.

## Core Idea

The current step theorem already states the exact postcondition the proof needs
after evaluating a well-typed expression. In `LeanProofs/StepFR.lean`, `StepFR`
first produces a canonical extension of the incoming tag meaning and then
concludes:

- the result type respects the extended tag meaning,
- `PredSatLaws` holds for the extended tag meaning,
- output values have the computed enriched type,
- output configs are well-formed,
- runtime states instantiate the post type context,
- regime consistency is preserved,
- clean context entries still agree,
- output values are regime-consistent,
- and clean outputs agree.

That bundle is the right contract for externs, but the tag-meaning layer must
remain explicit. `StepFR` does not merely prove facts under the incoming
`tm`; it returns some `tm'` such that `tm'` is the canonical extension for this
typed boundary and `PredSatLaws predSat tm'` holds. `StepFRPost` is just a name
for that full conclusion bundle. It is not an extra extern obligation and not a
separate proof layer.

```lean
/-- The tag-meaning part of the existing `StepFR` conclusion, abstracted away
    from syntax so it can also describe semantic extern call boundaries.

    For ordinary expression steps, this is obtained from
    `IsCanonicalExtension tm ctx e res tm'` plus `PredSatLaws predSat tm'`.
    For extern call boundaries, the boundary run facts must expose the same
    structural extension information directly, because the boundary is a
    semantic sub-event inside application rather than a source expression.

    `BoundaryTagMeaningPost` is produced by the boundary witness and consumed by
    the surrounding FR step.  For extern tag batches, the intended construction
    path is:
    `ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm'`
    for the structural part, then
    `ExternTypingAssumptions.externPredSatDelta` for
    `PredSatLaws predSat tm'`. -/
def BoundaryTagMeaningPost
    (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm tm' : TagMeaning) : Prop :=
  tm ⊑ tm' ∧
  TagMeaningBounded tm' res.nextTag' ∧
  wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
  QTypRespectsTagMeaning tm' res.qualType ∧
  PredSatLaws predSat tm'

/-- The existing large conjunction at the end of `StepFR`, factored out.
    This is not an additional property; it is the postcondition already
    required by the main FR proof. -/
def StepFRPost
    (ctx : TypeContext) (_e : Expr) (res : TypeResult) (predSat : PredSat)
    (tm : TagMeaning)
    (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop :=
  ∃ tm',
  BoundaryTagMeaningPost ctx res predSat tm tm' ∧
  PredSatLaws predSat tm' ∧
  QTypRespectsTagMeaning tm' res.qualType ∧
  ∃ θ₀' θ₁',
    wfExtendsMap θ₀ θ₀' ∧
    wfExtendsMap θ₁ θ₁' ∧
    valueHasETyp θ₀' o₀ res.qualType.etyp ∧
    valueHasETyp θ₁' o₁ res.qualType.etyp ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    wfTypeContext (ctxAfter ctx res) ∧
    TagBoundedCtx (ctxAfter ctx res) ∧
    wfConfig cf₀ ∧
    wfConfig cf₁ ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
    regimeConsistentWithCtx (ctxAfter ctx res) ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime
      (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime
      (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧
    agreeOnClean predSat (ctxAfter ctx res).regime
      (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀'
      cf₁.memory cf₁.varEnv θ₁' ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime
      res.qualType cf₀.memory θ₀' o₀ ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime
      res.qualType cf₁.memory θ₁' o₁ ∧
      resultAgreesIfClean predSat (ctxAfter ctx res).regime
        cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁
```

The `_e` parameter indexes the post by the expression whose typecheck produced
`res`; the post body does not inspect it, but downstream consumers use the
index to line up declaration and application proof paths without unfolding the
whole postcondition.

With `StepFRPost`, `StepFR` can state its conclusion as
`StepFRPost ...`, with the ordinary expression case discharging
`BoundaryTagMeaningPost` from `IsCanonicalExtension` plus
`PredSatLaws predSat tm'`. The FR boundary fields also conclude
`StepFRPost ...`; that is why applying an extern-boundary witness gives the
extern case exactly the facts the ordinary `StepFR` proof would need.

The boundary FR contracts should be understood as the same run-to-post pattern
as `StepFR`, but with different run relations. `StepFR` starts from two
successful `terminatesTo e` runs. Declaration and call boundary contracts start
from successful `ExternDeclBoundaryRun` or `ExternCallBoundaryRun` events. The
conclusion is the same `StepFRPost`.

For extern declarations, this is essentially `StepFR` specialized to
`Expr.externVal`, `Expr.externFn`, or `Expr.externPfn`, with the proof supplied
by trusted registry evidence. For extern dispatch, it is not just `StepFR`
restricted to a syntactic subset of `Expr`: the boundary is a semantic sub-event
inside application evaluation after the function and argument have already
evaluated.

## Extern Boundary Events

Externs appear at two proof boundaries. The first is expression evaluation of
extern declarations:

- `externVal`
- `externFn`
- `externPfn`

The second is runtime dispatch through an extern closure during application:

- impure `ExternImpl.fn`
- pure `ExternImpl.pfn`

These two boundaries should not have the same proof shape. Declaration
boundaries are top-level expression steps, so they line up closely with
`StepFR` for an extern expression. Call boundaries are semantic sub-events
inside `Expr.app`: they happen after the function and argument have already
evaluated, at the closure-body-entry context built from the captured
environment plus the argument binding.

```lean
inductive ExternDeclarationKind where
  | val
  | fn
  | pfn

inductive ExternBoundaryKind where
  | declVal
  | declFn
  | declPfn
  | callFn
  | callPfn

/-- Static declaration shape extracted from the source program. -/
structure ExternDeclaration where
  id      : ExternId
  kind    : ExternDeclarationKind
  typ     : Typ
  argName : Option Name
  retSpec : Option ExternReturn
  effects : List Effect
  preds   : List SyntaxPredicate

/-- Runtime evidence for a successful extern declaration step.
    The input configuration is the input of the extern expression itself. -/
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

/-- The body-entry state for an extern call. This is the context/state that
    `StepFRApp` constructs after evaluating the function and argument and
    combining the closure's captured environment with the argument binding. -/
structure ExternCallEntry where
  bodyCtx      : TypeContext
  callConfig   : Config
  capturedEnv  : VarEnv
  argName      : Name
  argValue     : Value
  unifiedEnv   : VarEnv

/-- Runtime evidence for a successful extern dispatch step.
    The input is an intermediate call-entry state, not the original input state
    of the surrounding `Expr.app`. -/
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
```

The fact payloads should include at least:

- the declaration id and kind, matching `d`;
- the registry lookup equation `cᵢ.registry.get? id = some impl`;
- the implementation shape equation, such as `impl = ExternImpl.pfn f`;
- the runtime success equation for the implementation call;
- the `validateExternReturn` success equation for call boundaries;
- the exact output configuration equation;
- the captured runtime/type environment, argument value, and updated call
  environment for `callFn` / `callPfn`;
- the relevant `pureMode` condition for impure calls.

Typechecking-origin evidence is deliberately separate. The runtime payloads
should not duplicate typechecker conclusions about `res`; the theorem-facing
contracts receive `ExternBoundaryTyping.Decl` or `ExternBoundaryTyping.Call`
witnesses that connect the boundary result to the successful typechecking or
closure-application path that produced it.

These payloads are the main precision point. If the direct `abs` or `max`
proofs cannot recover a required fact, tighten this boundary evidence rather
than duplicating typechecker conclusions in runtime-only payloads.

## The High-Level Contract

The central interface is one idea in two shapes: paired successful extern
boundary runs from clean-agreeing inputs produce `StepFRPost`. The displayed
signatures mirror `LeanProofs/ExternBoundary.lean`; that file is authoritative
if the implementation changes.

```lean
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
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀,
                   pureMode := pm, registry := registry } →
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁,
                   pureMode := pm, registry := registry } →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₀, varEnv := ρ₀, nextAddr := a₀,
            pureMode := pm, registry := registry }
          cf₀ o₀ →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₁, varEnv := ρ₁, nextAddr := a₁,
            pureMode := pm, registry := registry }
          cf₁ o₁ →
        StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

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
    -- `BodyEntryInputsAgree` packages the full StepFR input-hypothesis set at
    -- the closure-body-entry context: wfRealizationMap, wfTypeContext,
    -- TagBoundedCtx, runtimeInstantiatesCtx for both runs,
    -- regimeConsistentWithCtx, consistentWithRegime for both runs,
    -- agreeOnClean, and wfConfig for both entry configs.
    ∀ (θ₀ θ₁ : RealizationMap),
    BodyEntryInputsAgree predSat ctx entry₀ entry₁ θ₀ θ₁ →
    ∀ (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      ExternCallBoundaryRun d impl entry₀ res cf₀ o₀ →
      ExternCallBoundaryRun d impl entry₁ res cf₁ o₁ →
      StepFRPost ctx postExpr res predSat tm θ₀ θ₁
        (entry₀.bodyOutputConfig cf₀) (entry₁.bodyOutputConfig cf₁) o₀ o₁
```

`ExternDeclBoundaryFR` is the extern-declaration analogue of `StepFR`.
`ExternCallBoundaryFR` is the extern-call analogue of the user-closure body IH
inside `StepFRApp`: its context is the body-entry context, not the caller's
top-level application context. Both contracts must provide the tag-meaning
extension hidden inside `StepFRPost`. For declaration boundaries this should
line up with the same `IsCanonicalExtension` story as an ordinary extern
expression. For call boundaries it should be a boundary-specific structural
witness for the tags allocated while typechecking the extern closure member.
Any low-level facts about effects, address allocation, memory domain, predicate
satisfaction, or return-value non-leakage are internal ways to justify these
contracts; they are not required by the core Poison theorem.

## Single-Run Boundary Contract

The proof stack also has one-run facts. In `LeanProofs/StepFR.lean`,
`StepFRSingleRunFinalCleanPcTrue` and
`StepFRSingleRunFinalCleanPcTrueMaskedRegParam` have the same shape as
`StepFR`, but with one successful run instead of two. They produce the
single-run preservation facts needed when the final pc is clean.

Externs should get the same treatment. The boundary interface should include
single-run declaration and call contracts whose conclusions mirror the existing
`StepFRSingle...` postcondition, but whose run premises are
`ExternDeclBoundaryRun` / `ExternCallBoundaryRun` rather than `terminatesTo e`.

```lean
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
      ∀ (a : Address) (pm : Bool),
        wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
          cf o →
        ctx.pc = true →
        ExternBoundarySinglePost ctx res predSat tm θ μ cf o

def ExternCallBoundarySingle
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  -- Same single-run clean-pc postcondition, stated at the call body's
  -- `ExternCallEntry.bodyCtx` and `ExternCallEntry.unifiedEnv`.  This should
  -- thread `tm` and conclude `ExternBoundarySinglePost`, exactly as the
  -- declaration contract above does.
  ...

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

def ExternOperationalSafe
    (_d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  (∀ implFn, impl = ExternImpl.fn implFn →
    ∀ env vArg mem addr vRaw mem' addr',
      implFn env vArg mem addr = .ok (vRaw, mem', addr') →
      addr ≤ addr' ∧
      ((∀ a, mem.contains a → a < addr) →
        wfVarEnv addr env →
        wfValue addr vArg →
        (∀ a, mem'.contains a → a < addr') ∧ wfValue addr' vRaw))
  ∧
  (∀ implPfn, impl = ExternImpl.pfn implPfn →
    ∀ env vArg mem addr vRaw,
      implPfn env vArg mem = .ok vRaw →
      (∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      wfValue addr vRaw)
  ∧
  (∀ v, impl = ExternImpl.val v →
    ∀ (cfg : Config), wfConfig cfg → wfValue cfg.nextAddr v)

structure ExternBoundarySpec
    (d : ExternDeclaration) (impl : ExternImpl) : Prop where
  declFR : ExternDeclBoundaryFR d impl
  callFR : ExternCallBoundaryFR d impl
  declSingle : ExternDeclBoundarySingle d impl
  callSingle : ExternCallBoundarySingle d impl
  operational : ExternOperationalSafe d impl
```

Fields that do not apply to a declaration kind should be discharged by an
explicit kind-impossibility helper, not by informal convention. For example,
`callFR` and `callSingle` for a `.val` entry should be proved from the fact that
no `ExternCallBoundaryRun` can be constructed for a value implementation. If
that becomes awkward in Lean, specialize `ExternBoundarySpec` by declaration
kind or make the irrelevant fields optional.

The `single` fields are the extern analogues of the `StepFRSingle...` lemmas.
`operational` is a per-kind operational projection consumed by
`wfConfig_preserved` and `beval_nextAddr_mono` in `SemanticsProperties.lean`:
its three clauses mirror `RegistryOperationalSafe`'s shape so the bridge from
a trusted registry to runtime safety is a direct unpacking.  Each clause
should be proved from the same concrete implementation facts used by the FR and
single-run fields, not treated as an unrelated trust burden. A helper may
package those facts if it emerges naturally from the `abs` / `max` proofs, but
a public constructor API is not required for the current validation goal.

For nested extern returns, the single-run contract has the same structural
dependency as the two-run FR contract: returned extern closures must satisfy the
closure typing and captured-environment consistency predicates that later
application proofs consume.

## Extern Assumptions and Registry Evidence

The fault-robustness theorem accepts extern assumptions as explicit inputs,
keeping the trust boundary visible at the public API and avoiding
implementation proofs for externs that are declared but never registered.

There are two trust inputs:

- `ExternTypingAssumptions` (in `LeanProofs/ExternTypingAssumptions.lean`):
  generic assumptions about extern typechecking machinery, threaded through
  every consumer.
- `TrustedRegistry`: per-implementation evidence only for extern
  ids that are present in the runtime registry. Each trusted entry stores the
  implementation, the declaration shape it implements, and the boundary proof
  for that pair.

This distinction matters for conditionals. Both branches of an `if` typecheck,
so extern declarations in an unexecuted branch may still need the generic
typing assumptions. But if that branch is not executed, there is no successful
extern boundary run, so no implementation-level boundary proof is consumed.

```lean
/-- Generic typing-side assumptions about the extern typechecking machinery.
    Defined in `LeanProofs/ExternTypingAssumptions.lean` and threaded through
    the fault-robustness proof. -/
structure ExternTypingAssumptions where
  externPredSatDelta :
    ∀ (predSat : PredSat)
      {tm tm' : TagMeaning}
      {nextTag nextTag' : Tag}
      {mapping : TagMapping}
      {preds : List SyntaxPredicate}
      {env : VarTypeEnv},
      PredSatLaws predSat tm →
      ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' →
      PredSatLaws predSat tm'

structure TrustedExternEntry where
  decl : ExternDeclaration
  impl : ExternImpl
  spec : ExternBoundarySpec decl impl

abbrev TrustedRegistry := List TrustedExternEntry

namespace TrustedRegistry

def lookup? : TrustedRegistry → ExternId → Option TrustedExternEntry := ...

/-- Runtime registry projected from the trusted entries. -/
def toRuntimeRegistry (tr : TrustedRegistry) : ExternRegistry :=
  tr.foldr (fun entry reg => reg.insert entry.decl.id entry.impl) emptyExternRegistry

end TrustedRegistry

/-- Predicate saying expression `e` contains, or can synthesize through a
    nested extern return descriptor, an extern declaration with id `id` and
    declaration shape `d`. The concrete definition must walk both `Expr` and
    `ExternReturn` descriptors transitively. -/
def ExternDeclarationInProgram
    (e : Expr) (id : ExternId) (d : ExternDeclaration) : Prop := ...

/-- A trusted entry is allowed only when its declaration shape agrees with the
    extern declaration under the same id in the program. This is intentionally
    partial: declarations may appear in the program without trusted entries. -/
def TrustedRegistryAgreesWithProgram (e : Expr) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationInProgram e id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d

/-- The public theorem uses the wider reachable domain: root AST externs plus
    externs reachable from callable closure data already present in the initial
    typed context. -/
def TrustedRegistryAgreesWithReachable
    (root : Expr) (ctxRoot : TypeContext) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationReachableFromContext root ctxRoot id d →
    TrustedRegistry.lookup? tr id = some entry →
    entry.decl = d
```

The top-level theorem is relative to both inputs.  It is now
trusted-registry-facing and takes registry trust *per initial context*
(`InitialContextTrusted tr e ctx`, which is `TrustedRegistryAgreesWithReachable e
ctx tr`) as part of `FaultRobustnessSpec`, rather than as a single all-context
premise:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  FaultRobustnessSpec tr e s obs := ...
```

The old all-context premise survives as the corollary
`TypeSystemEnforcesFaultRobustness_allCtx`, concluding the renamed
registry-parametric spec `FaultRobustnessSpecForRegistry
(TrustedRegistry.toRuntimeRegistry tr) e s obs`; that all-context premise is
unprovable for a non-empty registry (see `doc/extern-regime.md`).

In the current runtime, `Config.registry` is the actual implementation map. The
registry-relative FR spec fixes successful runs to use the implementation
projection of the trusted registry: `TrustedRegistry.toRuntimeRegistry tr`.

Typing-side extern reasoning still uses `ExternTypingAssumptions` through the
FR spec. Structural induction threads expression reachability and a
`ContextReachableFrom` invariant while reusing the same trusted registry. Call
sites that need the relational boundary contract look up the trusted entry by
id; if `TrustedRegistry.lookup? tr id = some entry`, then `entry.spec.declFR` /
`entry.spec.callFR` are the relational boundary contracts, and
`entry.spec.declSingle` / `entry.spec.callSingle` are the single-run clean-pc
contracts. The `entry.spec.operational` field (`ExternOperationalSafe d impl`)
asserts that a successful extern boundary preserves `wfConfig`, produces a
`wfValue` at the output `nextAddr`, and pushes the address cursor forward
(`cᵢ.nextAddr ≤ cₒ.nextAddr`).

There is intentionally no obligation of the form "every extern declaration has
an implementation." If a trusted entry is absent, the projected runtime registry
has no implementation for that id; dispatch is a runtime error, not a
successful boundary event.

## Relationship to `LeanProofs/ExternTypingAssumptions.lean`

`LeanProofs/ExternTypingAssumptions.lean` contains the typing-side contract
floor:

- `TagMappingRespectsTagMeaning` — the semantic predicate that fresh-tag
  allocation must respect a `TagMeaning`.
- `ExternBatchTagMeaningExtension` — the structural extension predicate for
  one extern allocation batch (submap, boundedness, respects).
- `ExternTypingAssumptions` — the structure with one field:
  - `externPredSatDelta`: `PredSatLaws` preservation across one structural
    extern allocation batch.

The runtime-boundary structures are split across two modules:

- `LeanProofs/ExternRuntime.lean` (below `StepFR` in the dependency graph)
  contains runtime-event predicates that do not depend on FR-shaped machinery:
  `ExternDeclaration`, `ExternDeclBoundaryRun`, `ExternCallEntry`,
  `ExternCallBoundaryRun`, `ExternBoundaryWFRun`, the operational safety
  contracts `ExternOperationalSafe` (per trusted entry) and
  `RegistryOperationalSafe` (per registry, consumed by
  `SemanticsProperties.lean`).
- `LeanProofs/ExternBoundary.lean` (above `StepFR`) contains the FR-shaped
  theorem-facing API: `TrustedExternEntry`, `TrustedRegistry` (with the
  `operationalSafe` bridge to `RegistryOperationalSafe`),
  `TrustedRegistryAgreesWithReachable`, `BodyEntryInputsAgree`,
  `ExternBoundarySpec` (with `declFR`, `callFR`, `declSingle`, `callSingle`,
  and `operational` fields), and the reachability inductives
  (`ExternDeclarationReachableFromExpr` etc.) along with their navigation
  theorems.
- `LeanProofs/ExternBoundaryProofs.lean` (above `ExternBoundary`) carries
  the proof-heavy resolution and integration theorems for the
  trusted-registry agreement predicates (`TrustedRegistryAgreesWithProgram`
  / `TrustedRegistryAgreesWithReachable` resolveDeclaration variants, call
  boundary integration theorems, captured-environment/QTyp reachability
  navigation namespaces).  Consumers that need these proof bodies import
  this file instead of (or in addition to) `ExternBoundary.lean`.

`TagMeaning` is threaded through typechecking, and structural extern allocation
extends the output tag table with exactly the resolved guard descriptors via
`ExternBatchTagMeaningExtension`. A successful extern boundary must still
identify the extended tag meaning under which post facts are stated.

## Trust Boundary

The trusted boundary is intentionally large:

- it trusts registered extern implementations to preserve runtime
  well-formedness;
- it trusts them not to leak poisoned information into clean observations;
- it trusts extern declarations and returned extern callables to match their
  typechecking summaries;
- it trusts any tag-meaning and regime facts needed by the postcondition.

Runtime validation is weaker than this boundary. `validateExternReturn` checks
outer runtime shape, but `StepFRPost` also requires predicate-level and
regime-level facts such as `valueConsistentWithRegime` and
`resultAgreesIfClean`. A driver proof for a simple extern like `abs` must
establish those facts from the implementation's behavior; it cannot get them
from runtime shape validation alone.

This is appropriate when externs model host functions, separately verified
components, or abstract primitives. If a specific extern should be verified
inside Lean, one can later prove the relevant declaration/call boundary fields
from more detailed lemmas. The core FR theorem does not need to know those
details.

## Roadmap

The remaining work is now concrete builtin boundary evidence, not
registry-aware proof-spine plumbing and not a general constructor framework.

### 1. Direct `abs` Boundary Validation

Prove the built-in `abs` extern (`@12`) directly against
`ExternBoundarySpec` in `LeanProofs/ExternProofs.lean`, using only small
private helpers where they immediately reduce proof noise. Do not design a
public constructor first.

The current examples declare `abs` as:

```poison
extern pfn @12 x : (int) -> ((int :> clean {}))
```

That declaration is intentionally part of the spike. Under the no-shortcut
discipline above, it may overclaim: a clean no-predicate output from a possibly
dirty argument is sound only if the native analogue can justify the same clean
result, or if the trusted extern proof supplies an equivalent declassification
argument.

Before the proof, compare the current `abs` declaration with the native Poison
analogue. The current typechecker treats regular function application by
binding the argument with its qualified type and then typechecking the body; it
does not blindly join the argument poison into the result. Therefore a clean
extern result is acceptable only when the analogous native body could justify
that clean result by the same dependency, guard, or input-insensitivity
discipline.

Done means one of two outcomes:

- `TrustedExternEntry` / `ExternBoundarySpec` for `@12` compiles without new
  `sorry` or `axiom`; or
- the proof reaches a concrete false or missing obligation, and the document
  records whether the fix is to tighten the `abs` declaration, tighten
  `ExternBoundarySpec`, or expose a missing boundary payload fact.

Validation result: the direct `abs` check reaches the second outcome.  The
current `@12` declaration overclaims a clean result.  `LeanProofs/ExternProofs.lean`
records the proof-side declaration and implementation shape, plus
`ExternProofs.builtinAbs_cleanPost_obstruction`: for a clean integer result,
`StepFRPost` requires `resultAgreesIfClean`, but `abs` is input-sensitive and
dirty integer inputs need not agree.  Concretely, the implementation can return
`1` for `-1` and `2` for `2`, and those outputs cannot satisfy clean integer
agreement.  The appropriate fix is to tighten the `abs` declaration (for
example, stop promising `clean {}` for a possibly dirty argument) unless a
future declassification-style proof obligation is added.

This is the minimal boundary validation exercise. It checks that trusted
boundary evidence can actually be packaged, looked up, and consumed by the
`StepFR` extern branch. It does not validate nested returned callables.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternProofs.lean
make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean
```

### 2. Direct Built-In Curried `max`

After `abs`, prove `ExternBoundarySpec` directly for the built-in curried
`max` externs:

- `@11`, the inner pure extern, receives captured `a` and argument `b`, returns
  `Value.num (max a b)`, and leaves memory/config unchanged.
- `@10`, the outer pure extern, receives `a` and returns a `Value.peClosure`
  whose body is `Expr.externPfn 11 ...` and whose captured runtime environment
  contains `a`.

This pair is the main stress test. The `@11` proof checks that clean numeric
results can be justified from exactly the clean-agreement facts available at an
extern call boundary. The `@10` proof checks the nested-callable story: the
returned value is an extern closure that will be called later, so the witness
must establish the closure typing, regime consistency, and clean-result
agreement facts consumed by later application proofs.

As with `abs`, do not introduce public constructors before trying the direct
proof. If a helper from the `abs` proof is reused here, it can remain private
until there is a third use.

### 3. Boundary Tightening If Needed

If the direct `abs` or `max` proofs fail for semantic rather than tactical
reasons, tighten the boundary or declaration discipline at the smallest point:

- If a builtin declaration promises a clean result that the native analogue
  could not justify, revise that declaration or its proof-side trust
  obligation.
- If `ExternBoundarySpec` lacks typechecking-origin, body-entry, captured-env,
  or implementation-success evidence required for a valid proof, add that
  evidence to the boundary path rather than duplicating typechecker facts in
  runtime payloads.
- If a predicate-checked extern is intended to de-poison, require a formal
  proof that the implementation's value-level check semantically matches the
  declared predicate used by the typechecker.

Any such change must state its impact on soundness, precision, executable
semantics, and the public fault-robustness theorem.

### 4. Optional Helper Extraction

Only after `abs` and `max` are proved, review the proof bodies for repeated
shapes. Extract a public helper or constructor only if it removes real
duplication across those concrete proofs.

Non-goal: expose a complete set of constructors for arbitrary externs.
`LeanProofs/ExternProofs.lean` is the concrete home for the built-in `abs` and
`max` proofs. `LeanProofs/ExternBoundaryConstructors.lean` currently contains
private helper experiments. Do not extend it as a framework by default; either
ignore it or reuse only tiny private helpers that directly shorten the concrete
proofs.

If more coverage is desired later, the next checks are:

- low risk: `@20`, an extern integer value;
- medium risk: `@21`, a reference-valued extern value backed by the driver-initialized
  `errno` cell;
- high risk: `@22`, the impure `set_err` extern. It mutates the fixed
  driver-allocated `errno` cell without allocation and is the first proof that
  the impure-`fn` boundary handles clean-memory agreement, not just returned
  values.

### 5. Single-Run and Operational Facts

The single-run fields overlap with the two-run postcondition, but they serve a
different consumer: the existing `StepFRSingle...` lemmas. They should remain
separate projections in `ExternBoundarySpec`.

`ExternOperationalSafe` (the type of `entry.spec.operational`) is the
operational projection.  Its three clauses (fn, pfn, val) supply the
per-kind facts about memory bounds, returned-value well-formedness, and
`nextAddr` monotonicity for impure calls, consumed by `wfConfig_preserved`
and `beval_nextAddr_mono` in `SemanticsProperties.lean` via the
`TrustedRegistry.operationalSafe` bridge.

The proof effort should not be duplicated manually. The intended driver pattern
is to prove lower-level implementation facts once, then derive
the FR, single-run, and operational projections from those shared facts.
