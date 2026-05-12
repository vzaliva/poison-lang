# FFI Axioms: Externs as FR-Preserving Boundary Steps

Status: the `ExternTypingAssumptions` structure and registry-aware
extern-boundary consumption are implemented and threaded through the
fault-robustness proof. The remaining design work is the constructor layer for
concrete trusted entries and the operational well-formedness projections.

Recent work records the runtime call boundary in `BevalAppSuccess` (`externFn` /
`externPfn` cases of successful `Expr.app`), factors the typing-side tag-meaning
bundle as `BoundaryTagMeaningPost` in `LeanProofs/StepFR.lean` (reachable from
`typecheck` via `StepFRApp.boundary_tag_meaning_post_of_typecheck`), and adds
the shared `TrustedRegistry` / extern-boundary scaffolding. Probe 2 is complete:
the public fault-robustness theorem is registry-aware and consumes trusted
extern boundary evidence under a populated registry. The remaining work is to
build reusable constructors for concrete trusted entries and then prove
end-to-end driver examples.

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
separate proof layer. The proposal factors this bundle into named predicates,
then requires registered externs to produce it at extern boundaries.

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
    (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning)
    (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop :=
  ∃ tm',
  BoundaryTagMeaningPost ctx res predSat tm tm' ∧
  ∃ θ₀' θ₁',
    wfExtendsMap θ₀ θ₀' ∧
    wfExtendsMap θ₁ θ₁' ∧
    valueHasETyp θ₀' o₀ res.qualType.etyp ∧
    valueHasETyp θ₁' o₁ res.qualType.etyp ∧
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

Once `StepFRPost` exists, `StepFR` becomes easier to read: its conclusion is
just `StepFRPost ...`, with the ordinary expression case discharging
`BoundaryTagMeaningPost` from `IsCanonicalExtension` plus
`PredSatLaws predSat tm'`. The FR boundary fields also conclude
`StepFRPost ...`; that is why applying an extern-boundary witness gives the
extern case exactly the facts the ordinary `StepFR` proof would need.

Today's `StepFR` also states `QTypRespectsTagMeaning tm' res.qualType` and
`wfTagMeaningCtx tm' (ctxAfter ctx res)` outside `IsCanonicalExtension`, even
though both are already projections of `IsCanonicalExtension`. Refactoring its
conclusion to `StepFRPost` should collapse those duplicates rather than
preserve them.

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

/-- Runtime/typechecking evidence for a successful extern declaration step.
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

/-- Runtime/typechecking evidence for a successful extern dispatch step.
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
- the source/typechecking equation for the declaration or closure application;
- the registry lookup equation `cᵢ.registry.get? id = some impl`;
- the implementation shape equation, such as `impl = ExternImpl.pfn f`;
- the runtime success equation for the implementation call;
- the `validateExternReturn` success equation for call boundaries;
- the exact output configuration equation;
- the captured runtime/type environment, argument value, and updated call
  environment for `callFn` / `callPfn`;
- the relevant `pureMode` condition for impure calls.

This is the main place where the proposal must be precise. If these payloads
are too weak, the `StepFRApp` and `wfConfig_preserved` extern branches will
still need ad-hoc inversion lemmas.

## The High-Level Contract

The central interface is one idea in two shapes: paired successful extern
boundary runs from clean-agreeing inputs produce `StepFRPost`.

```lean
def ExternDeclBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (ctx : TypeContext) (res : TypeResult)
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
      ∀ (a₀ a₁ : Address) (pm : Bool),
        wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } →
        wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
          cf₀ o₀ →
        ExternDeclBoundaryRun d impl ctx res
          { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
          cf₁ o₁ →
        StepFRPost ctx res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁

def ExternCallBoundaryFR
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (res : TypeResult) (predSat : PredSat) (tm : TagMeaning)
    (entry₀ entry₁ : ExternCallEntry),
    let ctx := entry₀.bodyCtx
    entry₁.bodyCtx = ctx →
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
      StepFRPost ctx res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁
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

There is also a smaller `StepFRSingleRunTagMeaningPost` helper in the current
code. It is essentially the tag-meaning fragment captured by
`BoundaryTagMeaningPost` (with some redundant projections from
`IsCanonicalExtension`). Factoring `BoundaryTagMeaningPost` should let that
helper become the one-run analogue of the same shared tag-meaning post rather
than a separate copy of the pattern.

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
```

Fields that do not apply to a declaration kind should be discharged by an
explicit kind-impossibility helper, not by informal convention. For example,
`callFR` and `callSingle` for a `.val` entry should be proved from the fact that
no `ExternCallBoundaryRun` can be constructed for a value implementation. If
that becomes awkward in Lean, specialize `ExternBoundarySpec` by declaration
kind or make the irrelevant fields optional.

The `single` fields are the extern analogues of the `StepFRSingle...` lemmas.
`wf` is a smaller operational projection for consumers such as
`wfConfig_preserved`. It should be generated by the same constructor/helper that
builds the FR and single-run fields, not treated as an independent trust burden.
The constructor API is part of the design, not optional polish.

For nested extern returns, the single-run contract has the same structural
dependency as the two-run FR contract: returned extern closures must satisfy the
closure typing and captured-environment consistency predicates that later
application proofs consume.

## Extern Assumptions and Registry Evidence

The fault-robustness theorem accepts extern assumptions as explicit inputs,
keeping the trust boundary visible at the public API and avoiding
implementation proofs for externs that are declared but never registered.

There are two trust inputs:

- `ExternTypingAssumptions` (implemented in `LeanProofs/ExternTypingAssumptions.lean`):
  generic assumptions about extern typechecking machinery, threaded through
  every consumer.
- `TrustedRegistry` (implemented): per-implementation evidence only for extern
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
    the fault-robustness proof.  Previously also carried a `guardProvenance`
    field; that was removed once the typechecker was tightened to erase
    predicates on extern effect writes under poisoned `pc` (mirroring
    assignment), which made the guard-origin trace structurally provable via
    `applyFnTClosure_extern_ok_memEnv_guard_origin`. -/
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

abbrev TrustedRegistry := Std.HashMap ExternId TrustedExternEntry

/-- Runtime registry projected from the trusted entries. -/
def TrustedRegistry.toRuntimeRegistry (tr : TrustedRegistry) : ExternRegistry :=
  tr.mapValues (fun entry => entry.impl)

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
    tr.get? id = some entry →
    entry.decl = d

/-- The public theorem uses the wider reachable domain: root AST externs plus
    externs reachable from callable closure data already present in the initial
    typed context. -/
def TrustedRegistryAgreesWithReachable
    (root : Expr) (ctxRoot : TypeContext) (tr : TrustedRegistry) : Prop :=
  ∀ {id d entry},
    ExternDeclarationReachableFromContext root ctxRoot id d →
    tr.get? id = some entry →
    entry.decl = d
```

The top-level theorem then becomes relative to both inputs:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
    (hTrust :
      ∀ {ctx : TypeContext},
        ctxMatchesInputSpec s ctx →
        TrustedRegistryAgreesWithReachable e ctx tr) :
  FaultRobustnessSpec
    (TrustedRegistry.toRuntimeRegistry tr) e s obs := ...
```

In the current runtime, `Config.registry` is the actual implementation map. The
registry-relative FR spec fixes successful runs to use the implementation
projection of the trusted registry: `TrustedRegistry.toRuntimeRegistry tr`.

Typing-side extern reasoning still uses `ExternTypingAssumptions` through the
FR spec. Structural induction threads expression reachability and a
`ContextReachableFrom` invariant while reusing the same trusted registry. Call
sites that need the relational boundary contract look up the trusted entry by
id; if `tr.get? id = some entry`, then `entry.spec.declFR` /
`entry.spec.callFR` are the relational boundary contracts, and
`entry.spec.declSingle` / `entry.spec.callSingle` are the single-run clean-pc
contracts. The `entry.spec.wf` field remains the operational well-formedness
projection for preservation consumers.

There is intentionally no obligation of the form "every extern declaration has
an implementation." If a trusted entry is absent, the projected runtime registry
has no implementation for that id; dispatch is a runtime error, not a
successful boundary event.

## Proof Status

The fault-robustness proof now consumes trusted extern evidence under a
populated registry:

- `bevalApp_structure` and related app inversion facts expose user and extern
  dispatch cases, including successful `ExternCallBoundaryRun.fn` and
  `ExternCallBoundaryRun.pfn` events.
- Extern declaration cases in `FaultRobustnessProofs.lean` no longer close by
  empty-registry contradiction. Successful `externVal`, `externFn`, and
  `externPfn` declaration runs consume `entry.spec.declFR` /
  `entry.spec.declSingle`.
- Application cases in `StepFRApp.lean` consume `entry.spec.callFR` /
  `entry.spec.callSingle` for runtime `externFn` / `externPfn` dispatch and
  transport the body-local boundary post back to the outer app post.
- Extern ids are present in `FnTClosure.extern` / `PFnTClosure.extern`, extern
  closures are covered by value typing, regime consistency, and clean
  agreement, and reachable declaration evidence is derived from typechecking
  instead of from a global "all ids are trusted" assumption.
- The public theorem is registry-relative:
  `TypeSystemEnforcesFaultRobustness` proves
  `FaultRobustnessSpec
  (TrustedRegistry.toRuntimeRegistry tr) e s obs` from
  `TrustedRegistryAgreesWithReachable` for every initial context admitted by
  the input spec.

Two operational well-formedness proof gaps remain in
`LeanProofs/SemanticsProperties.lean`:

- the `app` / `ExternImpl.fn` dispatch path of `wfConfig_preserved`, which
  should consume `entry.spec.wf` on `ExternCallBoundaryRun.fn`;
- the `externVal ref int` path of `wfConfig_preserved`, which should consume
  `entry.spec.wf` on `ExternDeclBoundaryRun.val`.

These are not FR proof blockers, but they are still part of the complete FFI
trust story. Concrete constructor work should make the `wf` projection cheap to
derive from the same implementation facts used for FR and single-run posts.

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

The runtime-boundary structures live in `LeanProofs/ExternBoundary.lean`:
`ExternDeclaration`, `TrustedExternEntry`, `TrustedRegistry`,
`TrustedRegistryAgreesWithReachable`, declaration/call boundary runs,
`ExternBoundarySpec`, and the reachable-domain provenance lemmas used by the
public theorem.

`TagMeaning` is threaded through typechecking, and structural extern allocation
extends the output tag table with exactly the resolved guard descriptors via
`ExternBatchTagMeaningExtension`. A successful extern boundary must still
identify the extended tag meaning under which post facts are stated. Today the
FR spec remains relative to `ExternTypingAssumptions.externPredSatDelta`; a
future API cleanup may move that obligation into per-extern trusted-entry
constructors so callers do not supply one broad typing-side axiom.

`ExternTypingAssumptions.guardProvenance` no longer exists: the typechecker
fix to `applyExternEffect` (predicate erasure under poisoned `pc`, mirroring
assignment) makes the guard-origin trace structurally provable, so the field
was removed and the call site at the impure-extern dispatch path now invokes
`applyFnTClosure_extern_ok_memEnv_guard_origin` directly.

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

The remaining work is now constructor and driver evidence, not registry-aware
proof-spine plumbing.

### Probe 1: Structural Prerequisites — Complete

Before any end-to-end extern proof, make extern closures and call boundaries
first-class proof objects:

- factor the `StepFR` conclusion so the tag-meaning extension layer is explicit
  (`BoundaryTagMeaningPost` / `StepFRPost`);
- fold the existing `StepFRSingleRunTagMeaningPost` pattern into the same
  `BoundaryTagMeaningPost` abstraction instead of maintaining a parallel
  tag-meaning postcondition;
- add `ExternId` to `FnTClosure.extern` and `PFnTClosure.extern`;
- teach `valueHasETyp`, `valueConsistentWithRegime`, `resultAgreesIfClean`,
  and closure-agreement helpers about extern closures;
- make `ExternDeclarationInProgram` traverse nested `ExternReturn` descriptors
  transitively, not only `Expr` nodes;
- make the call-boundary payload expose the body-entry context, captured env,
  argument value, unified env, and implementation success facts;
- strengthen `bevalApp_structure` with user and extern dispatch cases.

This is a prerequisite for even simple call examples such as `abs`, because the
caller must first evaluate an extern `pfn` declaration to a closure value before
the call boundary can execute.

### Probe 2: Registry-Aware Boundary Consumption — Complete

The step theorem consumes trusted boundary evidence under a populated runtime
registry:

- `StepFR` and the single-run IH families are registry-parametric;
- top-level `externVal` / `externFn` / `externPfn` branches consume
  `ExternBoundarySpec` declaration evidence;
- app proofs expose successful extern dispatch and consume call-boundary
  evidence;
- static closure-list membership is bridged to trusted registry lookup through
  reachable-domain provenance; and
- the public populated-registry theorem targets
  `TrustedRegistry.toRuntimeRegistry`.

The old Probe 2 checkpoint plan was removed after completion; this document is
now the roadmap for remaining FFI proof work.

### Probe 3: Boundary Constructors — Next

Write constructor lemmas before proving concrete drivers directly against the
full `StepFRPost` conjunction. At minimum:

- `ExternBoundarySpec.pureUnaryCleanInt`;
- `ExternBoundarySpec.constCleanInt`;
- `ExternBoundarySpec.nestedPfn`;
- `ExternBoundarySpec.refValInitialized`;
- `ExternBoundarySpec.impureCellUpdate`.

These constructors should derive the FR, single-run, and WF projections from a
small implementation-specific behavior lemma. Concrete drivers should not have
to assemble the raw `StepFRPost` conjunction by hand.

### Probe 4: End-to-End `abs`

After the registry-aware theorem path and `pureUnaryCleanInt` constructor
exist, prove a trusted entry for built-in `abs` (`@12`):

- construct the `TrustedExternEntry` for `@12`;
- prove its `ExternBoundarySpec`;
- build a `TrustedRegistry` containing that entry;
- supply the reachable-domain trust premise and the required
  `ExternTypingAssumptions` witness at the FR spec boundary;
- apply the resulting theorem to a small program that calls `abs`.

This is the minimal end-to-end exercise. It checks that trusted-boundary
evidence can actually be packaged, looked up, and consumed by the `StepFR`
extern branch. It does not test nested returned callables, so it is not enough
to validate the whole design.

### Probe 5: Built-In Curried `max`

Next prove `ExternBoundarySpec` for the built-in curried `max` externs:

- `@11`, the inner pure extern, receives captured `a` and argument `b`, returns
  `Value.num (max a b)`, and leaves memory/config unchanged.
- `@10`, the outer pure extern, receives `a` and returns a `Value.peClosure`
  whose body is `Expr.externPfn 11 ...` and whose captured runtime environment
  contains `a`.

This pair is a useful stress test. The `@11` proof checks that a clean numeric
result can be justified from the clean-agreement facts available at an extern
call boundary. If the call-boundary payload does not expose enough information
to derive equality of the two `max` results, the call-boundary payload is
underspecified.

The `@10` proof checks the nested-callable story. The returned value is not a
number; it is an extern closure that will be called later. The witness must
establish the `StepFRPost` closure facts for that returned callable, including
typing, regime consistency, and clean-result agreement. If this proof is
tractable, the high-level boundary contract is viable for realistic drivers.
If it becomes opaque, the boundary interface needs additional reusable
constructor lemmas for common extern patterns.

After `@10` / `@11`, the next low-risk sanity checks are:

- `@20`, an extern integer value;
- `@21`, a reference-valued extern value backed by the driver-initialized
  `errno` cell;
- `@22`, an impure extern function that updates the `errno` cell without
  allocating.

### Probe 6: API Stability

The FR boundary fields are intentionally coupled to `StepFRPost`. That is a
maintenance cost: if the main FR postcondition changes, every direct boundary
witness changes too.

The mitigation is the constructor layer from Probe 3. Concrete drivers prove
compact facts about their implementation and invoke those constructors. If
`StepFRPost` changes, most edits stay inside the constructors rather than every
registered extern proof.

### Probe 7: Single-Run Boundary Facts

The single-run fields overlap with the two-run postcondition, but they serve a
different consumer: the existing `StepFRSingle...` lemmas. They should remain
separate projections in `ExternBoundarySpec`.

`ExternBoundaryPreservesWF` is even smaller. It is for operational preservation
lemmas such as `wfConfig_preserved`, where the proof only needs final
well-formedness and does not need the full single-run clean-pc postcondition.

The proof effort should not be duplicated manually. The intended driver pattern
is to prove lower-level implementation facts once, then derive
the FR, single-run, and `ExternBoundaryPreservesWF` projections from those
shared facts.

## Open Questions

1. Move the `ExternTypingAssumptions.externPredSatDelta` obligation into the
   trusted registry interface as per-extern evidence and delete the broad field.
2. Decide whether `ExternBoundaryPreservesWF` should remain a field of
   `ExternBoundarySpec` or be exposed only as a derived projection from the
   constructor API. It should not become an independent third proof burden for
   drivers.
3. Decide how much convenience API to expose for reachable-domain trust when a
   driver registry is built from a finite list of trusted entries.

The resulting theorem is a clean relative statement: Poison's type system
enforces fault-robustness assuming every registered extern boundary is itself
fault-robustness preserving.
