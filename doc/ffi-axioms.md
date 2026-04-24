# FFI Axioms: Externs as FR-Preserving Boundary Steps

Status: the `ExternTypingAssumptions` structure is implemented and threaded
through the fault-robustness proof; the broader extern-boundary design below
is a proposal.

This document covers two pieces of the FFI trust story:

1. The `ExternTypingAssumptions` structure (in
   `LeanProofs/ExternTypingAssumptions.lean`), which packages the two typing-side
   assumptions extern typechecking depends on. The fault-robustness theorem is
   relative to a witness of this structure: every consumer threads it through
   the proof, and the public API requires callers to supply (or postulate) one.

2. A proposed extern-boundary contract framework that would extend the same
   pattern to runtime extern dispatch, replacing per-implementation reasoning
   with a single FR-shaped property at every successful extern boundary. This
   would hide frame, address, initialization, and non-leakage details behind a
   per-extern witness rather than exposing them to the core language theorem.

The intended top-level theorem (with the boundary contract in place) is
relative:

> The Poison type system enforces fault-robustness for programs whose
> registered externs satisfy the extern-boundary FR contract.

This keeps the core language proof focused on Poison semantics and
typechecking, while making the FFI trust boundary explicit.

## Core Idea

The current step theorem already states the exact postcondition the proof needs
after evaluating a well-typed expression. In `LeanProofs/StepFR.lean`, `StepFR`
concludes:

- the result type respects the tag meaning,
- output values have the computed enriched type,
- output configs are well-formed,
- runtime states instantiate the post type context,
- regime consistency is preserved,
- clean context entries still agree,
- output values are regime-consistent,
- and clean outputs agree.

That bundle is the right contract for externs. `StepFRPost` is just a name for
that conclusion bundle. It is not an extra extern obligation and not a separate
proof layer. The proposal factors this bundle into a named predicate, then
requires registered externs to produce it at extern boundaries.

```lean
/-- The existing large conjunction at the end of `StepFR`, factored out.
    This is not an additional property; it is the postcondition already
    required by the main FR proof. -/
def StepFRPost
    (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning)
    (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop :=
  QTypRespectsTagMeaning tm res.qualType ∧
  ∃ θ₀' θ₁',
    wfExtendsMap θ₀ θ₀' ∧
    wfExtendsMap θ₁ θ₁' ∧
    valueHasETyp θ₀' o₀ res.qualType.etyp ∧
    valueHasETyp θ₁' o₁ res.qualType.etyp ∧
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧
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
just `StepFRPost ...`. The FR boundary fields also conclude `StepFRPost ...`;
that is why applying an extern-boundary witness gives the extern case exactly
the facts the ordinary `StepFR` proof would need.

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
top-level application context. Any low-level facts about effects, address
allocation, memory domain, predicate satisfaction, or return-value non-leakage
are internal ways to justify these contracts; they are not required by the core
Poison theorem.

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
    (predSat : PredSat)
    (θ : RealizationMap)
    (μ : Memory) (cf : Config) (o : Value) : Prop :=
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
        ExternBoundarySinglePost ctx res predSat θ μ cf o

def ExternCallBoundarySingle
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  -- Same single-run clean-pc postcondition, stated at the call body's
  -- `ExternCallEntry.bodyCtx` and `ExternCallEntry.unifiedEnv`.
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
- `TrustedRegistry` (proposed): per-implementation evidence only for extern
  ids that are present in the runtime registry. Each trusted entry would store
  the implementation, the declaration shape it implements, and the boundary
  proof for that pair.

This distinction matters for conditionals. Both branches of an `if` typecheck,
so extern declarations in an unexecuted branch may still need the generic
typing assumptions. But if that branch is not executed, there is no successful
extern boundary run, so no implementation-level boundary proof is consumed.

```lean
/-- Generic typing-side assumptions about the extern typechecking machinery.
    Defined in `LeanProofs/ExternTypingAssumptions.lean` and threaded through the
    fault-robustness proof. These assumptions are generic facts about extern
    typechecking, not per-runtime-implementation safety facts. -/
structure ExternTypingAssumptions where
  tagSoundness :
    ∀ (tm : TagMeaning) (mapping : TagMapping)
      (preds : List SyntaxPredicate) (env : VarTypeEnv)
      (nextTag nextTag' : Tag),
      collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag') →
      TagMappingRespectsTagMeaning tm mapping preds env

  guardProvenance :
    ∀ (ctx : TypeContext) (r : TypeResult),
      ImpureExternCallOk ctx r →
      ctx.pc = true →
      ∀ (l : Loc) (k : Tag) (qt_out : QTyp),
        trustedGuardedCell r.memEnv' r.regime' l k qt_out →
        ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in

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
```

The top-level theorem then becomes relative to both inputs:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (e : Expr)
    (tr : TrustedRegistry)
    (hTrust : TrustedRegistryAgreesWithProgram e tr)
    (extTyping : ExternTypingAssumptions)
    (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := ...
```

In the current runtime, `Config.registry` is the actual implementation map.
The FR theorem must connect the initial runtime configs to the implementation
projection of the trusted registry, for example by requiring the initial
configs' `registry` fields to equal `tr.toRuntimeRegistry`.

Typing-side extern reasoning uses `extTyping`. Structural induction decomposes
`hTrust` for subexpressions while reusing the same trusted registry. Call sites
that need the relational boundary contract look up the trusted entry by id; if
`tr.get? id = some entry`, then `entry.spec.declFR` / `entry.spec.callFR` are
the relational boundary contracts, `entry.spec.declSingle` /
`entry.spec.callSingle` are the single-run clean-pc contracts, and
`entry.spec.wf` is the operational well-formedness contract.

There is intentionally no obligation of the form "every extern declaration has
an implementation." If a trusted entry is absent, the projected runtime registry
has no implementation for that id; dispatch is a runtime error, not a
successful boundary event.

## Proof Gaps Addressed

### `bevalApp_structure`

`LeanProofs/SemanticsProperties.lean` has a `bevalApp_structure`
gap because the existing inversion lemma assumes only user-closure dispatch. The
extern runtime adds extra successful branches for extern closure bodies.

Under this approach, the inversion lemma should be strengthened to expose all
successful dispatch cases:

- user closure body evaluation,
- pure user closure body evaluation,
- impure extern dispatch described by `ExternCallBoundaryRun.fn`,
- pure extern dispatch described by `ExternCallBoundaryRun.pfn`.

This is not a cosmetic change. The current inversion proof is incomplete, and
the statement does not expose extern dispatch. The strengthened operational
inversion lemma is part of the main proof budget; the high-level extern
contract only makes the extern branch easy to consume after the branch has been
exposed.

### `wfConfig_preserved`, application extern dispatch

The `app` case of `wfConfig_preserved` needs to show that a successful
`ExternImpl.fn` dispatch returns a well-formed config and value. The proof can
look up the trusted entry by id and use `entry.spec.wf` on the
`ExternCallBoundaryRun.fn` branch.

No separate frame, domain, or address monotonicity lemma is needed in the main
proof. Those facts may be how a concrete driver justifies the `wf` field, but
the core proof only consumes the high-level result.

### `wfConfig_preserved`, `externVal ref int`

The `externVal` case needs `wfValue nextAddr (Value.loc a)` when the registered
extern value is a reference. The proof can look up the trusted entry by id and
use `entry.spec.wf` on the `ExternDeclBoundaryRun.val` branch.

This hides the details of address bounds, runtime memory presence, and reference
initialization behind the trusted boundary. If a driver registers a bad
reference, it cannot supply the `wf` field.

### Former `terminatesTo_extern_absurd` sites

The FR proof currently closes extern declaration cases vacuously under an empty
registry. Once a populated registry is threaded into the theorem, successful
extern declaration evaluations are no longer contradictory.

In those cases, the proof looks up the trusted entry by id and invokes
`entry.spec.declFR` on the declaration boundary:

- `ExternDeclBoundaryRun.val` for `externVal`,
- `ExternDeclBoundaryRun.fn` for `externFn`,
- `ExternDeclBoundaryRun.pfn` for `externPfn`.

The witness directly provides `StepFRPost`, including result typing,
tag-meaning obligations, regime consistency, runtime instantiation, and clean
result agreement.

### Extern fn/pfn dispatch in `StepFRApp`

When application evaluates a closure whose body is `Expr.externFn` or
`Expr.externPfn`, the proof invokes `entry.spec.callFR` on:

- `ExternCallBoundaryRun.fn`, or
- `ExternCallBoundaryRun.pfn`.

The witness supplies the postconditions that the ordinary user-closure proof
would otherwise derive structurally from the function body.

## Relationship to `LeanProofs/ExternTypingAssumptions.lean`

`LeanProofs/ExternTypingAssumptions.lean` contains:

- `TagMappingRespectsTagMeaning` — the semantic predicate that fresh-tag
  allocation must respect a `TagMeaning`.
- `trustedGuardedCell` — a cell predicate used by impure-extern guard
  provenance.
- `ImpureExternCallOk` — an existential witness that an impure extern call
  succeeded.
- `ExternTypingAssumptions` — the structure with two fields:
  - `tagSoundness` (Contract A): fresh-tag allocation respects an arbitrary
    `TagMeaning`.
  - `guardProvenance` (Contract B): impure-extern guard provenance under a
    poisoned program counter.

If the extern-boundary design above is implemented, this file would also
contain:

- `ExternDeclaration`
- `TrustedExternEntry`
- `TrustedRegistry`
- `TrustedRegistry.toRuntimeRegistry`
- `ExternDeclarationInProgram`
- `TrustedRegistryAgreesWithProgram`
- `ExternDeclBoundaryRun`
- `ExternCallEntry`
- `ExternCallBoundaryRun`
- `StepFRPost` or an import of it from `StepFR.lean`
- `ExternDeclBoundaryFR`
- `ExternCallBoundaryFR`
- `ExternBoundarySinglePost`
- `ExternDeclBoundarySingle`
- `ExternCallBoundarySingle`
- `ExternBoundaryWFRun`
- `ExternBoundaryPreservesWF`
- `ExternBoundarySpec`
- helper lemmas for looking up declaration and implementation evidence

`ExternTypingAssumptions.tagSoundness` and `.guardProvenance` are generic
typing-side assumptions. They are not per-implementation facts and do not
belong in `TrustedRegistry`. Typing-side extern reasoning consumes
`extTyping.tagSoundness` and `extTyping.guardProvenance` explicitly, including
for extern declarations in unexecuted branches that still typecheck.

If the extern-boundary design lands, a successful extern execution would
additionally produce a boundary witness supplying `StepFRPost`. That
postcondition includes the tag-meaning, regime-consistency, and agreement
facts needed after the boundary.

## Required Structural Refactors

This approach still requires a few structural changes.

- Extern ids must be recoverable at type-level extern call sites. Today
  `FnTClosure.extern` and `PFnTClosure.extern` do not carry `ExternId`, so the
  proof cannot look up the matching registry evidence during `StepFRApp`.
- The top-level FR theorem must thread `ExternTypingAssumptions`, a trusted
  registry, and the program/registry agreement predicate, and must ensure the
  evaluated configs use the projected runtime registry.
- The registry constraint must land in the actual `FaultRobustnessSpec` shape,
  or in `InputSpec`, not only in the final theorem wrapper. Otherwise the spec
  can still instantiate initial configs with `emptyExternRegistry`, and extern
  cases remain vacuous.
- `valueHasETyp`, `deepValueQTypProperty`, and closure agreement need explicit
  support for extern closures, or the boundary witness must provide equivalent
  typing/agreement evidence for returned extern callables.
- `bevalApp_structure` needs an extern-dispatch branch so the semantics and FR
  proofs can expose successful extern calls as `ExternCallBoundaryRun` events.

These are interface refactors, not per-extern semantic obligations.

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

## Viability Probes

The approach should be validated high-risk-first before doing broad theorem
threading.

### Probe 1: Structural Prerequisites

Before any end-to-end extern proof, make extern closures and call boundaries
first-class proof objects:

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

### Probe 2: Boundary Constructors

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

### Probe 3: End-to-End `abs`

After the structural prerequisites and `pureUnaryCleanInt` constructor exist,
prove a trusted entry for built-in `abs` (`@12`):

- construct the `TrustedExternEntry` for `@12`;
- prove its `ExternBoundarySpec`;
- build a `TrustedRegistry` containing that entry;
- pass the registry and `ExternTypingAssumptions` into the step/FR proof;
- apply the resulting theorem to a small program that calls `abs`.

This is the minimal end-to-end exercise. It checks that trusted-boundary
evidence can actually be packaged, looked up, and consumed by the `StepFR`
extern branch. It does not test nested returned callables, so it is not enough
to validate the whole design.

### Probe 4: Built-In Curried `max`

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

### Probe 5: API Stability

The FR boundary fields are intentionally coupled to `StepFRPost`. That is a
maintenance cost: if the main FR postcondition changes, every direct boundary
witness changes too.

The mitigation is the constructor layer from Probe 2. Concrete drivers prove
compact facts about their implementation and invoke those constructors. If
`StepFRPost` changes, most edits stay inside the constructors rather than every
registered extern proof.

### Probe 6: Single-Run Boundary Facts

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

## Open Questions / TODO

- Revisit the shape of `ExternTypingAssumptions.tagSoundness` and
  `ExternTypingAssumptions.guardProvenance`. The first may be too strong
  because it asks tag allocation to respect an arbitrary `TagMeaning`; if so,
  reformulate it as an assumption that extern tag allocation provides or
  extends a compatible tag meaning. The second likewise needs either a
  derivation from more structural extern-call facts or an explicitly scoped
  trust story parallel to tag soundness.
- Decide where registry agreement belongs in the public FR API:
  `FaultRobustnessSpec` itself or `InputSpec`. The trusted-boundary proof is
  not meaningful until successful runs use `tr.toRuntimeRegistry` instead of
  the default empty registry.
- Decide whether `ExternBoundaryPreservesWF` should remain a field of
  `ExternBoundarySpec` or be exposed only as a derived projection from the
  constructor API. It should not become an independent third proof burden for
  drivers.
- Finalize the exact `ExternCallEntry` / `BodyEntryInputsAgree` payload. It
  must include enough captured-env and argument information for `StepFRApp` to
  plug the extern boundary proof in where the user-closure body IH is used.

The resulting theorem is a clean relative statement: Poison's type system
enforces fault-robustness assuming every registered extern boundary is itself
fault-robustness preserving.
