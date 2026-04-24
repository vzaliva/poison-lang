# FFI Axioms Alternative: Externs as FR-Preserving Boundary Steps

Status: design proposal.

This document proposes a high-level proof interface for trusted externs.  The
proof assumes one FR-shaped property at every successful extern boundary,
rather than exposing frame, address, initialization, and non-leakage details to
the core language theorem.

The intended theorem is relative:

> The Poison type system enforces fault-robustness for programs whose
> registered externs satisfy the extern-boundary FR contract.

This keeps the core language proof focused on Poison semantics and typechecking,
while making the FFI trust boundary explicit.

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
proof layer. The alternative approach is to factor this bundle into a named
predicate, then require registered externs to produce it at extern boundaries.

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
just `StepFRPost ...`. `ExternBoundaryFR` also concludes `StepFRPost ...`;
that is why applying an extern-boundary witness gives the extern case exactly
the facts the ordinary `StepFR` proof would need.

`ExternBoundaryFR` should be understood as the same run-to-post pattern as
`StepFR`, but with a different run relation. `StepFR` starts from two
successful `terminatesTo e` runs. `ExternBoundaryFR` starts from two successful
`ExternBoundaryRun` events. The conclusion is the same `StepFRPost`.

For extern declarations, this is essentially `StepFR` specialized to
`Expr.externVal`, `Expr.externFn`, or `Expr.externPfn`, with the proof supplied
by trusted registry evidence. For extern dispatch, it is not just `StepFR`
restricted to a syntactic subset of `Expr`: the boundary is a semantic sub-event
inside application evaluation after the function and argument have already
evaluated.

## Extern Boundary Events

Externs appear at two proof boundaries.

The first boundary is expression evaluation of extern declarations:

- `externVal`
- `externFn`
- `externPfn`

The second boundary is runtime dispatch through an extern closure during
application:

- impure `ExternImpl.fn`
- pure `ExternImpl.pfn`

The proof interface should name these boundaries explicitly.

```lean
inductive ExternBoundaryKind where
  | declVal
  | declFn
  | declPfn
  | callFn
  | callPfn

/-- Static declaration shape extracted from the source program. -/
structure ExternDeclaration where
  id      : ExternId
  kind    : ExternBoundaryKind
  typ     : Typ
  argName : Option Name
  retSpec : Option ExternReturn
  effects : List Effect
  preds   : List SyntaxPredicate

/-- Runtime/typechecking evidence that a particular successful step is an
    extern boundary step for declaration `d` and implementation `impl`.

    Each constructor should carry the discriminating facts that downstream
    proofs need. The payload structures are placeholders for those facts; they
    should not be empty tags. -/
inductive ExternBoundaryRun
    (d : ExternDeclaration) (impl : ExternImpl)
    (ctx : TypeContext) (res : TypeResult)
    (cᵢ cₒ : Config) (v : Value) : Prop where
  | declVal :
      ExternDeclValFacts d impl ctx res cᵢ cₒ v →
      ExternBoundaryRun d impl ctx res cᵢ cₒ v
  | declFn :
      ExternDeclFnFacts d impl ctx res cᵢ cₒ v →
      ExternBoundaryRun d impl ctx res cᵢ cₒ v
  | declPfn :
      ExternDeclPfnFacts d impl ctx res cᵢ cₒ v →
      ExternBoundaryRun d impl ctx res cᵢ cₒ v
  | callFn :
      ExternCallFnFacts d impl ctx res cᵢ cₒ v →
      ExternBoundaryRun d impl ctx res cᵢ cₒ v
  | callPfn :
      ExternCallPfnFacts d impl ctx res cᵢ cₒ v →
      ExternBoundaryRun d impl ctx res cᵢ cₒ v
```

The fact payloads should include at least:

- the declaration id and kind, matching `d`;
- the source/typechecking equation for the declaration or closure application;
- the registry lookup equation `cᵢ.registry.get? id = some impl`;
- the implementation shape equation, such as `impl = ExternImpl.pfn f`;
- the runtime success equation for the implementation call;
- the `validateExternReturn` success equation for call boundaries;
- the exact output configuration equation;
- the captured environment, argument value, and updated call environment for
  `callFn` / `callPfn`;
- the relevant `pureMode` condition for impure calls.

This is the main place where the proposal must be precise. If these payloads
are too weak, the `StepFRApp` and `wfConfig_preserved` extern branches will
still need ad-hoc inversion lemmas.

## The High-Level Contract

The central interface is one property: paired successful extern boundary runs
from clean-agreeing inputs produce the normal `StepFRPost`.

```lean
def ExternBoundaryFR
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
        ExternBoundaryRun d impl ctx res
          { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
          cf₀ o₀ →
        ExternBoundaryRun d impl ctx res
          { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
          cf₁ o₁ →
        StepFRPost ctx res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁
```

This is deliberately strong. It says a trusted extern is already a valid
FR-preserving step at the same abstraction level as the rest of the proof.
Any low-level facts about effects, address allocation, memory domain, or
return-value non-leakage are internal ways to justify this contract; they are
not required by the core Poison theorem.

## Single-Run Boundary Contract

The proof stack also has one-run facts. In `LeanProofs/StepFR.lean`,
`StepFRSingleRunFinalCleanPcTrue` and
`StepFRSingleRunFinalCleanPcTrueMaskedRegParam` have the same shape as
`StepFR`, but with one successful run instead of two. They produce the
single-run preservation facts needed when the final pc is clean.

Externs should get the same treatment. The boundary interface should include a
single-run contract whose conclusion mirrors the existing `StepFRSingle...`
postcondition, but whose run premise is `ExternBoundaryRun` rather than
`terminatesTo e`.

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

def ExternBoundarySingle
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
        ExternBoundaryRun d impl ctx res
          { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
          cf o →
        ctx.pc = true →
        ExternBoundarySinglePost ctx res predSat θ μ cf o

def ExternBoundaryPreservesWF
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  ∀ (ctx : TypeContext) (res : TypeResult)
    (cᵢ cₒ : Config) (v : Value),
    ExternBoundaryRun d impl ctx res cᵢ cₒ v →
    wfConfig cᵢ →
    wfConfig cₒ ∧ wfValue cₒ.nextAddr v

structure ExternBoundarySpec
    (d : ExternDeclaration) (impl : ExternImpl) : Prop where
  fr : ExternBoundaryFR d impl
  single : ExternBoundarySingle d impl
  wf : ExternBoundaryPreservesWF d impl
```

`ExternBoundarySingle` is the extern analogue of the `StepFRSingle...` lemmas.
`ExternBoundaryPreservesWF` remains as a smaller projection for consumers such
as `wfConfig_preserved`, which only need operational well-formedness. All three
fields should be derived from shared driver lemmas where possible, so a driver
does not manually prove the same preservation facts three times.

## Extern Assumptions and Registry Evidence

The theorem should receive extern assumptions explicitly. This avoids hard-coded
global Lean axioms and avoids requiring implementation proofs for externs that
are declared but never registered.

There are two trust inputs:

- `ExternTypingAssumptions`: generic assumptions about extern typechecking
  machinery, replacing the current global axioms in
  `LeanProofs/ExternAxioms.lean`;
- `TrustedRegistry`: per-implementation evidence only for extern ids that are
  present in the runtime registry. Each trusted entry stores the implementation,
  the declaration shape it implements, and the boundary proof for that pair.

This distinction matters for conditionals. Both branches of an `if` typecheck,
so extern declarations in an unexecuted branch may still need the generic
typing assumptions. But if that branch is not executed, there is no successful
`ExternBoundaryRun`, so no implementation-level boundary proof is consumed.

```lean
/-- Explicit replacement for the current global axioms in
    `LeanProofs/ExternAxioms.lean`. These assumptions are generic facts about
    extern typechecking, not per-runtime-implementation safety facts. -/
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

/-- The trusted entry under an id agrees with the declaration shape found in
    the program at that id. -/
def TrustedRegistryMatchesProgram (e : Expr) (tr : TrustedRegistry) : Prop :=
  ProgramDeclsMatch e (tr.mapValues (fun entry => entry.decl))
```

The top-level theorem then becomes relative to both inputs:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (e : Expr)
    (tr : TrustedRegistry)
    (hDecls : TrustedRegistryMatchesProgram e tr)
    (extTyping : ExternTypingAssumptions)
    (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := ...
```

In the current runtime, `Config.registry` is the actual implementation map.
The FR theorem must connect the initial runtime configs to the implementation
projection of the trusted registry, for example by requiring the initial
configs' `registry` fields to equal `tr.toRuntimeRegistry`.

Typing-side extern reasoning uses `extTyping`. Structural induction decomposes
`hDecls` for subexpressions while reusing the same trusted registry. Call sites
that need the relational boundary contract look up the trusted entry by id; if
`tr.get? id = some entry`, then `entry.spec.fr` is the relational boundary
contract, `entry.spec.single` is the single-run clean-pc contract, and
`entry.spec.wf` is the operational well-formedness contract.

There is intentionally no obligation of the form "every extern declaration has
an implementation." If a trusted entry is absent, the projected runtime registry
has no implementation for that id; dispatch is a runtime error, not a
successful boundary event.

## How This Addresses Existing Sorries

### `bevalApp_structure`

`LeanProofs/SemanticsProperties.lean` currently has a `bevalApp_structure`
sorry because the old inversion lemma assumed only user-closure dispatch. The
extern runtime adds extra successful branches for extern closure bodies.

Under this approach, the inversion lemma should be strengthened to return one
of three cases:

- user closure body evaluation,
- pure user closure body evaluation,
- extern boundary dispatch described by `ExternBoundaryRun`.

The high-level extern contract does not replace this operational inversion.
It makes the extern branch easy to consume once the branch has been exposed.

### `wfConfig_preserved`, application extern dispatch

The `app` case of `wfConfig_preserved` needs to show that a successful
`ExternImpl.fn` dispatch returns a well-formed config and value. The proof can
look up the trusted entry by id and use `entry.spec.wf` on the
`ExternBoundaryRun.callFn` branch.

No separate frame, domain, or address monotonicity lemma is needed in the main
proof. Those facts may be how a concrete driver justifies the `wf` field, but
the core proof only consumes the high-level result.

### `wfConfig_preserved`, `externVal ref int`

The `externVal` case needs `wfValue nextAddr (Value.loc a)` when the registered
extern value is a reference. The proof can look up the trusted entry by id and
use `entry.spec.wf` on the `ExternBoundaryRun.declVal` branch.

This hides the details of address bounds, runtime memory presence, and reference
initialization behind the trusted boundary. If a driver registers a bad
reference, it cannot supply the `wf` field.

### Former `terminatesTo_extern_absurd` sites

The current FR proof closes extern declaration cases vacuously under an empty
registry. Once a populated registry is threaded into the theorem, successful
extern declaration evaluations are no longer contradictory.

In those cases, the proof looks up the trusted entry by id and invokes
`entry.spec.fr` on the declaration boundary:

- `ExternBoundaryRun.declVal` for `externVal`,
- `ExternBoundaryRun.declFn` for `externFn`,
- `ExternBoundaryRun.declPfn` for `externPfn`.

The witness directly provides `StepFRPost`, including result typing,
tag-meaning obligations, regime consistency, runtime instantiation, and clean
result agreement.

### Extern fn/pfn dispatch in `StepFRApp`

When application evaluates a closure whose body is `Expr.externFn` or
`Expr.externPfn`, the proof invokes `entry.spec.fr` on:

- `ExternBoundaryRun.callFn`, or
- `ExternBoundaryRun.callPfn`.

The witness supplies the postconditions that the ordinary user-closure proof
would otherwise derive structurally from the function body.

## Relationship to `LeanProofs/ExternAxioms.lean`

`LeanProofs/ExternAxioms.lean` currently contains two global axioms:

- `externTagSoundness`
- `externGuardProvenance`

In this proposal, that file becomes the home for explicit extern assumptions
and the extern-boundary interface. The global axioms should be retired rather
than extended: their current logical content becomes fields of
`ExternTypingAssumptions`, passed explicitly through the proof stack.

The replacement contents would be:

- `ExternTypingAssumptions`
- `ExternDeclaration`
- `TrustedExternEntry`
- `TrustedRegistry`
- `TrustedRegistry.toRuntimeRegistry`
- `TrustedRegistryMatchesProgram`
- `ExternBoundaryRun`
- `StepFRPost` or an import of it from `StepFR.lean`
- `ExternBoundaryFR`
- `ExternBoundarySinglePost`
- `ExternBoundarySingle`
- `ExternBoundaryPreservesWF`
- `ExternBoundarySpec`
- helper lemmas for looking up declaration and implementation evidence

The current `externTagSoundness` and `externGuardProvenance` obligations are
generic typing-side assumptions. They are not per-implementation facts and
should not live in `TrustedRegistry`. Typing-side extern reasoning consumes
`extTyping.tagSoundness` and `extTyping.guardProvenance` explicitly, including
for extern declarations in unexecuted branches that still typecheck.

When an extern actually executes successfully, the boundary witness supplies
`StepFRPost`. That postcondition includes the tag-meaning, regime-consistency,
and agreement facts needed after the boundary. If a local proof site still wants
the old theorem names, keep compatibility lemmas such as
`externTagSoundness_of_assumptions` or `externGuardProvenance_of_assumptions`;
they should read from `ExternTypingAssumptions`, not from global `axiom`
declarations.

## Required Structural Refactors

This approach still requires a few structural changes.

- Extern ids must be recoverable at type-level extern call sites. Today
  `FnTClosure.extern` and `PFnTClosure.extern` do not carry `ExternId`, so the
  proof cannot look up the matching registry evidence during `StepFRApp`.
- The top-level FR theorem must thread a trusted registry and must ensure the
  evaluated configs use that registry.
- `valueHasETyp`, `deepValueQTypProperty`, and closure agreement need explicit
  support for extern closures, or the boundary witness must provide equivalent
  typing/agreement evidence for returned extern callables.
- `bevalApp_structure` needs an extern-dispatch branch so the semantics and FR
  proofs can expose successful extern calls as `ExternBoundaryRun` events.

These are interface refactors, not per-extern semantic obligations.

## Trust Boundary

The trusted boundary is intentionally large:

- it trusts registered extern implementations to preserve runtime
  well-formedness;
- it trusts them not to leak poisoned information into clean observations;
- it trusts extern declarations and returned extern callables to match their
  typechecking summaries;
- it trusts any tag-meaning and regime facts needed by the postcondition.

This is appropriate when externs model host functions, separately verified
components, or abstract primitives. If a specific extern should be verified
inside Lean, one can later prove `ExternBoundaryFR d impl` from more detailed
lemmas. The core FR theorem does not need to know those details.

## Viability Probes

The approach should be validated high-risk-first before doing broad theorem
threading.

### Probe 1: End-to-End `abs`

First prove a trusted entry for a simple existing extern, preferably built-in
`abs` (`@12`):

- construct the `TrustedExternEntry` for `@12`;
- prove its `ExternBoundarySpec`;
- build a `TrustedRegistry` containing that entry;
- pass the registry and `ExternTypingAssumptions` into the step/FR proof;
- apply the resulting theorem to a small program that calls `abs`.

This is the minimal end-to-end exercise. It checks that trusted-boundary
evidence can actually be packaged, looked up, and consumed by the `StepFR`
extern branch. It does not test nested returned callables, so it is not enough
to validate the whole design.

### Probe 2: Built-In Curried `max`

Next prove `ExternBoundarySpec` for the built-in curried `max` externs:

- `@11`, the inner pure extern, receives captured `a` and argument `b`, returns
  `Value.num (max a b)`, and leaves memory/config unchanged.
- `@10`, the outer pure extern, receives `a` and returns a `Value.peClosure`
  whose body is `Expr.externPfn 11 ...` and whose captured runtime environment
  contains `a`.

This pair is a useful stress test. The `@11` proof checks that a clean numeric
result can be justified from the clean-agreement facts available at an extern
call boundary. If the call-boundary payload does not expose enough information
to derive equality of the two `max` results, `ExternBoundaryRun` is underspecified.

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

### Probe 3: Nested Returned Callables

Nested returned callables should be treated as a required structural feature,
not as an optional driver-side escape hatch.

Runtime validation already checks that a nested return has the expected extern
AST shape. The proof also needs the type-level and relational predicates to
understand extern closures. Concretely, the implementation should extend:

- `FnTClosure.extern` and `PFnTClosure.extern` with the corresponding
  `ExternId`;
- `valueHasETyp` so runtime extern closures can inhabit arrow/parrow enriched
  types;
- `valueConsistentWithRegime` and `resultAgreesIfClean` so two returned extern
  closures agree when their ids, declarations, and captured clean environments
  agree;
- closure-agreement helpers used by `StepFRApp` so a later call can recover the
  registry evidence for the extern id.

Without these changes, `StepFRPost` can assert closure facts but the rest of
the proof cannot consume them reliably.

### Probe 4: API Stability

`ExternBoundaryFR` is intentionally coupled to `StepFRPost`. That is a
maintenance cost: if the main FR postcondition changes, every direct boundary
witness changes too.

The mitigation is to avoid writing drivers directly against the raw conjunction.
`LeanProofs/ExternAxioms.lean` should provide reusable constructors such as:

- `ExternBoundarySpec.constCleanInt`;
- `ExternBoundarySpec.pureUnaryCleanInt`;
- `ExternBoundarySpec.nestedPfn`;
- `ExternBoundarySpec.refValInitialized`;
- `ExternBoundarySpec.impureCellUpdate`.

Concrete drivers then prove compact facts about their implementation and invoke
these constructors. If `StepFRPost` changes, most edits stay inside the
constructors rather than every registered extern proof.

### Probe 5: Single-Run Boundary Facts

`ExternBoundarySingle` overlaps with the two-run postcondition, but it serves a
different consumer: the existing `StepFRSingle...` lemmas. It should remain a
separate projection in `ExternBoundarySpec`.

`ExternBoundaryPreservesWF` is even smaller. It is for operational preservation
lemmas such as `wfConfig_preserved`, where the proof only needs final
well-formedness and does not need the full single-run clean-pc postcondition.

The proof effort should not be duplicated manually. The intended driver pattern
is to prove lower-level implementation facts once, then derive
`ExternBoundaryFR`, `ExternBoundarySingle`, and `ExternBoundaryPreservesWF` from
those shared facts.

## Open Questions / TODO

- Revisit the shape of `externTagSoundness`. Moving it into
  `ExternTypingAssumptions` removes the global axiom, but the current statement
  may still be too strong: it asks tag allocation to respect an arbitrary
  `TagMeaning`. If this is unprovable, reformulate it as an assumption that
  extern tag allocation provides or extends a compatible tag meaning.

The resulting theorem is a clean relative statement: Poison's type system
enforces fault-robustness assuming every registered extern boundary is itself
fault-robustness preserving.
