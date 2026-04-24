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

That bundle is the right contract for externs. The alternative approach is to
factor this bundle into a named predicate, then require registered externs to
produce it at extern boundaries.

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
just `StepFRPost ...`.

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

## Operational Well-Formedness

`StepFRPost` includes `wfConfig` for two final configurations, but
`LeanProofs/SemanticsProperties.lean` also has single-run preservation lemmas
such as `wfConfig_preserved`. Those lemmas are not themselves relational.

For that reason the high-level interface should include a single-run
well-formedness consequence alongside `ExternBoundaryFR`.

```lean
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
  wf : ExternBoundaryPreservesWF d impl
```

This is still a high-level contract. It does not say how the extern preserves
well-formedness; it only states the property the existing semantics lemmas need.
The two fields should be proved from shared driver lemmas where possible, so a
driver does not manually duplicate the `wfConfig` argument once for the
relational FR witness and once for the single-run preservation witness.

## Registry Evidence

The theorem should receive a trusted registry as an explicit hypothesis.
This avoids adding global Lean axioms.

```lean
abbrev DeclEnv := Std.HashMap ExternId ExternDeclaration

structure TrustedRegistry (e : Expr) where
  declEnv : DeclEnv
  reg     : ExternRegistry

  /-- The declaration environment faithfully describes extern declarations in
      the source expression being proved. -/
  programDeclsMatch : ProgramDeclsMatch e declEnv

  /-- Every successful registered extern boundary satisfies the trusted
      boundary contract. -/
  externSpec :
    ∀ {id d impl},
      declEnv.get? id = some d →
      reg.get? id = some impl →
      ExternBoundarySpec d impl
```

The top-level theorem then becomes relative to `TrustedRegistry e`:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (e : Expr) (tr : TrustedRegistry e)
    (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec e s obs := ...
```

In the current runtime, `Config.registry` is the actual implementation map.
The FR theorem must also connect the initial runtime configs to `tr.reg`, for
example by requiring the initial configs' `registry` fields to equal `tr.reg`.

Call sites that need the relational contract use `(tr.externSpec hd hi).fr`.
Single-run preservation lemmas use `(tr.externSpec hd hi).wf`.

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
use `(tr.externSpec hd hi).wf` on the `ExternBoundaryRun.callFn` branch.

No separate frame, domain, or address monotonicity lemma is needed in the main
proof. Those facts may be how a concrete driver justifies the `wf` field, but
the core proof only consumes the high-level result.

### `wfConfig_preserved`, `externVal ref int`

The `externVal` case needs `wfValue nextAddr (Value.loc a)` when the registered
extern value is a reference. The proof can use `(tr.externSpec hd hi).wf` on
the `ExternBoundaryRun.declVal` branch.

This hides the details of address bounds, runtime memory presence, and reference
initialization behind the trusted boundary. If a driver registers a bad
reference, it cannot supply the `wf` field.

### Former `terminatesTo_extern_absurd` sites

The current FR proof closes extern declaration cases vacuously under an empty
registry. Once a populated registry is threaded into the theorem, successful
extern declaration evaluations are no longer contradictory.

In those cases, the proof invokes `(tr.externSpec hd hi).fr` on the declaration
boundary:

- `ExternBoundaryRun.declVal` for `externVal`,
- `ExternBoundaryRun.declFn` for `externFn`,
- `ExternBoundaryRun.declPfn` for `externPfn`.

The witness directly provides `StepFRPost`, including result typing,
tag-meaning obligations, regime consistency, runtime instantiation, and clean
result agreement.

### Extern fn/pfn dispatch in `StepFRApp`

When application evaluates a closure whose body is `Expr.externFn` or
`Expr.externPfn`, the proof invokes `(tr.externSpec hd hi).fr` on:

- `ExternBoundaryRun.callFn`, or
- `ExternBoundaryRun.callPfn`.

The witness supplies the postconditions that the ordinary user-closure proof
would otherwise derive structurally from the function body.

## Relationship to `LeanProofs/ExternAxioms.lean`

`LeanProofs/ExternAxioms.lean` currently contains two global axioms:

- `externTagSoundness`
- `externGuardProvenance`

In this proposal, that file becomes the home for the extern-boundary interface.
The global axioms should be retired rather than extended.

The replacement contents would be:

- `ExternDeclaration`
- `DeclEnv`
- `ProgramDeclsMatch`
- `ExternBoundaryRun`
- `StepFRPost` or an import of it from `StepFR.lean`
- `ExternBoundaryFR`
- `ExternBoundaryPreservesWF`
- `ExternBoundarySpec`
- `TrustedRegistry`
- helper lemmas for looking up declaration and implementation evidence

The current `externTagSoundness` obligation is absorbed by `StepFRPost`:
`StepFRPost` already requires `QTypRespectsTagMeaning tm res.qualType` and
`wfTagMeaningCtx tm (ctxAfter ctx res)`. An extern boundary witness must supply
those facts directly.

The current `externGuardProvenance` obligation is absorbed by the post-state
regime and agreement facts in `StepFRPost`: `consistentWithRegime` and
`agreeOnClean` for the post context are exactly what downstream FR reasoning
needs. If an intermediate helper still wants a pointwise guard-provenance lemma,
it should either be derived from the boundary witness or the helper should be
rewritten to consume `StepFRPost` directly.

During migration, it may be practical to keep compatibility theorem names such
as `externTagSoundness_of_boundary` or `externGuardProvenance_of_boundary` for
local call sites. They should be theorems from trusted-registry evidence, not
global `axiom` declarations.

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

### Probe 1: Built-In Pure Externs

First prove `ExternBoundarySpec` for a small slice of the default registry.
The best target is the built-in curried `max` externs:

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

- `@12`, pure `abs`, which tests a simple clean numeric result;
- `@20`, an extern integer value;
- `@21`, a reference-valued extern value backed by the driver-initialized
  `errno` cell;
- `@22`, an impure extern function that updates the `errno` cell without
  allocating.

### Probe 2: Nested Returned Callables

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

### Probe 3: API Stability

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

### Probe 4: Single-Run WF

`ExternBoundaryPreservesWF` duplicates part of the two-run postcondition, but
it serves a different consumer: single-run semantic preservation. It should
remain a separate projection in `ExternBoundarySpec`.

The proof effort should not be duplicated manually. The intended driver pattern
is to prove lower-level implementation facts once, then derive both
`ExternBoundaryFR` and `ExternBoundaryPreservesWF` from those shared facts.

## Migration Sketch

1. Make `ExternBoundaryRun` precise enough for declaration and call inversion,
   then strengthen `bevalApp_structure` with extern boundary cases.
2. Extend runtime/typechecking closure representations and closure-agreement
   predicates so extern ids and nested returned callables are first-class proof
   objects.
3. Factor the conclusion of `StepFR` into `StepFRPost`.
4. Add `ExternDeclaration`, `ExternBoundaryFR`,
   `ExternBoundaryPreservesWF`, `ExternBoundarySpec`, and `TrustedRegistry`.
5. Prove `ExternBoundarySpec` for the built-in externs, starting with
   `@10` / `@11` curried `max`. Treat failure here as a design blocker.
6. Thread `(tr : TrustedRegistry e)` through the step theorem and top-level FR
   theorem.
7. Replace extern declaration cases in `FaultRobustnessProofs.lean` with
   calls to `(tr.externSpec hd hi).fr`.
8. Replace extern dispatch cases in `StepFRApp.lean` with calls to
   `(tr.externSpec hd hi).fr`.
9. Replace extern `wfConfig_preserved` cases in
   `SemanticsProperties.lean` with calls to `(tr.externSpec hd hi).wf`.
10. Remove global axioms from `LeanProofs/ExternAxioms.lean`.

The resulting theorem is a clean relative statement: Poison's type system
enforces fault-robustness assuming every registered extern boundary is itself
fault-robustness preserving.
