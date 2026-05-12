# Runtime Extern Safety Refactor

## Problem

Three proof gaps remain in `LeanProofs/SemanticsProperties.lean`:

- `beval_nextAddr_mono`, application through `ExternImpl.fn`;
- `wfConfig_preserved`, application;
- `wfConfig_preserved`, `externVal`.

These are not just missing tactics. After populated registries, the old
unqualified statement

```lean
terminatesTo e cfg0 cfg1 v -> cfg0.nextAddr <= cfg1.nextAddr
```

is false for arbitrary runtime registries. An impure extern implementation
receives the current `nextAddr` and can return any new address cursor. A bad
implementation can move the cursor backwards.

The intended fix is to make this an extern trust obligation. The existing
`ExternBoundarySpec.wf` field already captures operational well-formedness, but
it is too narrow: it proves final `wfConfig` and final `wfValue`, but not
`c_i.nextAddr <= c_o.nextAddr`. The proposed refactor replaces this narrow
field with the wider `ExternBoundarySpec.operational` projection.

There is also an import-cycle issue. `SemanticsProperties.lean` cannot import
the current `ExternBoundary.lean`, because the current dependency chain is:

```text
SemanticsProperties
  -> StepFR
    -> ExternBoundary
```

So the runtime operational part of the extern contract must live below the
FR-shaped boundary contract.

## Analysis

The proof stack has two different extern layers:

- Runtime safety: successful extern events preserve low-level runtime
  invariants such as `wfConfig`, `wfValue`, and `nextAddr` monotonicity.
- Fault-robustness boundary evidence: successful extern events produce
  `StepFRPost`, single-run posts, reachable-registry evidence, and other
  FR-specific facts.

`SemanticsProperties.lean` only needs the first layer. It should not know about
`StepFRPost`, `TrustedRegistryAgreesWithReachable`, or app-side FR transport.

Only `ExternImpl.fn` has a non-trivial monotonicity obligation. `ExternImpl.pfn`
does not change memory or `nextAddr`, and `externVal` declarations leave the
configuration unchanged. A uniform operational postcondition is still useful:

```lean
wfConfig c_o /\ wfValue c_o.nextAddr v /\ c_i.nextAddr <= c_o.nextAddr
```

For `pfn` and `val`, the monotonicity proof is immediate; for `fn`, it is a
real trusted obligation.

## Proposed Approach

Refactor the modules into a low-level runtime layer, an implementation-facing
extern runtime layer, and a high-level FR layer.

File organization should follow two repository conventions:

- Keep definitions and proof-heavy derivations separate when a module starts to
  carry both. Prefer `Foo.lean` for interfaces/definitions and
  `FooProofs.lean` for proof derivations.
- Preserve a mental separation between high-level interfaces and implementation
  plumbing. High-level interfaces are the names a user of the top-level theorem
  should understand; implementation plumbing exists only to prove those
  interfaces and should not leak into public theorem statements.

```text
Semantics
  - terminatesTo / stuck
  - wfValue / wfVarEnv / wfConfig

ExternRuntime
  - ExternDeclaration / ExternDeclarationKind
  - ExternDeclBoundaryRun
  - ExternCallEntry
  - ExternCallBoundaryRun
  - ExternBoundaryWFRun
  - ExternOperationalSafe
  - RegistryOperationalSafe

SemanticsProofs
  - basic wf lookup/update/mono lemmas if they are shared by multiple files

SemanticsProperties
  - beval structure lemmas
  - safe nextAddr monotonicity theorem
  - safe wfConfig preservation theorem

StepFR
  - imports SemanticsProperties

ExternBoundary
  - theorem-facing extern trust interface:
      TrustedRegistry, TrustedExternEntry, ExternBoundarySpec,
      TrustedRegistryAgreesWithReachable
  - exposes `ExternBoundarySpec.operational`

ExternBoundaryProofs
  - proof-heavy declaration/call adapters
  - reachable-domain extraction lemmas
  - trusted registry entries imply the low-level runtime safety predicate
```

The practical reason for the three-layer split is dependency direction:
`ExternRuntime` needs `terminatesTo`, `wfConfig`, and `wfValue`, while
`SemanticsProperties` needs the extern operational predicate. Keeping those
definitions inside `SemanticsProperties.lean` would make the dependency graph
recursive. Moving them to `Semantics.lean` gives a clean acyclic graph:

```text
Semantics -> ExternRuntime -> SemanticsProperties -> StepFR
StepFR -> ExternBoundary
ExternBoundary -> ExternBoundaryProofs
Semantics -> SemanticsProofs
```

`ExternRuntime` is not intended to be a user-facing trust interface. It is
an implementation-facing runtime event layer needed by low-level semantics
proofs. The user-facing trust interface remains `ExternBoundarySpec`, carried
inside `TrustedRegistry` and consumed by the top-level FR theorem.

The top-level theorem reader should be able to start from
`TypeSystemEnforcesFaultRobustness` and understand the statement by following a
small public surface:

- `FaultRobustnessSpec`;
- `TrustedRegistry`;
- `TrustedExternEntry`;
- `ExternBoundarySpec`;
- `TrustedRegistryAgreesWithReachable`;
- `ctxMatchesInputSpec`;
- `ExternTypingAssumptions` while that staging input remains part of
  `FaultRobustnessSpec`.

Definitions and lemmas not needed to understand those names should be treated as
implementation details and moved to proof/helper modules where possible.

The low-level operational predicate should be independent of `StepFRPost`. Name
it for the broader obligation, not just well-formedness:

```lean
def ExternOperationalSafe
    (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  forall (c_i c_o : Config) (v : Value),
    ExternBoundaryWFRun d impl c_i c_o v ->
    wfConfig c_i ->
    wfConfig c_o /\
    wfValue c_o.nextAddr v /\
    c_i.nextAddr <= c_o.nextAddr
```

Then `ExternBoundarySpec` should expose one operational projection:

```lean
operational : ExternOperationalSafe d impl
```

Do not keep a separate `ExternBoundaryPreservesWF` field. If a temporary
projection lemma is useful during migration, keep it private and delete it once
call sites consume `ExternOperationalSafe`. A public narrow name risks masking
future consumers that also need the full allocation-cursor discipline.

```lean
private theorem ExternOperationalSafe.preservesWF
    {d : ExternDeclaration} {impl : ExternImpl}
    (hsafe : ExternOperationalSafe d impl) :
  forall c_i c_o v,
    ExternBoundaryWFRun d impl c_i c_o v ->
    wfConfig c_i ->
    wfConfig c_o /\ wfValue c_o.nextAddr v
```

`SemanticsProperties.lean` cannot usually consume `ExternOperationalSafe d impl`
directly, because `beval` sees only a runtime registry lookup
`reg.get? id = some impl`; it does not have trusted declaration evidence `d`.
Therefore the semantics-facing predicate should be registry-level:

```lean
def RegistryOperationalSafe (reg : ExternRegistry) : Prop := ...
```

`RegistryOperationalSafe` states the raw preservation facts needed by
successful `externVal`, `ExternImpl.pfn`, and `ExternImpl.fn` runtime events.
See Step 3 for the per-kind obligations.

The bridge from trusted entries to runtime safety belongs above the semantics
layer:

```lean
TrustedRegistry.operationalSafe :
  RegistryOperationalSafe (TrustedRegistry.toRuntimeRegistry tr)
```

That bridge can use each entry's `spec.operational` plus lookup/declaration
reconstruction. The public theorem should still mention only the trusted
registry and reachable-trust assumptions, not `RegistryOperationalSafe`.

## Plan

### Step 1: Extract Semantics Definitions

Create `LeanProofs/Semantics.lean` and move only the low-level semantic
definitions out of `SemanticsProperties.lean`:

- `terminatesTo`;
- `stuck`;
- `wfValue`;
- `wfVarEnv`;
- `wfConfig`;
- `nextAddr_not_in_memory` if it is best treated as part of the definitions
  API.

Put shared proof lemmas in `LeanProofs/SemanticsProofs.lean` if they are
used by multiple files. Keep proof lemmas local/private in their consumer file
when they are only needed by one proof.

`SemanticsProperties.lean` should import this file and continue exporting the
same public names through imports. This step should be behavior-neutral and
should not touch the proof bodies except for imports and removed duplicate
definitions.

Done when:

- `make lean-build-file FILE=LeanProofs/SemanticsProperties.lean` passes;
- no sorry/axiom delta is introduced.

### Step 2: Split Extern Runtime Definitions

Create `LeanProofs/ExternRuntime.lean` for implementation-facing runtime
boundary data that does not depend on `StepFR`:

- declaration shapes;
- declaration and call boundary run predicates;
- `ExternCallEntry`;
- `ExternBoundaryWFRun`;
- `ExternOperationalSafe`;
- `RegistryOperationalSafe`.

Move only definitions that do not mention `StepFRPost`,
`ExternBoundarySinglePost`, or reachable-registry FR transport. Lemmas that
depend on `terminatesTo` can stay above this layer until there is a clear need
to move them.

This file should not become the conceptual FFI API. It exists so
`SemanticsProperties.lean` can talk about raw runtime extern safety without
importing the high-level FR boundary module.

Done when:

- `ExternBoundary.lean` imports and reuses `ExternRuntime.lean`;
- `make lean-build-file FILE=LeanProofs/ExternBoundary.lean` passes.

### Step 3: Add Registry-Level Runtime Safety

Define `RegistryOperationalSafe`, the predicate consumed by
`SemanticsProperties`. It should be stated over raw successful runtime events,
because `beval` has registry lookup facts and implementation-success facts but
not trusted declaration evidence.

The important obligations are:

- `externVal`: returned value is well-formed at the unchanged config;
- `ExternImpl.pfn`: returned value is well-formed and config/`nextAddr` are
  unchanged;
- `ExternImpl.fn`: returned config/value are well-formed and returned
  `nextAddr` is at least the input `nextAddr`.

Done when the predicate is expressive enough to prove the current
`SemanticsProperties.lean` extern branches without importing high-level
`ExternBoundary.lean`.

### Step 4: Prove Safe Semantics Lemmas

Before changing signatures, audit all consumers of `terminatesTo_nextAddr_mono`
and `wfConfig_preserved`. Draft the new safe signatures once and confirm the
safety hypothesis can be supplied uniformly from the orchestration layer. If any
consumer cannot obtain the hypothesis, stop and update this plan before landing
code.

Replace or add safe variants of the semantics lemmas:

```lean
beval_nextAddr_mono_safe
terminatesTo_nextAddr_mono_safe
wfConfig_preserved_safe
```

Directly migrate current callers to the safe lemmas. In the Probe-2-complete FR
path, proofs already run under a trusted registry, so the orchestration can
supply `RegistryOperationalSafe (TrustedRegistry.toRuntimeRegistry tr)` from the
trusted-entry bridge. Keep empty-registry aliases only for isolated legacy
callers if `rg` finds a real use outside the trusted-registry-aware proof path.

High-risk point: `terminatesTo_nextAddr_mono` has many downstream callers,
especially in `StepFRApp.lean`. Prefer a migration pattern that keeps the call
sites readable, but do not hide a false premise. This may ripple into
signatures of `StepFR`, single-run helpers, per-operator `stepFR_*` lemmas, and
`wfConfig_preserved` consumers. The safety hypothesis should be threaded as a
uniform parameter alongside the existing registry/trusted-registry parameters,
not reinvented per operator.

Done when the three existing `SemanticsProperties.lean` sorries are removed.

### Step 5: Bridge Trusted Registries to Runtime Safety

In `ExternBoundary.lean`, prove that trusted entries imply the low-level
registry safety predicate for `TrustedRegistry.toRuntimeRegistry`.

This should use the strengthened `operational` field of `ExternBoundarySpec`.
The top-level FR theorem should not gain a new public trust premise beyond the
trusted registry construction; operational safety is part of building a trusted
entry.

Move proof-heavy derivations to `LeanProofs/ExternBoundaryProofs.lean` if they
are not needed by theorem users directly. Keep `ExternBoundary.lean` focused on
the high-level definitions and theorem-facing interface.

Done when:

- the FR proof uses the safe semantics lemmas under
  `TrustedRegistry.toRuntimeRegistry`;
- `lake build LeanProofs` passes.

### Step 6: Trim Theorem-Facing Interfaces

Audit the current theorem-facing modules and move implementation details out of
high-level files where it can be done without destabilizing the proof:

- keep `FaultRobustness.lean` focused on `FaultRobustnessSpec` and the
  predicates a user needs to understand it;
- keep `ExternBoundary.lean` focused on `TrustedRegistry`,
  `TrustedExternEntry`, `ExternBoundarySpec`, and trust/reachability predicates
  that appear in the top-level theorem;
- move proof-heavy trusted-registry adapters, app-call boundary construction
  lemmas, and reachability extraction lemmas to `ExternBoundaryProofs.lean` or a
  reachability-specific proofs file if needed.

Done when the final theorem surface is small and documented, and helper modules
do not leak implementation predicates into the public theorem statement.

This cleanup is independent of the sorry-elimination path in Steps 1-5. It
should not block the operational-safety refactor if the proof migration is ready
first.

### Step 7: Update FFI Roadmap

After the refactor compiles, update `doc/ffi-axioms.md`:

- correct the remaining sorry count from two to three if still relevant;
- describe operational safety as `ExternBoundarySpec.operational`;
- make Probe 3 constructor work depend on the runtime safety refactor;
- update Probe 3 constructor targets from the obsolete `.wf` field to the new
  `.operational` field.

## Acceptance Criteria

- No new `sorry` or `axiom`.
- The three existing `SemanticsProperties.lean` sorries are removed.
- `SemanticsProperties.lean` does not import the high-level
  `ExternBoundary.lean`.
- `ExternBoundarySpec` has one strengthened `operational` projection, not
  independent `wf` and `nextAddr` proof burdens.
- High-level theorem users only need to understand `TrustedRegistry`,
  `TrustedExternEntry`, `ExternBoundarySpec`, `TrustedRegistryAgreesWithReachable`,
  `ctxMatchesInputSpec`, `ExternTypingAssumptions`, and `FaultRobustnessSpec`;
  runtime helper predicates remain implementation details.
- The public FR theorem remains registry/trusted-entry relative; no separate
  public operational-safety premise is exposed.
- `lake build LeanProofs` passes.
- `git diff --check` is clean.

## History

Probe 2 made the FR proof registry-aware and taught extern declaration and app
call branches to consume `ExternBoundarySpec` evidence from a populated trusted
registry. That solved the fault-robustness boundary consumption problem.

The remaining `SemanticsProperties.lean` gaps are lower-level operational
preservation obligations. They were masked by the old empty-registry setting:
successful extern dispatch was impossible, so monotonicity and well-formedness
never had to reason about host-provided memory/address updates.

The key design decision for this refactor is to keep low-level runtime safety
below `StepFR`, while keeping FR-shaped boundary evidence above `StepFR`.
