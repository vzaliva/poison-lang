# Probe 2 Plan: Registry-Aware Extern Boundaries

## Objective

Complete the proof-side bridge from the current empty-registry fault-robustness
theorem to a registry-aware extern-boundary theorem.

This is the Probe 2 sub-task of `doc/ffi-axioms.md`. It is about consuming
trusted boundary evidence in the proof stack. Reusable concrete driver
constructors such as `ExternBoundarySpec.pureUnaryCleanInt` are intentionally
left to the next high-level probe.

The target shape is a relative theorem:

```lean
TypeSystemEnforcesFaultRobustness_spec_with_registry
  (TrustedRegistry.toRuntimeRegistry tr) e s obs
```

under explicit trusted-registry agreement hypotheses. Successful extern
declarations and extern calls should be justified by `ExternBoundarySpec`
evidence instead of by the current empty-registry vacuity arguments.

No new `sorry` or `axiom` is acceptable.

## Current Status

Implemented and compiling:

- `StepFRPost` is shared in `LeanProofs/StepFR.lean`, and `StepFR` concludes it.
- `StepFR`, `StepFR_IH`, `StepFRSingleRunFinalCleanPcTrue`,
  `StepFRSingleRunFinalCleanPcTrue_IH`,
  `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`, and
  `StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH` are registry-parametric.
  Their initial config literals carry `registry := registry`.
- Non-app per-operator proof modules have been threaded through the
  registry-parametric IHs and compile.  Recursive calls use registry-preservation
  facts instead of forcing `emptyExternRegistry`.
- `PredSatLaws.match_iff` is registry-parametric, so guard-alignment reasoning
  in `StepFRIte.lean` can consume condition runs from populated-registry
  initial configs.
- `config_eq_of_registry` in `LeanProofs/StepFR.lean` is the
  registry-parametric replacement for recursive-call rewrites that previously
  used `config_eq_of_registry_default`.
- `LeanProofs/ExternBoundary.lean` defines:
  - extern declaration and call boundary run predicates;
  - `ExternBoundarySpec`;
  - `TrustedExternEntry`;
  - `TrustedRegistry` and `TrustedRegistry.toRuntimeRegistry`;
  - `ExternDeclarationInProgram`;
  - trusted registry / closure-list agreement predicates;
  - trusted-to-runtime lookup transport in both directions;
  - boundary-run constructors for trusted extern calls and declarations.
- `TerminatesToAppSuccess` and `terminatesTo_app_inv_full` expose user and
  extern application branches without assuming an empty runtime registry.
- `FaultRobustnessSpecWithRegistry` states the registry-relative top-level
  property.
- `TypeSystemEnforcesFaultRobustness_emptyRegistry` proves the existing theorem
  is the empty-registry instance of the registry-relative spec.
- `StepFRPost` now stores `BoundaryTagMeaningPost` rather than an
  expression-indexed `IsCanonicalExtension`.  The expression parameter remains
  phantom for caller stability, and ordinary source proofs build posts through
  compatibility constructors/projections.
- `StepFRApp.lean` has cursor/member extraction helpers for extern closure-list
  entries in threaded `applyFnTClosureAtCursor` and
  `applyPFnTClosureAtCursor` maps.  These expose the member result needed by a
  future app-side transport helper.
- The extern closure invariant extension is implemented and compiling:
  `deepValueQTypProperty`, `closureCapturedVarsRegime`, `agreeValueUnder`, the
  transport/projection lemmas, and the known inversion sites now include
  extern-arrow / extern-parrow cases.
- `StepFRApp.lean` has extern captured-env extractors and a named
  `AppTwoRunOutPack` / `AppTwoRunOutChoice` post core for the app-side
  body-to-join transport refactor.
- `ExternBoundary.lean` has program-membership based trusted lookup helpers
  (`TrustedRegistryAgreesWithProgram.resolve*Declaration` and
  `.callBoundaryRun*`) in addition to the closure-list extern-member helpers.
- `FaultRobustnessProofs.lean` no longer carries local extern declaration
  inversion plumbing.  Successful `externVal`, `externFn`, and `externPfn`
  declaration runs are normalized to `ExternDeclBoundaryRun` by helpers in
  `ExternBoundary.lean`, and the top-level proof branches consume declaration
  boundary contract adapters instead of unfolding `beval` in-place.
- `StepFRApp.lean` now uses `terminatesTo_app_inv_full` directly in the main
  app splits.  The old empty-user-only app inversion wrapper is no longer used.
- `StepFRApp.lean` has trusted lookup-side constructors
  `ExternCallBoundaryFnStaticSource.callBoundaryRun` and
  `ExternCallBoundaryPfnStaticSource.callBoundaryRun`.  These turn static
  extern source evidence plus runtime facts into `ExternCallBoundaryRun`
  evidence using closure-list agreement.  The impure `externFn`
  regular-extern-body path is explicit as a separate resolver premise, because
  closure-list extern agreement alone does not cover
  `FnTClosure.regular x (Expr.externFn id y ...) ...`.  The pure `externPfn`
  source has only the extern-member case, because a regular pure closure body
  must pass `Expr.toPExpr?`.
- `StepFRApp.lean` also has the packaged two-run transport helper
  `appTwoRunOutChoice_from_body_stepFRPost`.  It is the intended adapter from a
  body-local `StepFRPost` to an app-level `AppTwoRunOutChoice`.  Its
  lower-level pieces are used by regular branches, and the packaged
  body-post-to-app shape has now been validated against a boundary-produced
  `StepFRPost`.
- `StepFRApp.lean` has a compiled boundary-consumption wrapper,
  `appTwoRunOutChoice_from_call_boundaryFR`, that consumes an
  `ExternCallBoundaryFR`, obtains the body-local `StepFRPost`, and feeds it
  through `appTwoRunOutChoice_from_body_stepFRPost`.  This validates that the
  existential realization maps returned by the boundary post compose with the
  app transport continuation.
- The six local app extern-call contracts in `StepFRApp.lean` no longer promise
  the final outer `Expr.app` post.  The two single-run contracts return
  `ExternBoundarySinglePost` for a body/member result, and the four two-run side
  contracts return body-local `ExternCallBoundaryRun` evidence indexed by an
  `ExternCallEntry` and member `result3`.

Still true:

- The populated-registry theorem is not proven yet.
- `StepFRApp` still discharges successful `externFn` / `externPfn` runtime
  branches under the current empty-registry theorem.  Those branches are now
  closed directly by registry preservation and empty lookup contradiction,
  rather than by an outer-post provider contract.
- The populated app proof is not wired yet: successful extern branches still
  need to build `ExternCallEntry`, produce body entry agreement, consume trusted
  boundary evidence, and transport the resulting body post through the app
  helpers.
- The top-level `externVal`, `externFn`, and `externPfn` proof branches no
  longer inline the empty-registry contradiction, but the current theorem is
  still the empty-registry instance, so the declaration boundary adapters still
  discharge through empty-registry lookup contradiction.  The populated theorem
  must replace those adapters with trusted-registry/spec-backed consumers.
- `TypeSystemEnforcesFaultRobustness_step` currently proves the default
  empty-registry instance of the registry-parametric step spec; it has not yet
  been generalized to arbitrary `registry`.

Latest verification after the app provider-contract reshape:

- `lake build LeanProofs` succeeds.
- `make lean-build-file FILE=LeanProofs/StepFRApp.lean` succeeds.
- `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeded
  at the declaration-boundary checkpoint.
- `make test` passed at the declaration-boundary checkpoint.
- `git diff --check` is clean.
- No new actual `sorry` or `axiom` was introduced.  Existing `sorry` warnings in
  `LeanProofs/SemanticsProperties.lean` remain pre-existing.

## Main Refactor

The remaining work is now an extern-boundary evidence refactor.  The
registry-parametric theorem spine exists and compiles, but the populated
registry cannot be completed until app extern-call evidence is consumed at the
right proof boundary.

With a populated registry, extern declaration expressions can terminate.  The
current declaration branches in `FaultRobustnessProofs.lean` have already been
reshaped so successful runs become `ExternDeclBoundaryRun` evidence before the
empty-registry instance discharges them.  When the populated theorem is added,
those adapters must be replaced by trusted-registry consumers of
`ExternBoundarySpec.declFR`, `ExternBoundarySpec.declSingle`, and
`ExternBoundarySpec.wf`.

Successful extern calls are different from declaration expressions: the extern
boundary should justify only the body-level call result.  The surrounding
application proof owns the app-specific transport through
`applyFnTClosure` / `applyPFnTClosure`, provenance normalization,
`joinTypeResults`, and the final app configuration restoration.  This keeps
concrete `ExternBoundarySpec` instances independent of app proof internals.

The change is proof-side only.  It does not change evaluation, typechecking, or
the existing empty-registry compatibility theorem.  The new populated-registry
theorem will add explicit trusted-registry assumptions rather than weakening
fault-robustness.

## Current Blocker

The active blocker has moved from contract shape to app transport integration.
The local extern-call contracts are now body-local, and the lookup side can
already build `ExternCallBoundaryRun` evidence from trusted registry agreement.
The regular user-closure branches still need to be rewired so their existing
body-post reasoning flows through the packaged app transport helpers.

The target populated path is:

1. Build an `ExternCallEntry` at the successful runtime extern branch.
2. Prove the body entry inputs agree.
3. Consume:

```lean
entry.spec.callFR ... :
  StepFRPost entry.bodyCtx postExpr memberResult predSat tm ...
```

4. Transport that member post through provenance normalization,
`joinTypeResults`, and app-config restoration.

The first transport-specific risk has been checked:
`appTwoRunOutChoice_from_call_boundaryFR` composes the body-local post produced
by an `ExternCallBoundaryFR` with the packaged app transport helper.  The next
step is to validate and use that transport shape in the regular user-closure
branches, before the extern proof depends on it.

The remaining app-specific wrinkle is also still relevant: runtime `externFn`
dispatch is not forced to originate from a `FnTClosure.extern` member.  It can
also arise from a regular closure whose body AST is `Expr.externFn ...`, because
runtime app dispatch matches on the closure body.  Therefore the populated app
proof needs two trusted lookup paths:

- `FnTClosure.extern` / `PFnTClosure.extern` membership uses
  `TrustedRegistryAgreesWithFnTClosures` /
  `TrustedRegistryAgreesWithPFnTClosures`.
- Regular closure members with an extern body AST use
  `TrustedRegistryAgreesWithProgram` evidence for the corresponding
  `ExternDeclarationInProgram` node, via the new program-membership lookup
  helpers, or a precise typed-closure provenance invariant if program
  membership cannot be recovered from the current closure evidence.

Changing `ExternBoundarySpec.callFR` to return an outer app post is still the
wrong direction: it would push app-specific `apply*Closure`/join/restoration
reasoning into every concrete extern boundary.

## Suggested Fixing Direction

The high-risk next fix is to validate the app transport shape on regular
user-closure branches before using it for populated extern branches.  This keeps
transport debugging separate from trusted-registry lookup and body-entry
agreement construction.

1. Validate the new shape on regular user-closure branches before using it for
   extern branches.  This prevents the extern proof from debugging transport
   and boundary lookup at the same time.

2. After the regular branch is wired through the helper, use
   `ExternCallBoundaryFnStaticSource.callBoundaryRun` and
   `ExternCallBoundaryPfnStaticSource.callBoundaryRun` to build
   `ExternCallBoundaryRun` evidence in the successful extern runtime branches.
   Then consume `entry.spec.callSingle` or `entry.spec.callFR` and pass the
   resulting body-local post into the app transport helper.

3. For impure regular-extern-body dispatch, add a precise resolver premise or
   derivation that connects
   `FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls`
   to a trusted entry.  Closure-list extern agreement alone is insufficient for
   this case.  If the current facts cannot recover an
   `ExternDeclarationInProgram` witness, add a named typed-closure provenance
   invariant and thread it explicitly rather than weakening
   `TrustedRegistryAgreesWithProgram` into a vague global premise.

This remains proof-side only.  It does not change evaluation, typechecking, or
the empty-registry theorem.  The populated theorem will still be a relative
theorem with explicit trusted-registry assumptions.

## Remaining Plan

1. **Validate app transport helpers on regular branches.**

   Rewire the existing regular user-closure app branches to use the new
   body-post-to-app transport shape.  Keep this step free of trusted-registry
   lookup so that failures isolate the transport interface.

   Expected helper families:

   - single-run masked-regime arrow;
   - single-run masked-regime parrow;
   - two-run arrow side 0;
   - two-run arrow side 1;
   - two-run parrow side 0;
   - two-run parrow side 1.

   Done when the regular branches compile through the new helper interface and
   `lake build LeanProofs` succeeds.

2. **Consume extern call boundaries in `StepFRApp`.**

   In successful `externFn` / `externPfn` branches, build `ExternCallEntry`,
   prove the body entry inputs agree, construct `ExternCallBoundaryRun.fn` /
   `.pfn` using `ExternCallBoundaryFnStaticSource.callBoundaryRun` /
   `ExternCallBoundaryPfnStaticSource.callBoundaryRun`, consume
   `entry.spec.callSingle` / `entry.spec.callFR`, and feed the body-boundary
   post into the transport helper from steps 1-2.

   For `FnTClosure.extern` / `PFnTClosure.extern` members, resolve trusted
   entries through `TrustedRegistryAgreesWithFnTClosures` /
   `TrustedRegistryAgreesWithPFnTClosures`.  For regular impure closure members
   whose body is `Expr.externFn`, use a precise regular-extern-body resolver
   derived from program membership or an explicit typed-closure provenance
   invariant.

   Done when app runtime `externFn` / `externPfn` dispatch is no longer proved
   impossible from `emptyExternRegistry`.

3. **Replace declaration adapters with populated-registry consumers.**

   The top-level extern expression branches already normalize successful
   declaration runs to `ExternDeclBoundaryRun`.  After the app proof is
   registry-backed, replace the empty-registry declaration adapters with
   trusted-registry lookup plus `ExternBoundarySpec` declaration fields:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - `wf` for operational well-formedness consumers.

   Done when the declaration branches consume trusted boundary evidence instead
   of `.of_emptyExternRegistry` adapters.

4. **Generalize the step theorem and bridge trusted agreement.**

   Generalize `TypeSystemEnforcesFaultRobustness_step` to arbitrary
   `registry`, instantiate it with `TrustedRegistry.toRuntimeRegistry tr`, and
   add the public populated-registry theorem under explicit assumptions:

   - `TrustedRegistryAgreesWithProgram e tr`;
   - `TrustedRegistryAgreesWithFnTClosures` facts for executed impure extern
     closure lists;
   - `TrustedRegistryAgreesWithPFnTClosures` facts for executed pure extern
     closure lists.

   The closure-list assumptions should be derived from typechecking facts where
   possible, without weakening `TrustedRegistryAgreesWithProgram` into a vague
   global premise.

5. **Preserve compatibility and verify.**

   Preserve `TypeSystemEnforcesFaultRobustness_emptyRegistry` as the
   compatibility corollary.  Run `lake build LeanProofs`, `make test`,
   `git diff --check`, and a `sorry` / `axiom` scan.

## Acceptance Criteria

- `lake build LeanProofs` succeeds.
- `make test` passes.
- `git diff --check` is clean.
- No new `sorry`.
- No new `axiom`.
- Existing empty-registry theorem still compiles.
- New populated-registry theorem is explicit about its trusted-registry
  assumptions.

## Hard Stops

- Stop if a body-to-app transport helper needs facts that are not already
  present in the regular user-closure app proof or in `ExternBoundarySpec`.
- Stop if `ExternCallEntry.bodyCtx` cannot be connected to the app body context
  built by the closure-start machinery without changing runtime syntax.
- Stop if the bridge from closure-list membership to trusted registry lookup
  cannot be stated without weakening `TrustedRegistryAgreesWithProgram` into a
  vague global assumption.
- Stop if a regular `FnTClosure.regular x (Expr.externFn ...) ...` runtime
  dispatch cannot be tied either to program-membership trusted agreement or to
  a precise typed-closure provenance premise.
- Stop if tying regular extern-body closure membership to trusted lookup
  requires weakening `TrustedRegistryAgreesWithProgram` into a global
  "all extern ids are trusted" premise instead of adding a precise provenance
  invariant.
- Stop if a required `ExternBoundarySpec` field lacks enough payload to
  reconstruct the body post needed by the app transport helper.
- Stop if the `Expr.externFn` / `Expr.externPfn` declaration step proofs cannot
  construct `closureCapturedVarsRegime` and clean extern closure agreement from
  typing-side facts and trusted-registry lookup alone, without circular
  dependence on `ExternBoundarySpec`.
