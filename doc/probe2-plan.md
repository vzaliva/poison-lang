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

Still true:

- The populated-registry theorem is not proven yet.
- `StepFRApp` still consumes empty-registry local providers in the extern arrow
  cases.
- `StepFRApp` now uses full app inversion at the remaining direct
  `terminatesTo_app_inv'` sites, but the successful `externFn` / `externPfn`
  runtime branches are still discharged only in the empty-registry wrapper.
- Top-level `externVal`, `externFn`, and `externPfn` proof branches still rely
  on empty-registry contradiction.
- `TypeSystemEnforcesFaultRobustness_step` currently proves the default
  empty-registry instance of the registry-parametric step spec; it has not yet
  been generalized to arbitrary `registry`.

Last verification after the app-inversion checkpoint:

- `lake build LeanProofs` succeeds.
- `make test` passes.
- `git diff --check` is clean.
- No new actual `sorry` or `axiom` was introduced.  Existing `sorry` warnings in
  `LeanProofs/SemanticsProperties.lean` remain pre-existing.

## Main Refactor

The remaining work is now an extern-boundary evidence refactor.  The
registry-parametric theorem spine exists and compiles, but the populated
registry cannot be completed until app extern-call evidence is consumed at the
right proof boundary.

With a populated registry, extern declaration expressions can terminate.
Therefore the current declaration branches in `FaultRobustnessProofs.lean` are
no longer vacuous. They must consume declaration-boundary evidence from
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

The next blocker is a postcondition-shape mismatch in the app extern-call
boundary.

`ExternBoundarySpec.callFR` and `callSingle` are body-boundary contracts.  For a
successful extern call, they produce post facts in the body context carried by
`ExternCallEntry`:

```lean
StepFRPost entry.bodyCtx postExpr res predSat tm ...
ExternBoundarySinglePost entry.bodyCtx res predSat tm ...
```

The current `StepFRApp.lean` local providers, however, are consumed at the point
where the app proof already expects the final joined application post:

```lean
StepFRPost ctxᵢ (Expr.app e1 e2) res predSat tm ...
StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost ... ctxᵢ res ...
```

Instantiating `callFR` with the outer app result gives a post in the wrong
context (`entry.bodyCtx` instead of `ctxᵢ`).  Instantiating it with the member
body result gives the right boundary meaning, but then the app proof must still
transport value typing, runtime instantiation, regime consistency,
`agreeOnClean`, value consistency, and clean-result agreement through:

1. the extern member result (`applyFnTClosure` / `applyPFnTClosure`);
2. `normalizeAppResultByProvenance`;
3. `joinTypeResults`; and
4. the app runtime restoration from the synthetic body-final config to the final
   app config.

The current local provider interfaces do not carry that static app-transport
payload, and `ExternBoundarySpec.callFR` / `callSingle` intentionally do not
know it.  Replacing the providers by direct calls to `entry.spec.callFR` would
therefore require a concrete extern boundary to prove an outer app
`StepFRPost`, which would force arbitrary `IsCanonicalExtension` evidence for a
post expression outside the extern boundary.

The tag-meaning part of this blocker is smaller than it first appears:
`IsCanonicalExtension`'s expression parameter is already phantom for
`StepFRPost` consumers.  The projections used from
`IsCanonicalExtension tm ctx e res tm'`, together with `PredSatLaws predSat tm'`
and `QTypRespectsTagMeaning tm' res.qualType`, are exactly the facts bundled by
`BoundaryTagMeaningPost ctx res predSat tm tm'`.  Refactoring `StepFRPost` to use
`BoundaryTagMeaningPost` is therefore bookkeeping, not a loss of information.

The real work is in `StepFRApp.lean`.  The current user-function proof does not
expose a body-level post as a clean intermediate: body identity, member/cursor
recovery from the threaded closure application, body IH consumption, and
body-to-app transport are interleaved.  The proof must be reorganized so those
concerns are separated before extern-call boundary evidence can be substituted.

## Suggested Fixing Direction

The remaining fix should factor the app proof's existing body-to-app transport
instead of strengthening the extern boundary into an outer-app post provider.

1. Refactor `StepFRPost` to use `BoundaryTagMeaningPost` as its tag-meaning
   component.  Keep the `e : Expr` parameter for caller-signature stability, but
   make it phantom in the definition.  Add compatibility constructors/projections
   so ordinary source proofs can still build posts from `IsCanonicalExtension`
   with minimal churn.

2. Reorganize the app proof to expose body-to-app transport as explicit helpers.
   This is the high-risk step.  It is not a one-shot extraction: first separate
   the existing user-function proof into:

   - body identity and regular-member/cursor recovery;
   - body post production or consumption;
   - pure transport from body post to the joined app post.

   Expect six transport helpers:

   - single-run masked-regime arrow;
   - single-run masked-regime parrow;
   - two-run arrow side 0;
   - two-run arrow side 1;
   - two-run parrow side 0;
   - two-run parrow side 1.

   The current regular user-closure branches should be rewired to use these
   helpers first.  That validates the helper statements before populated extern
   branches depend on them.

3. Use the helpers in successful extern runtime branches.  Construct
   `ExternCallEntry` from full app inversion payloads, verify that
   `entry.bodyCtx` matches the app body context built by the closure-start
   machinery, construct `ExternCallBoundaryRun.fn` / `.pfn` using the trusted
   lookup helpers, consume `entry.spec.callSingle` / `entry.spec.callFR`, and
   pass the body-boundary post into the corresponding app transport helper.

4. Replace the local empty-registry providers with lookup-based providers using
   `TrustedRegistryAgreesWithFnTClosures`,
   `TrustedRegistryAgreesWithPFnTClosures`, and the strengthened trusted-entry
   match predicates already present in `ExternBoundary.lean`.

## Remaining Plan

1. **Refactor `StepFRPost` to boundary tag meaning.**

   Change `LeanProofs/StepFR.lean` so `StepFRPost` stores
   `BoundaryTagMeaningPost ctx res predSat tm tm'` instead of direct
   `IsCanonicalExtension tm ctx e res tm'` plus separate tag-meaning facts.
   Keep the `e : Expr` parameter phantom for API stability.

   Done when ordinary source proofs can still construct `StepFRPost` from
   `IsCanonicalExtension`, all previous projection sites compile against the
   boundary post, and no theorem statement is weakened.

2. **Re-architect app body-to-app transport.**

   This is the highest-risk remaining step.  In `LeanProofs/StepFRApp.lean`,
   separate the current user-closure proof into body identity/member/cursor
   recovery, body post production/consumption, and transport from a body post to
   the joined app post.

   Implement and validate six helper shapes:

   - single-run masked-regime arrow;
   - single-run masked-regime parrow;
   - two-run arrow side 0;
   - two-run arrow side 1;
   - two-run parrow side 0;
   - two-run parrow side 1.

   Done when the existing regular user-closure app branches use these helpers
   and `lake build LeanProofs` still succeeds.  At this point no populated
   extern branch needs to be completed yet; the goal is to prove the transport
   interface on the known-good regular branches first.

3. **Consume extern call boundaries in `StepFRApp`.**

   Replace the empty-registry extern-call providers with lookup-based providers.
   In successful `externFn` / `externPfn` branches, use full app inversion to
   build `ExternCallEntry`, prove its `bodyCtx` agrees with the app body context,
   construct `ExternCallBoundaryRun.fn` / `.pfn` from trusted lookup and runtime
   facts, consume `entry.spec.callSingle` / `entry.spec.callFR`, and feed the
   body-boundary post into the transport helpers from step 2.

   Done when app runtime `externFn` / `externPfn` dispatch is no longer proved
   impossible from `emptyExternRegistry`.

4. **Replace extern declaration vacuity.**

   In the top-level extern expression cases in
   `LeanProofs/FaultRobustnessProofs.lean`, use trusted-registry lookup plus
   `ExternBoundarySpec` declaration fields:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - `wf` for operational well-formedness consumers.

   Done when `externVal`, `externFn`, and `externPfn` cases no longer inspect
   `emptyExternRegistry` to prove contradiction.

5. **Generalize the step theorem and bridge trusted agreement.**

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

6. **Preserve compatibility and verify.**

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

- Stop if the `StepFRPost` refactor to `BoundaryTagMeaningPost` reveals an
  information gap not recoverable from the old `IsCanonicalExtension`
  projections plus `PredSatLaws`.
- Stop if a body-to-app transport helper needs facts that are not already
  present in the regular user-closure app proof or in `ExternBoundarySpec`.
- Stop if `ExternCallEntry.bodyCtx` cannot be connected to the app body context
  built by the closure-start machinery without changing runtime syntax.
- Stop if the bridge from closure-list membership to trusted registry lookup
  cannot be stated without weakening `TrustedRegistryAgreesWithProgram` into a
  vague global assumption.
- Stop if a required `ExternBoundarySpec` field lacks enough payload to
  reconstruct the body post needed by the app transport helper.
