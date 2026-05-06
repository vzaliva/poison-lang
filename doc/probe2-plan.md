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

Still true:

- The populated-registry theorem is not proven yet.
- `StepFRApp` still consumes empty-registry local providers in the extern arrow
  cases.
- The main two-run app proof still uses
  `terminatesTo_app_inv_full_empty_user_only` at the arrow/parrow runtime
  splits, so successful `externFn` / `externPfn` runtime branches are still
  discharged inside the empty-registry wrapper rather than consumed directly.
- Top-level `externVal`, `externFn`, and `externPfn` proof branches still rely
  on empty-registry contradiction.
- `TypeSystemEnforcesFaultRobustness_step` currently proves the default
  empty-registry instance of the registry-parametric step spec; it has not yet
  been generalized to arbitrary `registry`.

Latest verification after the `StepFRPost` / `StepFRApp` helper updates:

- `lake build LeanProofs` succeeds.
- `make test` passes on rerun.  The first run had transient tree-sitter cache
  load failures while `poison.so` was being rebuilt.
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

The `StepFRPost` tag-meaning mismatch and the captured-env invariant gap are
resolved.  The active blocker is now the app proof structure itself:
`StepFRApp.lean` must expose the existing body-to-app transport as reusable
helpers before successful runtime extern branches can consume
`ExternBoundarySpec.callFR` / `callSingle`.

`ExternBoundarySpec.callFR` is intentionally body-local.  For a successful
extern call, the app proof should build an `ExternCallEntry`, prove the body
entry inputs agree, consume:

```lean
entry.spec.callFR ... :
  StepFRPost entry.bodyCtx postExpr memberResult predSat tm ...
```

and then transport that member post through provenance normalization,
`joinTypeResults`, and app-config restoration.

A new app-specific wrinkle is now mapped: runtime `externFn` dispatch is not
forced to originate from a `FnTClosure.extern` member.  It can also arise from a
regular closure whose body AST is `Expr.externFn ...`, because runtime app
dispatch matches on the closure body.  Therefore the populated app proof needs
two trusted lookup paths:

- `FnTClosure.extern` / `PFnTClosure.extern` membership uses
  `TrustedRegistryAgreesWithFnTClosures` /
  `TrustedRegistryAgreesWithPFnTClosures`.
- Regular closure members with an extern body AST use
  `TrustedRegistryAgreesWithProgram` evidence for the corresponding
  `ExternDeclarationInProgram` node, via the new program-membership lookup
  helpers.

Changing `ExternBoundarySpec.callFR` to return an outer app post is still the
wrong direction: it would push app-specific `apply*Closure`/join/restoration
reasoning into every concrete extern boundary.

## Suggested Fixing Direction

The remaining fix should factor the app proof's existing body-to-app transport
instead of strengthening the extern boundary into an outer-app post provider.

1. Extend closure captured-regime and clean-agreement invariants for extern
   closure members.  This step is implemented and compiling.

   - 1a. Add extern-member constructors to `deepValueQTypProperty` and clean
     extern closure agreement constructors to `agreeValueUnder`.
   - 1b. Repair transport, monotonicity, and projection lemmas, including
     `deepValueQTypProperty_mono`, `closureCapturedVarsRegime` transports, and
     regular-member extraction helpers.
   - 1c. Sweep inversion sites that currently assume only regular closure
     cases.  The expected surface is non-trivial, including `StepFRVar.lean`,
     `StepFRAssign.lean`, `StepFRVlet.lean`, `StepFRFnPfn.lean`, and
     `FaultRobustnessProofs.lean`.
   - 1d. Add producer-side construction for populated-registry
     `Expr.externFn` / `Expr.externPfn` declaration steps.  These cases must
     construct the new `closureCapturedVarsRegime` and clean extern agreement
     facts from typing-side captured-env facts and runtime registry lookup,
     without circular dependence on `ExternBoundarySpec`.

   This preserves the current regular-member extraction used by the
   user-closure app proof and adds extern-member extraction for future
   `BodyEntryInputsAgree` construction.  The remaining producer use is in the
   populated direct extern declaration branches, when those branches stop being
   empty-registry vacuity.

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
   Handle both static extern closure-list members and regular closure members
   whose body AST is an extern declaration.

4. Replace the local empty-registry providers with lookup-based providers using
   `TrustedRegistryAgreesWithFnTClosures`,
   `TrustedRegistryAgreesWithPFnTClosures`, and the strengthened trusted-entry
   match predicates already present in `ExternBoundary.lean`.

## Remaining Plan

1. **Extend extern closure regime/agreement invariants.** Completed.

   This was the highest-risk remaining step.  The shared closure
   captured-variable and clean-agreement relations so extern closure-list
   members carry the same captured-env regime, typing, and agreement payload
   that regular members already carry.

   1a. Add extern constructors.

   - Add extern-arrow and extern-parrow cases to the deep property used by
     `closureCapturedVarsRegime`.
   - Add corresponding clean extern closure agreement constructors to
     `agreeValueUnder`.
   - Preserve theorem strength: this is an extension of the value invariant,
     not a new precondition on fault-robustness.

   1b. Repair shared transport and projection lemmas.

   - Update `deepValueQTypProperty_mono`, `closureCapturedVarsRegime`
     transport lemmas, `valueConsistentWithRegime` transports, and agreement
     transport helpers for the new constructors.
   - Keep the current regular-member extractors unchanged in behavior.
   - Add extern-member extractors that expose captured-env typing, captured-env
     regime evidence, and captured-env agreement for `BodyEntryInputsAgree`.

   1c. Sweep consumer inversion sites.

   - Update every case split that currently has only regular `closure` /
     `peClosure` branches.  Expected files include `StepFRVar.lean`,
     `StepFRAssign.lean`, `StepFRVlet.lean`, `StepFRFnPfn.lean`, and
     `FaultRobustnessProofs.lean`.
   - Empty-registry-only paths may keep vacuity arguments where the operational
     premise is still impossible, but the new constructors must be handled
     syntactically so the populated-registry theorem has a route.

   1d. Add producer-side construction.

   - In the direct `Expr.externFn` / `Expr.externPfn` declaration branches,
     construct the new closure captured-regime and clean extern agreement facts
     when a populated registry returns an extern closure value.
   - The construction should use typing-side captured-env facts, runtime
     instantiation, registry lookup, and trusted-entry agreement.  It must not
     assume `ExternBoundarySpec.callFR`; declaration producers are upstream of
     app call boundaries.

   Current status: 1a-1c are implemented and compiling, including the
   extern-member extraction needed for later `BodyEntryInputsAgree`
   construction.  The producer-side use in 1d remains part of the populated
   direct extern declaration proof, because those branches are still
   empty-registry vacuity in the current theorem.

2. **Re-architect app body-to-app transport.**

   This is still a high-risk step after the invariant extension.  In
   `LeanProofs/StepFRApp.lean`,
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

   Runtime `externFn` dispatch has two static shapes.  If the closure-list
   member is `FnTClosure.extern`, resolve it through
   `TrustedRegistryAgreesWithFnTClosures`.  If the member is regular but its
   body is `Expr.externFn`, resolve the trusted entry through
   `TrustedRegistryAgreesWithProgram` for the corresponding declaration node.
   The pure `externPfn` path is expected to use the extern-member route because
   regular pure closures require `Expr.toPExpr? body = some ...`.

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
- Stop if a required `ExternBoundarySpec` field lacks enough payload to
  reconstruct the body post needed by the app transport helper.
- Stop if the `Expr.externFn` / `Expr.externPfn` declaration step proofs cannot
  construct `closureCapturedVarsRegime` and clean extern closure agreement from
  typing-side facts and trusted-registry lookup alone, without circular
  dependence on `ExternBoundarySpec`.
