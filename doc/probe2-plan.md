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
- `ExternCallEntry` now separates runtime dispatch from body-local proof
  shape.  `entry.callConfig` remains the actual runtime dispatch config, while
  `entry.bodyConfig` is the synthetic closure-body input config with
  `varEnv := entry.unifiedEnv`, and `entry.bodyOutputConfig cf` is the
  synthetic body-output config over a runtime extern result.  `BodyEntryInputsAgree`,
  `ExternCallBoundaryFR`, and `ExternCallBoundarySingle` now use these body
  configs for body-local posts.

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

Latest verification after threading the masked true-tag absence invariant:

- `lake build LeanProofs` succeeds.
- `make lean-build-file FILE=LeanProofs/StepFRApp.lean` succeeds.
- `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeded
  after the masked-spine invariant was threaded through the orchestration proof.
- `make test` passed after the masked-spine invariant change.
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

## Current Status

The previous blocker in the single-run masked app spine is resolved.  A direct
attempt to
make `stepFRSingleRunFinalCleanPcTrue_app_*_parametric_maskedReg` arbitrary in
`registry` had exposed a mismatch between the masked induction theorem and the
current extern boundary API:

- `StepFRSingleRunFinalCleanPcTrueMaskedRegParam` is deliberately generic over
  `CtxCons` / `ValCons` and assumes only
  `regimeConsistentWithCtxMasked masked ctx`.
- `ExternBoundarySpec.callSingle` requires ordinary
  `regimeConsistentWithCtx bodyCtx` and ordinary
  `consistentWithRegime ... bodyCtx ...`.
- The existing unmasking lemmas recover ordinary value/context consistency
  from masked consistency plus
  `∀ k, masked k → R.lookup? k = none`, but they do not recover ordinary
  tag-env consistency.  That loss is real: a masked tag-env entry may be
  accepted precisely because it is masked while its regime lookup is `none`.

The fix is now implemented as `MaskedTagsAbsentFromTrueTagEnv`.  The masked
single-run proof carries the invariant, and
`regimeConsistentWithCtxMasked_unmask` combines it with masked tag-env
consistency to recover ordinary `regimeConsistentWithCtx`.  The invariant is
preserved through `ctxAfter`, branch tag insertion, assignment invalidation,
join, and app body contexts.

The option-2 structural check has been performed.  The current non-masked
single-run theorem is not an independent case split: it is a wrapper around
`TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked` with
`masked := fun _ => False`, followed by unmasking the final post.  The app case
is owned by the masked induction:

```lean
TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue
  -> TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked
  -> stepFRSingleRunFinalCleanPcTrue_app_maskedReg
  -> stepFRSingleRunFinalCleanPcTrue_app_*_parametric_maskedReg
```

Moreover, app expressions are reachable from genuinely masked recursive calls.
For example, the masked `ite` proof calls its recursive IH under branch contexts
such as `ctxTrue`; if that branch expression is an app, the app proof is reached
inside the masked spine rather than at the outer false-mask wrapper.  Therefore
successful extern-call boundary consumption cannot simply be hooked at the
outer non-masked theorem without a much larger direct ordinary single-run
induction.  Option 2 fails as a cheap local bridge.

This was distinct from lookup.  The local extern-call contracts are already
body-local, and the lookup side can build `ExternCallBoundaryRun` evidence from
trusted registry agreement.  The masked single-run proof can now provide the
ordinary tag-env consistency premise needed to call the boundary spec.

A second app-boundary mismatch was found and fixed: a single `callConfig` could
not serve both as the runtime extern dispatch config and as the body-local proof
input config.  Runtime extern dispatch must preserve the caller environment in
the actual app output, while the boundary post must be over the closure
environment extended with the argument.  The boundary layer now exposes
`bodyConfig` / `bodyOutputConfig` so app transport can restore the caller
configuration after consuming a body-local post.

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
step is to finish using the provider-backed contracts in the remaining app
extern branches and then replace the empty-registry provider at the app wrapper
with trusted-registry providers for the populated theorem.

The next concrete app blocker is
branch integration: successful extern branches must either fall back through
the existing dirty-internal app-result path, or, when both runs dispatch the
same trusted extern boundary, construct body entries, consume `callFR`, set the
body eval configs to `entry.bodyOutputConfig cf`, and then transport to the
actual app configs.  Single-run extern branches need the analogous body-output
transport.  If the existing normalized-member helper cannot consume an extern
member result directly, add either a direct-member transport variant or an
extern-apply inversion lemma that exposes the pre-normalized body result
expected by the current helper.

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

## Implemented Fix And Next Direction

Option 1 has landed: the proof spine now threads the smallest invariant needed
to recover ordinary tag-env consistency from masked tag-env consistency at
boundary call sites.

The predicate is:

```lean
MaskedTagsAbsentFromTrueTagEnv masked ctx :=
  ∀ k deps, masked k → ctx.tagEnv.get? k = some ⟨true, deps⟩ → False
```

Together with `regimeConsistentWithCtxMasked masked ctx`, this proves ordinary
`regimeConsistentWithCtx ctx`: each true tag-env entry is either masked or has
`R.lookup? k = some true`; the invariant eliminates the masked case.  The
initial false mask satisfies the invariant, `typecheck` preservation threads it
through `ctxAfter`, `tagEnv.insert ... false` preserves it immediately, and
`tagEnv.insert ... true` is discharged by contradicting `hmasked_none`.

The remaining work is no longer a masked-spine API problem.  It is the app
extern provider and top-level registry wiring:

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

1. **Thread the masked true-tag absence invariant.** **Done.**

   `MaskedTagsAbsentFromTrueTagEnv` is added and the bridge is proved:

   ```lean
   regimeConsistentWithCtxMasked masked ctx →
   MaskedTagsAbsentFromTrueTagEnv masked ctx →
   regimeConsistentWithCtx ctx
   ```

   The invariant is threaded through
   `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`,
   `StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH`, the per-operator masked
   single-run lemmas, and the high-risk `ite`, assignment, and app body-context
   paths.  `LeanProofs/StepFRApp.lean`,
   `LeanProofs/FaultRobustnessProofs.lean`, and `lake build LeanProofs`
   compile.

2. **Larger ordinary-induction split.** **Not needed.**

   Option 1 succeeded, so the larger ordinary single-run induction split is not
   part of the active plan.

3. **Validate app transport helpers on regular branches.**

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

4. **Consume extern call boundaries in `StepFRApp`.**

   In successful `externFn` / `externPfn` branches, build `ExternCallEntry`,
   prove the body entry inputs agree over `entry.bodyConfig`, construct
   `ExternCallBoundaryRun.fn` /
   `.pfn` using `ExternCallBoundaryFnStaticSource.callBoundaryRun` /
   `ExternCallBoundaryPfnStaticSource.callBoundaryRun`, consume
   `entry.spec.callSingle` / `entry.spec.callFR`, and feed the body-boundary
   post over `entry.bodyOutputConfig cf` into the transport helper from steps
   1-2.

   Mixed user/extern closure branches should not use boundary evidence unless
   both sides are successful extern dispatches for the same body member.  Reuse
   the existing clean-sync reasoning to reduce clean mixed branches to
   contradiction and the dirty-internal fallback to the poisoned app result.

   For `FnTClosure.extern` / `PFnTClosure.extern` members, resolve trusted
   entries through `TrustedRegistryAgreesWithFnTClosures` /
   `TrustedRegistryAgreesWithPFnTClosures`.  For regular impure closure members
   whose body is `Expr.externFn`, use a precise regular-extern-body resolver
   derived from program membership or an explicit typed-closure provenance
   invariant.

   Done when app runtime `externFn` / `externPfn` dispatch is no longer proved
   impossible from `emptyExternRegistry`.

5. **Replace declaration adapters with populated-registry consumers.**

   The top-level extern expression branches already normalize successful
   declaration runs to `ExternDeclBoundaryRun`.  After the app proof is
   registry-backed, replace the empty-registry declaration adapters with
   trusted-registry lookup plus `ExternBoundarySpec` declaration fields:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - `wf` for operational well-formedness consumers.

   Done when the declaration branches consume trusted boundary evidence instead
   of `.of_emptyExternRegistry` adapters.

6. **Generalize the step theorem and bridge trusted agreement.**

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

7. **Preserve compatibility and verify.**

   Preserve `TypeSystemEnforcesFaultRobustness_emptyRegistry` as the
   compatibility corollary.  Run `lake build LeanProofs`, `make test`,
   `git diff --check`, and a `sorry` / `axiom` scan using `scripts/sorry-count.py` script.

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
- Stop if the masked single-run theorem cannot supply ordinary
  `regimeConsistentWithCtx` to `ExternBoundarySpec.callSingle` and the only
  alternative is to silently assume ordinary tag-env consistency for masked
  tags.
- Stop if the `Expr.externFn` / `Expr.externPfn` declaration step proofs cannot
  construct `closureCapturedVarsRegime` and clean extern closure agreement from
  typing-side facts and trusted-registry lookup alone, without circular
  dependence on `ExternBoundarySpec`.
