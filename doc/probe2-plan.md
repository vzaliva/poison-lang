# Probe 2 Plan: Registry-Aware Extern Boundaries

## Objective

Complete the proof-side bridge from the current empty-registry fault-robustness
theorem to a registry-aware extern-boundary theorem.

This is the Probe 2 sub-task of `doc/ffi-axioms.md`. It is about consuming
trusted boundary evidence in the proof stack. Reusable concrete driver
constructors such as `ExternBoundarySpec.pureUnaryCleanInt` are intentionally
left to the next high-level probe.

The staging target is a relative theorem:

```lean
TypeSystemEnforcesFaultRobustness_spec_with_registry
  (TrustedRegistry.toRuntimeRegistry tr) e s obs
```

under explicit trusted-registry agreement hypotheses.  The final public API
target is still `TypeSystemEnforcesFaultRobustness`: it should be updated to
take the non-empty runtime registry / trusted-registry proof obligations rather
than leaving the populated theorem as a parallel endpoint.  Compatibility
theorems may recover the old empty-registry formulation as corollaries.
Successful extern declarations and extern calls should be justified by
`ExternBoundarySpec` evidence instead of by the current empty-registry vacuity
arguments.

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
  `ExternBoundary.lean`, and the generalized proof core consumes declaration
  providers instead of unfolding `beval` in-place or proving successful
  declarations impossible from `emptyExternRegistry`.
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
- `StepFRApp.lean` now has provider-backed two-run paths for all successful
  runtime extern app-call branches.  The six branch finishers
  `finish_user_extern_p1p_true`, `finish_extern_user_p1p_true`,
  `finish_extern_extern_p1p_true`, `finish_user_pfn_extern_pfn_p1p_true`,
  `finish_extern_pfn_user_pfn_p1p_true`, and
  `finish_extern_pfn_extern_pfn_p1p_true` build or consume body-local extern
  boundary posts and transport them back to the final app post.  The
  dirty/non-internal and non-clean app fallback paths no longer discharge by
  contradiction from `emptyExternRegistry`.
- `StepFRApp.lean` keeps small provider-side adapters used by those paths:
  - `externCallBoundaryRun_singlePost` is the single canonical adapter from a
    successful `ExternCallBoundaryRun` plus `entry.spec.callSingle` to a
    body-local `ExternBoundarySinglePost`;
  - `externCallBoundaryRunProvider_singlePost` consumes the existential
    provider result directly and exposes the same body-local single post;
  - `externPfnStaticSource_of_valueConsistentWithRegime` mirrors the existing
    impure `externFn` source extractor, so both fn and pfn dirty paths get local
    provider inputs from value-consistency evidence.
- `stepFR_app` no longer carries the temporary `hregistry_empty` hypothesis.  It
  is registry-parametric at the app-call proof boundary.
- `ExternBoundary.lean` has registry-parametric declaration adapters from
  `ExternBoundarySpec.declSingle` / `ExternBoundarySpec.declFR`, plus trusted
  registry adapters
  `ExternDeclBoundarySingleMaskedContract.of_trustedRegistry` and
  `ExternDeclBoundaryFRContract.of_trustedRegistry`.
- `FaultRobustnessProofs.lean` now has `CanUse`-indexed proof cores for the
  masked single-run theorem, the ordinary single-run theorem, and the two-run
  step theorem.  The public empty-registry wrappers instantiate those cores with
  `CanUse := fun _ => True`; declaration branches themselves consume
  `CanUse`-indexed `hdeclSingle` / `hdeclFR` providers.
- `FaultRobustnessProofs.lean` has a registry-parametric implementation bridge
  `TypeSystemEnforcesFaultRobustness_impl_with_registry_for` that only requires
  a step theorem for the target expression.  The older global-form bridge is a
  wrapper around this root-expression-specific theorem.
- `FaultRobustnessProofs.lean` has root-aware declaration-provider wrappers for
  the masked single-run theorem, ordinary single-run theorem, and two-run step
  theorem.  These wrappers instantiate `CanUse current` as
  `ExternDeclLift root current` and discharge declaration providers from
  `ExternDeclSingleProviderFor registry root` /
  `ExternDeclFRProviderFor registry root`.
- `StepFRApp.lean` now accepts `WithExpr` single-run IHs in both the masked
  single-run app proof and the two-run app proof.  Regular closure-body
  recursive calls consume the app proof's `hcanFnBody` / `hcanPfnBody`
  provenance hooks, while compatibility wrappers recover the old plain-IH API.
- App-call providers in `FaultRobustnessProofs.lean` are now `CanUse`-indexed
  as well.  The root-aware proof wrappers instantiate `CanUse current` as
  `ExternDeclLift root current`, so extern call providers, declaration
  providers, and closure-body recursive calls are all scoped to the same root
  expression.
- `FaultRobustnessProofs.lean` has a public populated-registry theorem:

  ```lean
  TypeSystemEnforcesFaultRobustness
  ```

  It proves `TypeSystemEnforcesFaultRobustness_spec_with_registry
  (TrustedRegistry.toRuntimeRegistry tr) e s obs` from
  `TrustedRegistryAgreesWithProgram e tr` plus a new explicit
  `TrustedRegistryAppClosureProvenance e tr` assumption.  The implementation
  theorem `TypeSystemEnforcesFaultRobustness_with_trustedRegistry` is retained
  as a staging/helper wrapper under the public theorem.
- The original empty-registry public statement is retained as
  `TypeSystemEnforcesFaultRobustness_emptySpec`, and
  `TypeSystemEnforcesFaultRobustness_emptyRegistry` still proves the
  registry-relative empty instance.
- `ExternDeclLift` and `TrustedRegistryAppClosureProvenance` live in
  `ExternBoundary.lean`.  The provenance structure packages the remaining
  app-call obligations: regular closure bodies in app closure lists lift back to
  the root program; impure fn closure lists agree with the trusted registry;
  regular impure extern-body members resolve to trusted entries; and pure pfn
  closure lists agree with the trusted registry.

Still true:

- The public theorem now has the populated-registry shape, but its app-call
  provenance is still explicit.  The remaining target is to derive
  `TrustedRegistryAppClosureProvenance e tr` from typechecking facts and trusted
  registry agreement, then simplify the public assumptions accordingly.
- `TypeSystemEnforcesFaultRobustness_step` remains the public empty-registry
  compatibility theorem.  The generalized proof core exists privately and must
  eventually be wrapped or renamed by the populated public theorem.
- App-call providers are root-scoped but still not derived from typechecking
  itself.  `TrustedRegistryAppClosureProvenance` is currently an explicit
  theorem assumption; the remaining proof work is to derive that provenance from
  typed closure-list construction/transport instead of asking callers to supply
  it directly.
- `TrustedRegistryAppClosureProvenance` is temporary scaffolding, not a final
  public API.  Its current `fnClosures`, `pfnClosures`, and
  `fnRegularExternBody` fields quantify over arbitrary `tcls` lists, which is
  stronger than typing can honestly justify for a finite trusted registry.  The
  next slice must re-index those fields by actual typechecking provenance, then
  internalize them so the public theorem no longer exposes a separate `happ`
  premise.

Latest incremental verification after adding the trusted-registry theorem,
app provenance wrapper, and public theorem API switch:

- `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeds.

Latest full verification from the preceding provider-threading slice:

- `make lean-build-file FILE=LeanProofs/StepFRApp.lean` succeeds.
- `lake build LeanProofs` succeeds.
- `make test` passes 96/96.
- `git diff --check` is clean.
- `scripts/sorry-count.py --no-build` reports no `sorry` / `axiom` delta.
  Existing `sorry` warnings in `LeanProofs/SemanticsProperties.lean` remain
  pre-existing.

## Main Refactor

The remaining work is now the root-provenance and top-level theorem bridge.
The registry-parametric theorem spine exists and compiles, app extern-call
evidence is consumed at the app proof boundary, and successful extern
declarations are routed through provider slots in the generalized proof core.
The populated top-level theorem cannot be completed until those provider slots
are discharged from root-program trusted-registry agreement rather than from
globally quantified provider hypotheses.

With a populated registry, extern declaration expressions can terminate.  The
current declaration branches in `FaultRobustnessProofs.lean` normalize
successful runs to `ExternDeclBoundaryRun` evidence and consume declaration
providers.  The next bridge is root expression provenance: each local extern
declaration proof must be lifted back to the top-level program before
`TrustedRegistryAgreesWithProgram root tr` can justify the boundary contract.

Successful extern calls are different from declaration expressions: the extern
boundary should justify only the body-level call result.  The surrounding
application proof owns the app-specific transport through
`applyFnTClosure` / `applyPFnTClosure`, provenance normalization,
`joinTypeResults`, and the final app configuration restoration.  This keeps
concrete `ExternBoundarySpec` instances independent of app proof internals.

The change is proof-side only.  It does not change evaluation or typechecking.
The populated top-level theorem will add explicit trusted-registry assumptions
rather than weakening fault-robustness, and the existing empty-registry theorem
will remain as a compatibility corollary.

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

The transport-specific risk has been checked and the app branches have been
wired through it.  `appTwoRunOutChoice_from_call_boundaryFR` composes the
body-local post produced by an `ExternCallBoundaryFR` with the packaged app
transport helper, and the dirty app-result transport uses
`appTwoRunOutChoice_from_independent_single_boundary_posts_dirty` to consume
per-side body-local `ExternBoundarySinglePost` values.  The `stepFR_app`
signature no longer needs an empty-registry equality witness.

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

The remaining work is no longer a masked-spine, app-extern transport, or
declaration-adapter problem.  It is typed closure-list provenance wiring for
the populated public theorem's final assumption shape:

1. The provider-parametric proof core is registry-parametric and
   root-expression-aware.  It is instantiated by the compiled staging theorem
   `TypeSystemEnforcesFaultRobustness_with_trustedRegistry`, which targets
   `TypeSystemEnforcesFaultRobustness_spec_with_registry
   (TrustedRegistry.toRuntimeRegistry tr) e s obs`.

2. Root-expression declaration provenance is threaded through the step proof
   core.  The lift shape is:

   ```lean
   ∀ {id d}, ExternDeclarationInProgram current id d →
     ExternDeclarationInProgram root id d
   ```

   Recursive calls compose this lift with the corresponding
   `ExternDeclarationInProgram` constructor (`op_left`, `ite_then`,
   `app_arg`, `fn_body`, and so on).  Declaration branches then lift their
   local immediate declaration witness to the root and consume
   `TrustedRegistryAgreesWithProgram root tr`.

3. The populated theorem currently assumes `TrustedRegistryAppClosureProvenance`,
   which packages the remaining closure-list facts.  The unresolved part is to
   derive this provenance from typed closure-list construction and transport.
   In particular, impure regular-extern-body dispatch must connect
   `FnTClosure.regular x (Expr.externFn id y argTyp retSpec effects) σcap ∈ tcls`
   to a trusted entry.  Closure-list extern agreement alone is insufficient for
   this case, so the proof must use a precise typed-closure provenance
   invariant rather than weakening `TrustedRegistryAgreesWithProgram` into a
   vague global premise.

This remains proof-side only.  It does not change evaluation or typechecking.
The populated top-level theorem will be relative to explicit trusted-registry
assumptions, and the old empty-registry theorem should remain available as a
compatibility corollary.

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

3. **Validate app transport helpers on regular branches.** **Done.**

   The regular user-closure app branches compile through the body-post-to-app
   transport shape, isolating the app transport interface before extern lookup
   was added.

4. **Consume extern call boundaries in `StepFRApp`.** **Done.**

   Successful `externFn` / `externPfn` branches now build `ExternCallEntry`
   values, use the local side providers to obtain body-local boundary evidence,
   consume `callFR` / `callSingle` through the body-post adapters, and transport
   the result through provenance normalization and `joinTypeResults` to the
   final app post.  The dirty/non-internal and non-clean fallback branches use
   the same provider-backed transport rather than empty-registry contradiction.

   The app proof no longer needs `hregistry_empty`, and `StepFRApp.lean` no
   longer proves runtime `externFn` / `externPfn` dispatch impossible from
   `emptyExternRegistry`.

   Verification after this slice:

   - `lake build LeanProofs` succeeds.
   - `make test` passes 96/96.
   - `git diff --check` succeeds.
   - `scripts/sorry-count.py --no-build` reports no sorry/axiom delta.

   The following slice completed Step 5 by moving the declaration branches onto
   provider hypotheses in the generalized proof core.

5. **Replace declaration adapters with populated-registry consumers.** **Done.**

   The top-level extern expression branches normalize successful declaration
   runs to `ExternDeclBoundaryRun`, and the generalized proof core consumes
   provider hypotheses rather than empty-registry contradiction adapters:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - trusted-registry lookup transport from program declaration membership to
     the matching `TrustedExternEntry`.

   No separate `ExternBoundarySpec.wf` consumer was needed in this step proof:
   the declaration posts returned by `declFR` / `declSingle` already carry the
   required output `wfConfig` facts.  The standalone `wf` field remains
   available for later operational consumers.

   The public empty-registry wrappers still instantiate those providers with
   `.of_emptyExternRegistry`, preserving the existing theorem.  The populated
   theorem should instantiate the same provider slots with the trusted-registry
   adapters added in `ExternBoundary.lean`.

6. **Generalize the step theorem and bridge trusted agreement.**

   Partially done.  The implementation bridge has been split so the top-level
   theorem only needs a step theorem for the target expression.  The step and
   single-run proof cores are root-expression aware for both declaration and
   app-call providers through `CanUse := ExternDeclLift root`.  The public
   populated-registry theorem is now:

   ```lean
   TypeSystemEnforcesFaultRobustness
   ```

   It proves the registry-relative spec for `TrustedRegistry.toRuntimeRegistry
   tr` from:

   - `TrustedRegistryAgreesWithProgram e tr`;
   - `TrustedRegistryAppClosureProvenance e tr`.

   The latter packages the closure-list agreement and regular-body provenance
   facts needed to build the single-run and two-run app-call providers.  This
   means the provider contract shape is now validated, but the provenance is
   still an explicit staging assumption rather than a fact derived from
   typechecking.

   Precision warning: the current staging structure is intentionally too strong.
   Its `fnClosures`, `pfnClosures`, and `fnRegularExternBody` fields quantify
   over arbitrary `tcls` lists.  That is sound as a theorem precondition, but it
   is close to the forbidden "registry agrees with every imaginable closure
   list" shape and is not a dischargeable final API for ordinary finite trusted
   registries.  Treat this as a temporary bridge only.

   Current blocker: derive `TrustedRegistryAppClosureProvenance e tr` from
   typed closure-list construction/transport.  The app proof API still sees
   closure-list membership as `FnTClosure.regular ... ∈ tcls` /
   `PFnTClosure.regular ... ∈ tcls`; it does not yet expose the typechecking
   provenance explaining why a regular closure body belongs to the root program
   or why a regular impure extern-body member resolves to a trusted entry.

   Suggested fix:

   1. High-risk first: replace the universal-over-`tcls` staging assumption with
      a typed closure-list provenance predicate for type results / closure
      lists, or prove that the existing typechecking data already implies the
      needed app provenance.  The predicate must state both:
      - every regular closure body in the list has an `ExternDeclLift root body`
        witness;
      - every extern closure member, and every regular extern-body member, can
        be resolved against the trusted registry without assuming global
        agreement for arbitrary closure lists.
   2. Prove the provenance predicate is produced/preserved by typechecking for
      arrow/parrow closure lists and transported through the app
      `apply*Closure` / join machinery.
   3. Use that provenance to build `TrustedRegistryAppClosureProvenance` for the
      top-level expression, especially the impure
      `FnTClosure.regular x (Expr.externFn ...) ...` case.  The provenance must
      survive closure-list joins/merges and function/pfunction body typing.
   4. Once the provenance is derivable, reduce the public assumptions so
      callers supply only the populated runtime/trusted registry obligations.
      The final public theorem should not expose
      `TrustedRegistryAppClosureProvenance e tr`; it should derive app-call
      provenance internally from `TrustedRegistryAgreesWithProgram e tr` plus
      typing facts, with the old empty-registry theorem retained as a
      compatibility corollary.

   Latest finding: the strong-induction callback problem for declarations and
   app calls is resolved through the `CanUse` / `WithExpr` IH variants.  The
   remaining proof edit is deriving app-call closure provenance from typing
   rather than assuming it at the staging theorem boundary.

7. **Preserve compatibility and verify.**

   Preserve `TypeSystemEnforcesFaultRobustness_emptyRegistry` as the
   compatibility corollary.  Run `lake build LeanProofs`, `make test`,
   `git diff --check`, and a `sorry` / `axiom` scan using
   `scripts/sorry-count.py`.

## Acceptance Criteria

- `lake build LeanProofs` succeeds.
- `make test` passes.
- `git diff --check` is clean.
- No new `sorry`.
- No new `axiom`.
- Existing empty-registry theorem still compiles.
- New populated-registry theorem is explicit about its trusted-registry
  assumptions.
- `TrustedRegistryAppClosureProvenance` is not exposed as a final public theorem
  premise.  If the structure remains internally, its closure-list fields are
  indexed by actual typechecking provenance rather than universally quantified
  over arbitrary `tcls`.

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
- Stop if direct `FnTClosure.extern` effect typing remains under caller
  `ctx.pc` and the dirty app branch must nevertheless prove source clean-back
  for clean effect-written memory locations.  In that shape the proof lacks the
  pre-state agreement needed for final clean memory agreement; fix the
  app-level extern effect pc first.
- Stop if the masked single-run theorem cannot supply ordinary
  `regimeConsistentWithCtx` to `ExternBoundarySpec.callSingle` and the only
  alternative is to silently assume ordinary tag-env consistency for masked
  tags.
- Stop if the `Expr.externFn` / `Expr.externPfn` declaration step proofs cannot
  construct `closureCapturedVarsRegime` and clean extern closure agreement from
  typing-side facts and trusted-registry lookup alone, without circular
  dependence on `ExternBoundarySpec`.
