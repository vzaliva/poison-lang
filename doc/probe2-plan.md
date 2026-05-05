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
  - trusted registry / closure-list agreement predicates.
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
- Top-level `externVal`, `externFn`, and `externPfn` proof branches still rely
  on empty-registry contradiction.
- `TypeSystemEnforcesFaultRobustness_step` currently proves the default
  empty-registry instance of the registry-parametric step spec; it has not yet
  been generalized to arbitrary `registry`.

Last verification after the registry-parametric spine work:

- `lake build LeanProofs` succeeds.
- `make test` passes.
- `git diff --check` is clean.
- No new actual `sorry` or `axiom` was introduced.  Existing `sorry` warnings in
  `LeanProofs/SemanticsProperties.lean` remain pre-existing.

## Main Refactor

The remaining work is now an extern-boundary evidence refactor.  The
registry-parametric theorem spine exists and compiles, but the populated
registry cannot be completed until app extern-call evidence can be connected to
trusted registry entries without losing the extern argument type.

With a populated registry, extern declaration expressions can terminate.
Therefore the current declaration branches in `FaultRobustnessProofs.lean` are
no longer vacuous. They must consume declaration-boundary evidence from
`ExternBoundarySpec.declFR`, `ExternBoundarySpec.declSingle`, and
`ExternBoundarySpec.wf`.

At the same time, recursive application reasoning needs IHs for configs carrying
the same populated registry. That requires registry-parametric versions of:

- `StepFR`;
- `StepFR_IH`;
- `StepFRSingleRunFinalCleanPcTrue`;
- `StepFRSingleRunFinalCleanPcTrue_IH`;
- `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`;
- `StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH`.

This part is complete.  The remaining app-call bridge needs stronger trusted
closure-list agreement.

## Current Blocker

The attempted `StepFRApp.lean` migration reached a concrete payload mismatch.
`ExternCallFnFacts.impl_success` and `ExternCallPfnFacts.impl_success` require:

```lean
valueMatchesTyp entry.argValue d.typ = true
```

The runtime app inversion (`terminatesTo_app_inv_full`) gives the corresponding
fact for the AST argument type carried by the runtime extern body:

```lean
valueMatchesTyp v₂ argTyp = true
```

To rewrite this fact, the proof must know `d.typ = argTyp` for the trusted
entry that was found from a static closure-list member.  The current trusted
closure-list bridge does not expose that.  In `LeanProofs/ExternBoundary.lean`:

```lean
TrustedRegistryEntryMatchesFn entry id x retSpec effects
TrustedRegistryEntryMatchesPfn entry id x retSpec
TrustedRegistryAgreesWithFnTClosures tr tcls
TrustedRegistryAgreesWithPFnTClosures tr tcls
```

match the id, argument name, return spec, and effects, but not the declared
argument type.  Meanwhile `FnTClosure.extern` / `PFnTClosure.extern` members do
not store `argTyp`, so the current closure-list agreement cannot recover it from
membership alone.

This is the precise reason the local empty-registry providers in `StepFRApp`
could not yet be replaced by `ExternBoundarySpec.callFR` / `callSingle`.

## Suggested Fixing Direction

Prefer strengthening the proof-side agreement predicates before changing runtime
syntax:

1. Extend the trusted-entry match predicates to carry the extern argument type:

   ```lean
   def TrustedRegistryEntryMatchesFn
       (entry : TrustedExternEntry) (id : ExternId) (x : Name)
       (argTyp : Typ) (retSpec : ExternReturn) (effects : List Effect) : Prop :=
     entry.decl.id = id ∧
     entry.decl.kind = .fn ∧
     entry.decl.typ = argTyp ∧
     entry.decl.argName = some x ∧
     entry.decl.retSpec = some retSpec ∧
     entry.decl.effects = effects
   ```

   and analogously for `TrustedRegistryEntryMatchesPfn`.

2. Make closure-list agreement indexed by the ambient arrow/parrow argument
   type rather than by `tcls` alone:

   ```lean
   def TrustedRegistryAgreesWithFnTClosures
       (tr : TrustedRegistry) (argTyp : Typ) (tcls : List FnTClosure) : Prop := ...

   def TrustedRegistryAgreesWithPFnTClosures
       (tr : TrustedRegistry) (argTyp : Typ) (tcls : List PFnTClosure) : Prop := ...
   ```

   In app proofs the ambient argument type is available from the function type
   (`ETyp.arrow st1 st2 p tcls` / `ETyp.parrow st1 st2 p tcls`) and from
   `valueHasETyp.closure_extern` inversion, which also relates the runtime
   extern-body `argTyp` to that arrow/parrow argument type by constructor
   injectivity.

3. Prove lookup transport lemmas from `TrustedRegistry.lookup? tr id = some entry`
   to `(TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl`, plus
   the shape equalities from the strengthened match predicates.  These lemmas
   should be small and live near `TrustedRegistry` / agreement definitions.

4. Re-enter `StepFRApp.lean`:

   - switch populated-registry application cases from `terminatesTo_app_inv'` to
     `terminatesTo_app_inv_full`;
   - construct `ExternCallEntry` from the full app inversion payload;
   - construct `ExternCallBoundaryRun.fn` / `.pfn` using the runtime `hArg` fact
     rewritten through `entry.decl.typ = argTyp`;
   - consume `entry.spec.callFR` and `entry.spec.callSingle`.

Only if the arg-type-indexed agreement becomes awkward or impossible should the
syntax-level closure descriptors be changed to store `argTyp` directly:
`FnTClosure.extern id x argTyp retSpec effects capturedEnv` and
`PFnTClosure.extern id x argTyp retSpec capturedEnv`.  That is a larger
implementation/proof churn and should be the fallback, not the first move.

## Plan

1. **Make the step theorem registry-parametric.** Done.

   `StepFR` and the single-run theorem families now carry a runtime registry
   parameter directly.  Initial config literals in these definitions include
   `registry := registry`.

   The existing empty-registry theorem remains the compatibility instance via
   `registry := emptyExternRegistry`.

2. **Update all non-app per-operator proof modules.** Done.

   Thread the registry-parametric IHs through every `StepFR*` module. Most
   non-extern cases should be mechanical because `terminatesTo_preserves_registry`
   already proves evaluation preserves the registry.

   Replace uses of `config_eq_of_registry_default` only where they are used to
   force empty-registry configs for recursive calls.

   Done when `lake build LeanProofs` succeeds with the registry-parametric
   `StepFR` spine and no behavior change to the empty-registry theorem.

3. **Strengthen trusted closure-list agreement with argument types.** Next.

   Implement the suggested fixing direction above before returning to app
   extern-call proofs.

4. **Switch application proofs to full app inversion.**

   In `StepFRApp.lean`, replace `terminatesTo_app_inv'` with
   `terminatesTo_app_inv_full` where populated registry support is needed.

   Keep the `Expr.toPExpr?` contradiction for user-pfn branches whose typed
   evidence is `peClosure_extern`; that argument is independent of the registry.

   Done when runtime `externFn` / `externPfn` branches are explicit proof cases
   rather than eliminated by empty-registry assumptions.

5. **Replace extern declaration vacuity.**

   In the top-level extern expression cases, use trusted-registry lookup plus
   `ExternBoundarySpec` declaration fields:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - `wf` for operational well-formedness consumers.

   Done when `externVal`, `externFn`, and `externPfn` cases no longer inspect
   `emptyExternRegistry` to prove contradiction.

6. **Bridge closure-list membership to trusted entries.**

   Connect the `FnTClosure.extern ... in tcls` and
   `PFnTClosure.extern ... in tcls` evidence exposed by `valueHasETyp` to
   trusted-registry lookup.

   The intended bridge uses:

   - `TrustedRegistryAgreesWithFnTClosures`;
   - `TrustedRegistryAgreesWithPFnTClosures`;
   - `TrustedRegistryAgreesWithProgram`;
   - typechecking facts that relate app closure lists to declarations in the
     source program or nested return descriptors.

   Done when the local provider wrapper in `StepFRApp.lean` can be replaced by
   registry lookup and `ExternBoundarySpec.callFR` / `callSingle`.

7. **Prove the populated-registry top-level theorem.**

   Add the public theorem that instantiates the registry-relative spec with
   `TrustedRegistry.toRuntimeRegistry tr` under trusted-registry agreement.

   Preserve `TypeSystemEnforcesFaultRobustness_emptyRegistry` as the
   compatibility corollary.

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

- Stop if registry-parametric `StepFRPost` needs facts that are not available
  from either typechecking or `ExternBoundarySpec`.
- Stop if the bridge from closure-list membership to trusted registry lookup
  cannot be stated without weakening `TrustedRegistryAgreesWithProgram` into a
  vague global assumption.
- Stop if a concrete extern boundary would need to prove
  `IsCanonicalExtension` for an arbitrary `postExpr`. In that case, refactor
  `StepFRPost` to use `BoundaryTagMeaningPost` directly before continuing.
