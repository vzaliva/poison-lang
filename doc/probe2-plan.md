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

## Current Baseline

Implemented and compiling:

- `StepFRPost` is shared in `LeanProofs/StepFR.lean`, and `StepFR` concludes it.
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
- `StepFR`, `StepFR_IH`, and the single-run IH families still build initial
  configs with the default empty registry.
- `StepFRApp` still consumes empty-registry local providers in the extern arrow
  cases.
- Top-level `externVal`, `externFn`, and `externPfn` proof branches still rely
  on empty-registry contradiction.

## Main Refactor

The remaining work is a theorem-shape refactor, not a local `StepFRApp` patch.

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

## Plan

1. **Make the step theorem registry-parametric.**

   Add a runtime registry parameter to `StepFR` and the single-run theorem
   families, or add parallel `WithRegistry` variants if that produces a smaller
   migration. Initial config literals in these definitions must include
   `registry := registry`.

   Done when recursive IHs can be applied to sub-runs whose starting configs
   carry the same registry, and the existing empty-registry theorem can be
   recovered by instantiating `registry := emptyExternRegistry`.

2. **Update all per-operator proof modules.**

   Thread the registry-parametric IHs through every `StepFR*` module. Most
   non-extern cases should be mechanical because `terminatesTo_preserves_registry`
   already proves evaluation preserves the registry.

   Replace uses of `config_eq_of_registry_default` only where they are used to
   force empty-registry configs for recursive calls.

   Done when `lake build LeanProofs` succeeds with the registry-parametric
   `StepFR` spine and no behavior change to the empty-registry theorem.

3. **Replace extern declaration vacuity.**

   In the top-level extern expression cases, use trusted-registry lookup plus
   `ExternBoundarySpec` declaration fields:

   - `declFR` for two-run `StepFR`;
   - `declSingle` for clean-pc single-run obligations;
   - `wf` for operational well-formedness consumers.

   Done when `externVal`, `externFn`, and `externPfn` cases no longer inspect
   `emptyExternRegistry` to prove contradiction.

4. **Switch application proofs to full app inversion.**

   In `StepFRApp.lean`, replace `terminatesTo_app_inv'` with
   `terminatesTo_app_inv_full` where populated registry support is needed.

   Keep the `Expr.toPExpr?` contradiction for user-pfn branches whose typed
   evidence is `peClosure_extern`; that argument is independent of the registry.

   Done when runtime `externFn` / `externPfn` branches are explicit proof cases
   rather than eliminated by empty-registry assumptions.

5. **Bridge closure-list membership to trusted entries.**

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

6. **Prove the populated-registry top-level theorem.**

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
