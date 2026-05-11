# Probe 2 Plan: Registry-Aware Extern Boundaries

## Objective

Complete the proof-side bridge from the current empty-registry fault-robustness
theorem to a registry-aware extern-boundary theorem.

This is the Probe 2 sub-task of `doc/ffi-axioms.md`.  It is about consuming
trusted boundary evidence in the proof stack.  Reusable concrete driver
constructors such as `ExternBoundarySpec.pureUnaryCleanInt` are intentionally
left to the next high-level probe.

The staging target is a relative theorem:

```lean
TypeSystemEnforcesFaultRobustness_spec_with_registry
  (TrustedRegistry.toRuntimeRegistry tr) e s obs
```

under explicit trusted-registry agreement hypotheses.  The final public API
target is `TypeSystemEnforcesFaultRobustness`: it should take the non-empty
runtime registry / trusted-registry proof obligations rather than leaving the
populated theorem as a parallel endpoint.  Compatibility theorems recover the
old empty-registry formulation as corollaries.  Successful extern declarations
and extern calls should be justified by `ExternBoundarySpec` evidence instead
of by the current empty-registry vacuity arguments.

No new `sorry` or `axiom` is acceptable.

## Current Status

The registry-parametric proof spine exists and compiles.  All extern app-call
and declaration branches consume provider hypotheses; the empty-registry
contradiction discharges have been removed from `stepFR_app` and from the
declaration top-level branches.

The public populated-registry theorem `TypeSystemEnforcesFaultRobustness` is in
place.  It proves

```lean
TypeSystemEnforcesFaultRobustness_spec_with_registry
  (TrustedRegistry.toRuntimeRegistry tr) e s obs
```

from `TrustedRegistryAgreesWithProgram e tr` plus
`TrustedRegistryAppClosureProvenance e tr`.  The original empty-registry
public statement is preserved as `TypeSystemEnforcesFaultRobustness_emptySpec`,
and `TypeSystemEnforcesFaultRobustness_emptyRegistry` proves the
registry-relative empty instance.

Shape of the current state:

- `StepFR*`, `StepFRSingleRunFinalCleanPcTrue*`, and the masked single-run
  cores are registry-parametric.  Recursive calls use registry-preservation
  facts, not `emptyExternRegistry`.
- The provider-parametric proof cores (`_with_contracts`,
  `_with_contracts_canUse`, `_with_contracts_for`) thread declaration and
  app-call providers as hypotheses.  Empty-registry public wrappers
  instantiate the providers via `.of_emptyExternRegistry`.
- Root-aware declaration provenance is threaded through the step core via
  `CanUse := ExternDeclLift root`.  Closure-body recursive calls in
  `StepFRApp` consume explicit body-provenance hooks
  (`hcanFnBody` / `hcanPfnBody`).
- `TrustedRegistryAppClosureProvenance` is typing-indexed (fields are gated by
  `AppFnClosureListFromTypecheck` / `AppPfnClosureListFromTypecheck` witnesses)
  and produces `ExternDeclarationInProgram root` facts rather than
  registry-wide closure-list coverage.  Populated app-call providers compose
  this with the actual successful runtime lookup and
  `TrustedRegistryAgreesWithProgram`.
- All six app-call branch finishers
  (`finish_user_extern_p1p_true`, `finish_extern_user_p1p_true`,
  `finish_extern_extern_p1p_true`, `finish_user_pfn_extern_pfn_p1p_true`,
  `finish_extern_pfn_user_pfn_p1p_true`, and
  `finish_extern_pfn_extern_pfn_p1p_true`) build or consume body-local extern
  boundary posts and transport them back to the final app post.

Verification baseline:

- `lake build LeanProofs` succeeds.
- `make test` passes 96/96.
- `git diff --check` is clean.
- `scripts/sorry-count.py --no-build` reports no `sorry` / `axiom` delta.
  Existing `sorry` warnings in `LeanProofs/SemanticsProperties.lean` remain
  pre-existing.

## Active Blocker

The remaining proof work is to derive `TrustedRegistryAppClosureProvenance e tr`
from typed closure-list construction rather than asking callers to supply it.
**This derivation is false under the current public spec.**

`TypeSystemEnforcesFaultRobustness_spec_with_registry` quantifies over any
initial `ctx` matching the input spec.  `wfInputSpec` makes listed input
variables first-order, but `ctxMatchesInputSpec` does not forbid additional
function-typed variables in `ctx.varEnv`.  Therefore an app whose function
expression is a variable can obtain its typed closure list from the initial
context rather than from syntax under the root expression.

Counterexample:

```lean
root := Expr.app (Expr.var "f") (Expr.num 1)
body := Expr.seq
  (Expr.externVal 41 Typ.int false SyntaxPredicate.noPred)
  (Expr.num 0)
ctx.varEnv["f"] :=
  { etyp := ETyp.arrow Typ.int Typ.int false
      [FnTClosure.regular "x" body []],
    poison := false, pred := Predicate.noPred }
```

`typecheck ctx root fuel` succeeds and its `AppFnClosureListFromTypecheck`
witness contains `FnTClosure.regular "x" body []`.  However
`ExternDeclLift root body` is false: `body` contains extern declaration `41`
and `root` contains no extern declaration syntactically.  So the `fnBody`
field of `TrustedRegistryAppClosureProvenance root tr` cannot be derived from
root typechecking and `TrustedRegistryAgreesWithProgram root tr` alone.

Three sound options:

1. **First-order initial context.**  Strengthen the public spec/context
   well-formedness so every initial `ctx.varEnv` binding is first-order, or at
   least every function-typed closure in the initial context is excluded.
   Closest to the existing `wfInputSpec` first-order design; changes the
   `ctxMatchesInputSpec` surface.
2. **Initial-context closure provenance premise.**  Keep the current context
   generality, but add a premise that every closure body and extern member
   stored in `ctx.varEnv` is lifted to the trusted root/program set.
   Replaces `TrustedRegistryAppClosureProvenance` with a more local and
   honest initial-context provenance premise.
3. **Extend the trusted-program surface.**  Extend `ExternDeclarationInProgram`
   so the trusted "program" includes initial closure bodies, not only the root
   expression syntax.  Broader; should be treated as a language/spec design
   change.

Option 1 aligns with the existing first-order input-spec design and is the
default direction unless option 2 is needed for downstream callers.

## Remaining Plan

Steps 1–5 are complete; see History for narratives.

### 6. Generalize the step theorem and bridge trusted agreement — Active

The step proof core is provider-parametric, root-aware, and the public
populated-registry theorem `TypeSystemEnforcesFaultRobustness` is in place.
`TrustedRegistryAppClosureProvenance` is typing-indexed and produces
program-membership evidence.  Remaining work:

1. Resolve the initial-context spec blocker per one of the three options
   above.
2. Prove typed closure-list provenance lemmas, or prove the existing
   typechecking data already implies the needed
   `TrustedRegistryAppClosureProvenance` fields:
   - every regular closure body in the list has an
     `ExternDeclLift root body` witness;
   - every extern closure member, and every regular extern-body member, has
     precise root-program declaration membership evidence.
3. Prove the provenance predicate is produced/preserved by typechecking for
   arrow/parrow closure lists and transported through the app
   `apply*Closure` / join machinery.
4. Reduce the public assumptions so the final public theorem no longer
   exposes `TrustedRegistryAppClosureProvenance e tr`.  The exact final
   assumption shape depends on which Active Blocker option is chosen:
   - **Under Option 1 (first-order initial context):** callers supply only
     the populated runtime/trusted registry obligations
     (`TrustedRegistryAgreesWithProgram e tr`).  App-call provenance is
     derived internally from typing facts plus the strengthened
     `ctxMatchesInputSpec`.
   - **Under Option 2 (initial-context closure provenance premise):**
     callers additionally supply a local initial-context closure provenance
     premise stating that closure bodies and extern members stored in the
     initial `ctx.varEnv` lift to the trusted root/program set.  This is
     a narrower premise than the current `TrustedRegistryAppClosureProvenance`,
     and the rest of the app-call provenance is still derived internally
     from typing facts.
   - **Under Option 3 (extend trusted-program surface):** the public
     assumptions match Option 1 in shape, but the meaning of "in the
     program" widens to include initial closure bodies — a language/spec
     design change rather than a proof-side change.
   In all cases, the old empty-registry theorem is retained as a
   compatibility corollary.

### 7. Preserve compatibility and verify

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
- `TrustedRegistryAppClosureProvenance` is not exposed as a final public
  theorem premise.  If the structure remains internally, its closure-list
  fields are indexed by actual typechecking provenance rather than
  universally quantified over arbitrary `tcls`.

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
  for clean effect-written memory locations.  In that shape the proof lacks
  the pre-state agreement needed for final clean memory agreement; fix the
  app-level extern effect pc first.
- Stop if the masked single-run theorem cannot supply ordinary
  `regimeConsistentWithCtx` to `ExternBoundarySpec.callSingle` and the only
  alternative is to silently assume ordinary tag-env consistency for masked
  tags.
- Stop if the `Expr.externFn` / `Expr.externPfn` declaration step proofs
  cannot construct `closureCapturedVarsRegime` and clean extern closure
  agreement from typing-side facts and trusted-registry lookup alone, without
  circular dependence on `ExternBoundarySpec`.

## History

### Design notes

- **Extern boundary is body-local, not app-final.**  The
  `ExternBoundarySpec.callFR` / `callSingle` posts justify only the body-level
  call result.  The surrounding application proof owns
  `applyFnTClosure` / `applyPFnTClosure` transport, provenance normalization,
  `joinTypeResults`, and final app-config restoration.  Changing
  `ExternBoundarySpec.callFR` to return an outer app post would push
  app-specific reasoning into every concrete extern boundary and is rejected.

- **`callConfig` vs `bodyConfig` separation.**  A single config cannot serve
  both as the runtime extern dispatch config and as the body-local proof
  input config.  Runtime extern dispatch must preserve the caller environment
  in the actual app output, while the boundary post must be over the closure
  environment extended with the argument.  The boundary layer exposes
  `bodyConfig` / `bodyOutputConfig` so app transport can restore the caller
  configuration after consuming a body-local post.

- **Two trusted lookup paths for runtime `externFn` dispatch.**  Runtime
  `externFn` dispatch is not forced to originate from a `FnTClosure.extern`
  member.  It can also arise from a regular closure whose body AST is
  `Expr.externFn ...`, because runtime app dispatch matches on the closure
  body.  Both paths now resolve uniformly through typed program-membership
  provenance plus the actual successful runtime lookup and
  `TrustedRegistryAgreesWithProgram`.  The structural distinction is only
  in how the `ExternDeclarationInProgram root id _` evidence is obtained at
  the closure-list level:
  - direct `FnTClosure.extern` / `PFnTClosure.extern` membership uses the
    `fnExternMember` / `pfnExternMember` fields of
    `TrustedRegistryAppClosureProvenance`;
  - regular closures with an extern body AST use the
    `fnRegularExternBody` / `pfnRegularExternBody` fields.

  The closure-list-wide agreement predicates
  (`TrustedRegistryAgreesWithFnTClosures` /
  `TrustedRegistryAgreesWithPFnTClosures`) are no longer the load-bearing
  app-side API; they were the rejected universal-over-`tcls` shape, kept
  only as helpers internally.

- **Provider-parametric proof core.**  The step and single-run cores are
  parameterized over provider hypotheses rather than calling registry-specific
  lemmas directly.  Empty-registry public wrappers instantiate providers via
  `.of_emptyExternRegistry`; trusted-registry wrappers instantiate via
  `_trustedRegistry` adapters.  Adding new instantiations (e.g. for a future
  third registry shape) is a matter of supplying new provider instances, not
  reshaping the proof core.

- **`TrustedRegistryAppClosureProvenance` is staging, not final API.**  The
  acceptance criterion forbids exposing it as a final public theorem premise.
  The structure may persist internally if its closure-list fields remain
  indexed by actual typechecking provenance.

### Resolved blockers and lessons

#### Masked single-run app spine: `MaskedTagsAbsentFromTrueTagEnv` (Step 1)

Making `stepFRSingleRunFinalCleanPcTrue_app_*_parametric_maskedReg` arbitrary
in `registry` exposed a mismatch between the masked induction theorem and the
extern boundary API:

- `StepFRSingleRunFinalCleanPcTrueMaskedRegParam` is deliberately generic over
  `CtxCons` / `ValCons` and assumes only
  `regimeConsistentWithCtxMasked masked ctx`.
- `ExternBoundarySpec.callSingle` requires ordinary
  `regimeConsistentWithCtx bodyCtx` and ordinary
  `consistentWithRegime ... bodyCtx ...`.
- The existing unmasking lemmas recover ordinary value/context consistency
  from masked consistency plus `∀ k, masked k → R.lookup? k = none`, but they
  do not recover ordinary tag-env consistency.  A masked tag-env entry may be
  accepted precisely because it is masked while its regime lookup is `none`.

Resolved by adding `MaskedTagsAbsentFromTrueTagEnv`:

```lean
MaskedTagsAbsentFromTrueTagEnv masked ctx :=
  ∀ k deps, masked k → ctx.tagEnv.get? k = some ⟨true, deps⟩ → False
```

Together with `regimeConsistentWithCtxMasked masked ctx`, this proves
ordinary `regimeConsistentWithCtx ctx`.  The initial false mask satisfies the
invariant; `typecheck` preservation threads it through `ctxAfter`,
`tagEnv.insert ... false` preserves it immediately, and
`tagEnv.insert ... true` is discharged by contradicting `hmasked_none`.

The invariant is threaded through
`StepFRSingleRunFinalCleanPcTrueMaskedRegParam`, its IH, the per-operator
masked single-run lemmas, and the high-risk `ite`, assignment, and app
body-context paths.

#### Why option 2 (ordinary-induction split) was not pursued (Step 2)

The current non-masked single-run theorem is not an independent case split:
it is a wrapper around
`TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked` with
`masked := fun _ => False`, followed by unmasking the final post.  The app
case is owned by the masked induction:

```
TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue
  -> TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked
  -> stepFRSingleRunFinalCleanPcTrue_app_maskedReg
  -> stepFRSingleRunFinalCleanPcTrue_app_*_parametric_maskedReg
```

App expressions are reachable from genuinely masked recursive calls.  For
example, the masked `ite` proof calls its recursive IH under branch contexts
such as `ctxTrue`; if that branch expression is an app, the app proof is
reached inside the masked spine rather than at the outer false-mask wrapper.
Therefore successful extern-call boundary consumption cannot simply be hooked
at the outer non-masked theorem without a much larger direct ordinary
single-run induction.  Option 1 (the invariant above) was the cheap local
bridge; option 2 was deemed unnecessary.

#### `TrustedRegistryAppClosureProvenance` precision evolution

The provenance structure has been tightened twice; both intermediate shapes
were rejected as final API:

1. **Universal-over-`tcls` (rejected).**  Fields universally quantified over
   `tcls : List FnTClosure` without typing witnesses.  Effectively unprovable
   for finite trusted registries, because an arbitrary closure list can
   mention arbitrary extern ids.
2. **Typing-indexed.**  Fields gated by `AppFnClosureListFromTypecheck` /
   `AppPfnClosureListFromTypecheck` witnesses, so `tcls` is constrained to
   the typechecker output at a reachable app site.
3. **Program-membership.**  The closure-list-wide `fnClosures` /
   `pfnClosures` fields were removed.  The structure now produces
   `ExternDeclarationInProgram root id _` per extern closure member, and the
   populated providers compose that with the actual successful runtime lookup
   and `TrustedRegistryAgreesWithProgram root tr` to recover trusted boundary
   evidence.

Step 6 will replace this with internally derived provenance once the
initial-context spec blocker (see Active Blocker) is resolved.

### Completed milestones

- **Step 1** — Masked true-tag absence invariant
  (`MaskedTagsAbsentFromTrueTagEnv`) threaded through the masked single-run
  spine.
- **Step 2** — Option 2 ordinary-induction split investigated and deemed
  unnecessary.
- **Step 3** — App transport helpers validated on regular user-closure
  branches.
- **Step 4** — Extern call boundaries consumed in `StepFRApp` for all six
  app-call branch combinations; `hregistry_empty` removed from `stepFR_app`;
  `applyFnTClosure` extern-effect pc fixed to use app-body pc instead of
  caller `ctx.pc`.
- **Step 5** — Declaration adapters replaced with populated-registry
  consumers (`declFR`, `declSingle`).  Trusted-registry adapters
  (`ExternDeclBoundarySingleMaskedContract.of_trustedRegistry`,
  `ExternDeclBoundaryFRContract.of_trustedRegistry`) added.  No separate
  `ExternBoundarySpec.wf` consumer was needed in the step proof; the
  declaration posts returned by `declFR` / `declSingle` already carry the
  required output `wfConfig` facts.
- **Public populated theorem** — `TypeSystemEnforcesFaultRobustness` exposed
  as the registry-aware top-level theorem.  Original empty-registry public
  statement preserved as `TypeSystemEnforcesFaultRobustness_emptySpec`.
