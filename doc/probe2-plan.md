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

from the context-indexed reachable-domain premise

```lean
∀ {ctx : TypeContext},
  ctxMatchesInputSpec s ctx →
  TrustedRegistryAgreesWithReachable e ctx tr
```

The public theorem no longer exposes `TrustedRegistryAppClosureProvenance`.
The original empty-registry public statement is preserved as
`TypeSystemEnforcesFaultRobustness_emptySpec`, and
`TypeSystemEnforcesFaultRobustness_emptyRegistry` proves the registry-relative
empty instance.

Shape of the current state:

- `StepFR*`, `StepFRSingleRunFinalCleanPcTrue*`, and the masked single-run
  cores are registry-parametric.  Recursive calls use registry-preservation
  facts, not `emptyExternRegistry`.
- The provider-parametric proof cores (`_with_contracts`,
  `_with_contracts_canUse`, `_with_contracts_for`) thread declaration and
  app-call providers as hypotheses.  Empty-registry public wrappers
  instantiate the providers via `.of_emptyExternRegistry`.
- Root-aware declaration provenance is threaded through the step core via the
  abstract `CanUse` interface.  Legacy wrappers instantiate it with
  `ExternDeclLift root`; the reachable theorem instantiates it with
  `ExternDeclarationReachableFromExpr root ctxRoot`.  Closure-body recursive
  calls in `StepFRApp` consume explicit body-provenance hooks
  (`hcanFnBody` / `hcanPfnBody`).
- The reachable-context proof path derives app-call providers from
  `TrustedRegistryAgreesWithReachable root ctxRoot tr`, typechecking evidence,
  and `QTypReachableFrom.of_typecheck`.  `TrustedRegistryAppClosureProvenance`
  remains only as legacy/internal staging surface.
- All six app-call branch finishers
  (`finish_user_extern_p1p_true`, `finish_extern_user_p1p_true`,
  `finish_extern_extern_p1p_true`, `finish_user_pfn_extern_pfn_p1p_true`,
  `finish_extern_pfn_user_pfn_p1p_true`, and
  `finish_extern_pfn_extern_pfn_p1p_true`) build or consume body-local extern
  boundary posts and transport them back to the final app post.

Verification baseline:

- `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeds
  after the reachable-domain theorem cutover.
- Full post-cutover verification succeeds: `lake build LeanProofs`, `make test`
  passes 96/96, `git diff --check` is clean, and
  `scripts/sorry-count.py --no-build` reports no `sorry` / `axiom` delta.
  Existing `sorry` warnings in `LeanProofs/SemanticsProperties.lean` remain
  pre-existing.

## Resolved Trust-Domain Blocker

The Step 6 public-theorem cutover derives app-call provider evidence from the
reachable initial typed configuration rather than asking callers to supply
`TrustedRegistryAppClosureProvenance e tr`.  The original attempt to derive
that provenance from AST-only trust was false under the old public spec.

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

Chosen direction: trust should range over extern declarations reachable from
the initial typed configuration, not only over declarations syntactically in
the root expression.  This is a proof/spec trust-domain extension, not a
language semantics change: evaluation and typechecking are unchanged.

Add a reachable-extern predicate alongside the existing AST-only
`ExternDeclarationInProgram`, rather than overloading that name:

```lean
ExternDeclarationReachableFromContext root ctx id d
```

The intended domain is:

- extern declarations in `root`'s AST, using the existing
  `ExternDeclarationInProgram root id d`;
- extern declarations in every regular closure body listed in function or
  pfunction closure lists in `ctx.varEnv`;
- direct extern closure members in those closure lists;
- extern declarations in captured type environments of those closure members,
  recursively;
- nested extern returns inside `ExternReturn`.

The populated theorem now requires trusted agreement for this reachable domain
at each initial context:

```lean
TrustedRegistryAgreesWithReachable root ctx tr
```

The important point is that `ctx` must be in scope; `root` alone cannot
determine hidden initial closure bodies.  With that premise, app-call provider
facts are internally derived from typechecking facts and reachable-extern
trust; `TrustedRegistryAppClosureProvenance` does not remain in the public
API.

Implemented direction: keep `CanUse : Expr → Prop` focused on syntactic root
reachability, and thread only a context monotonicity invariant through the
proof spine:

```lean
ContextReachableFrom root ctxRoot ctx
```

This invariant means every closure-bearing qualified type in `ctx.varEnv`,
including nested closure lists and captured type environments, is covered by
the initial `(root, ctxRoot)` reachable trust domain.  Do **not** widen
`CanUse` to `CanUse ctx e` unless this monotonicity route fails.

`QTypReachableFrom` is not threaded as a separate invariant.  It is treated as
the postcondition of an on-demand preservation lemma:

```lean
ContextReachableFrom root ctxRoot ctx →
CanUse e →
typecheck ctx e fuel = .ok res →
QTypReachableFrom root ctxRoot res.qualType
```

At app-provider use sites, the reachable proof path applies this lemma to the
`typecheck` evidence inside `AppFnClosureListFromTypecheck` /
`AppPfnClosureListFromTypecheck`, then uses extraction lemmas from
`QTypReachableFrom` to obtain the exact reachable declarations needed for
extern members and regular extern-body members.

This factoring handles both sources of app closure lists: those inherited from
`ctx.varEnv` and those produced by typechecking root subexpressions.  The
load-bearing preservation cases are variable lookup, `fn` / `pfn`, extern
callable declarations, `app` / `apply*Closure`, and `ite` / `joinTypeResults`.
Most other expression forms are closure-provenance no-ops.  The
`joinTypeResults` and app-threading cases are covered by the qtype/member-level
reachability helpers in `ExternBoundary.lean`.

## Remaining Plan

Steps 1–7 are complete; see History for narratives.

### 6. Generalize the step theorem and bridge trusted agreement — Complete

The step proof core is provider-parametric, root-aware, and the public
populated-registry theorem `TypeSystemEnforcesFaultRobustness` is in place.
The reachable-domain bridge is implemented:

- `ExternDeclarationReachableFromContext root ctx id d` and
  `TrustedRegistryAgreesWithReachable root ctx tr` define the reachable trust
  domain while preserving `ExternDeclarationInProgram` as the AST-only
  component.
- `ContextReachableFrom root ctxRoot ctx` is threaded through the reachable
  step theorem as the monotonicity invariant over typed contexts.
- `QTypReachableFrom root ctxRoot qt` is used as a lemma-level postcondition,
  not as a threaded spine invariant.  Extraction lemmas cover the reachable
  declarations needed by app providers:
   - regular closure bodies;
   - direct extern closure members;
   - regular extern-body members;
   - nested extern returns;
   - captured type environments.
- `QTypReachableFrom.of_typecheck` proves on-demand typecheck preservation for
  closure provenance, including the `var`, `fn`, `pfn`, `externFn`,
  `externPfn`, `app`, and `ite`/join cases.
- App-call providers in the reachable proof path are derived from
  `TrustedRegistryAgreesWithReachable root ctxRoot tr`, typechecking facts,
  and the reachable qtype extraction lemmas.
- The final public theorem no longer exposes
  `TrustedRegistryAppClosureProvenance e tr`.  Its trusted premise is the
  context-indexed reachable-domain agreement over every initial context
  admitted by the input spec, and the old empty-registry theorem remains the
  compatibility corollary.

### 7. Preserve compatibility and verify — Complete

`TypeSystemEnforcesFaultRobustness_emptyRegistry` is preserved as the
compatibility corollary.  `lake build LeanProofs`, `make test`,
`git diff --check`, and `scripts/sorry-count.py --no-build` all pass.

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
  cannot be stated without weakening reachable-domain trust into a vague
  global assumption.
- Stop if a regular `FnTClosure.regular x (Expr.externFn ...) ...` runtime
  dispatch cannot be tied either to reachable trusted agreement or to a precise
  typed-closure provenance premise.
- Stop if tying regular extern-body closure membership to trusted lookup
  requires weakening reachable-domain trust into a global "all extern ids are
  trusted" premise instead of adding a precise provenance invariant.
- Stop if the reachable-extern trust domain cannot be stated with the initial
  `ctx` in scope and must instead quantify over arbitrary hidden closure
  bodies independent of the initial context.
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
  body.  Both paths now resolve uniformly through typed closure/source
  provenance, the actual successful runtime lookup, and
  `TrustedRegistryAgreesWithReachable`.  The structural distinction is only
  in how reachable declaration evidence is obtained at the closure-list level:
  direct `FnTClosure.extern` / `PFnTClosure.extern` membership is extracted
  from the closure member itself, while regular closures with an extern body
  AST use body-source provenance from typechecking and `QTypReachableFrom`.

  The closure-list-wide agreement predicates
  (`TrustedRegistryAgreesWithFnTClosures` /
  `TrustedRegistryAgreesWithPFnTClosures`) are no longer the load-bearing
  app-side API; they were the rejected universal-over-`tcls` shape, kept
  only as helpers internally.

- **Provider-parametric proof core.**  The step and single-run cores are
  parameterized over provider hypotheses rather than calling registry-specific
  lemmas directly.  Empty-registry public wrappers instantiate providers via
  `.of_emptyExternRegistry`; trusted-registry wrappers instantiate via
  reachable-context adapters.  Adding new instantiations (e.g. for a future
  third registry shape) is a matter of supplying new provider instances, not
  reshaping the proof core.

- **`TrustedRegistryAppClosureProvenance` is staging, not final API.**  The
  acceptance criterion forbids exposing it as a final public theorem premise.
  The structure persists only as legacy/internal surface; the public theorem
  uses reachable-domain trust directly.

- **Extern ids are tracked literals.**  Runtime extern dispatch can only use
  ids that came from source `Expr.externVal` / `Expr.externFn` /
  `Expr.externPfn` declarations or from `FnTClosure.extern` /
  `PFnTClosure.extern` members already present in typed closure data.  The
  typechecker transports, combines, and exposes those ids through var lookup,
  closure capture, `apply*Closure`, nested returns, and joins; it does not
  synthesize a third source of ids.  This is the structural reason the final
  trust premise can be a single configuration-wide reachable-domain statement
  over `(root, ctxRoot)` rather than a global "all ids are trusted" premise.

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
   `pfnClosures` fields were removed.  The structure produced
   `ExternDeclarationInProgram root id _` per extern closure member, and the
   populated providers composed that with the actual successful runtime lookup
   and `TrustedRegistryAgreesWithProgram root tr` to recover trusted boundary
   evidence.
4. **Reachable-domain trust.**  Step 6 replaced the public provenance premise
   with internally derived provider evidence from
   `TrustedRegistryAgreesWithReachable root ctxRoot tr`,
   `ContextReachableFrom`, and `QTypReachableFrom.of_typecheck`.  This covers
   externs in initial-context closure data as well as root AST externs.

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
- **Step 6** — Reachable-domain trust added for the initial typed
  configuration.  `ContextReachableFrom` is threaded through the reachable
  proof path, `QTypReachableFrom.of_typecheck` supplies on-demand closure
  provenance, and app extern providers are derived from
  `TrustedRegistryAgreesWithReachable`.  The public populated theorem no
  longer exposes `TrustedRegistryAppClosureProvenance`.
- **Step 7** — Compatibility and verification completed:
  `TypeSystemEnforcesFaultRobustness_emptyRegistry` still compiles,
  `lake build LeanProofs` succeeds, `make test` passes 96/96,
  `git diff --check` is clean, and `scripts/sorry-count.py --no-build` reports
  no `sorry` / `axiom` delta.
- **Public populated theorem** — `TypeSystemEnforcesFaultRobustness` exposed
  as the registry-aware top-level theorem.  Original empty-registry public
  statement preserved as `TypeSystemEnforcesFaultRobustness_emptySpec`.
