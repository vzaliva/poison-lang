# `stepFR_app` Proof Plan

Notes:
- This is the active forward plan for finishing `stepFR_app`.
- Historical checkpoints and discarded routes live in `doc/app-proof-history.md`.
- The focused memo for the framing problem is `doc/app-framing-proposal.md`.
- Avoid depending on line numbers; use lemma names and `rg`.

## Goal

Finish `stepFR_app` in `LeanProofs/StepFRApp.lean` with only the dependencies that are
actually needed for that proof.

Out of scope:

- `stepFR_ite_*`
- `stepFR_kwhile`
- unrelated proof cleanup

## Current State

What is done:

- the strengthened unary interface
  `PreservesInheritedCleanLocOneRun` /
  `PreservesInheritedCleanLocsOneRun`
  exists in `LeanProofs/StepFR.lean`
- the strengthened `StepFR_single_run` statement is in place
- the `parrow` location blocker is structurally solved
- the control-poison write semantics change is complete across spec, implementation, docs,
  proofs, and tests
- the typing-side `app` origin theorem
  `typecheckExpr_clean_lookup_origin_of_pc_true`
  now has its `app` branch proved

What is intentionally deferred:

- the `kwhile` branch inside
  `typecheckExpr_clean_lookup_origin_of_pc_true`
  is still `sorry`
- all `kwhile` proof work is permanently postponed from this plan

Build status:

- `make lean-build` passes
- remaining warnings are `sorry` warnings only

## Remaining Proof Debt For `stepFR_app`

To completely finish `stepFR_app`, the remaining work is:

1. close the `arrow` fallback branch in `stepFR_app`
   - this is the branch currently ending in the local existential pack `sorry`
   - current diagnosis: it still needs a reusable unary member-evidence / output-packaging
     fact, not more app-typing infrastructure

2. close the `parrow` dirty-internal fallback branch in `stepFR_app`
   - this currently has a direct `sorry`
   - current diagnosis: it likely needs the same dual-run body-IH packaging shape as the
     `arrow` fallback, so it should not be attacked independently first

3. prove the new unary conjunct in `StepFR_single_run`
   - `StepFR_single_run` still ends with `sorry` for
     `PreservesInheritedCleanLocsOneRun`
   - if the remaining `stepFR_app` fallback branches truly need this semantic fact, this is
     the main upstream dependency

4. remove the deferred `kwhile` theorem debt from the `stepFR_app` dependency cone
   - preferred route: split the current origin theorem or replace it with an app-specific
     helper that does not mention `kwhile`
   - do not prove `kwhile`; refactor around it instead

## Execution Order

The plan is ordered by risk. The first steps are meant to expose architectural problems
early, before paying for long local proofs.

1. classify the exact missing fact in the `arrow` fallback branch
   - work inside `stepFR_app`, not in generic infrastructure
   - goal:
     reduce the current fallback `sorry` to one precise reusable statement
   - success condition:
     either the branch closes locally, or the exact missing unary/output-pack fact is frozen

2. if Step 1 freezes a real unary/output-pack fact, prove that fact at the `StepFR` layer
   - target:
     the current `StepFR_single_run` conjunct or a tightly-related corollary
   - do not widen the interface again unless the current statement is provably insufficient
   - success condition:
     `StepFR_single_run` no longer contains the new conjunct `sorry`

3. return to the `arrow` fallback branch and finish it
   - use the proved unary fact instead of adding new app-local witness tricks
   - success condition:
     the existential output pack in the `arrow` case is closed

4. reuse the same pattern for the `parrow` dirty-internal fallback branch
   - only after the `arrow` fallback is understood
   - success condition:
     the remaining direct `sorry` in the `parrow` path is gone

5. cut `kwhile` out of the theorem dependency cone for `stepFR_app`
   - preferred route:
     split `typecheckExpr_clean_lookup_origin_of_pc_true` into an app-relevant helper that
     excludes `kwhile`
   - success condition:
     `stepFR_app` no longer depends on a theorem containing the deferred `kwhile` `sorry`

6. run full verification
   - `make lean-build`
   - reassess any remaining `sorry`s reachable from `stepFR_app`

## Design Rules

- Keep this plan focused on finishing `stepFR_app`, not on generic cleanup.
- Prefer proving one reusable semantic fact over duplicating app-local witness arguments in
  both `arrow` and `parrow`.
- Do not reopen the control-poison typing redesign unless a new contradiction appears.
- Do not spend proof effort on `kwhile`.

## Stop / Reassess Conditions

- If the `arrow` fallback branch cannot be reduced to a single precise missing fact, stop
  and restate the obstruction before more proof work.
- If finishing the current unary fact would require widening the `StepFR` interface again,
  stop and justify that redesign explicitly.
- If `stepFR_app` still depends on `kwhile` after attempted theorem factoring, keep the
  `kwhile` proofs postponed and split the dependency instead of proving them.

## Working Set

Primary files:

- `LeanProofs/StepFRApp.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/TypeSafety.lean`

Current key lemmas:

- `stepFR_app`
- `StepFR_single_run`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- `typecheckExpr_lookup_clean_back_of_pc_true`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1_true`
