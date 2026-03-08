# `stepFR_app` Proof Plan

Notes:
- This is the active forward plan for finishing `stepFR_app`.
- Historical checkpoints and discarded routes live in `doc/app-proof-history.md`.
- The focused memo for the framing problem is `doc/app-framing-proposal.md`.
- Keep this file concrete: current state, next steps, and stop conditions.
- Avoid depending on line numbers; use lemma names and `rg`.

## Goal

Finish `stepFR_app` in `LeanProofs/StepFRApp.lean` with only the dependencies that are
actually needed for that proof.

Out of scope:

- `stepFR_ite_*`
- all `kwhile` proof work
- unrelated proof cleanup

External constraint:

- there is a separate known type-system / regime-handling blocker that currently prevents
  `stepFR_ite_*` from being proved
- that work is tracked in GitHub issue `#128`
- that work is owned in another branch
- therefore the app plan must not depend on finishing `ite` now
- however, the app-side narrowing should stay compatible with a later `ite` proof once
  that external blocker is fixed

## Current State

What is done:

- the local `arrow` fallback packaging in `stepFR_app` is closed
- the local `parrow` dirty-internal fallback packaging in `stepFR_app` is closed
- `StepFR_single_run_core` now exists in `LeanProofs/StepFR.lean`
  and isolates the sound unary extraction payload from the unsound preservation add-on
- generic one-run composition now exists for
  `PreservesInheritedCleanLocOneRun.trans`
- generic final-clean composition now exists for
  `PreservesInheritedFinalCleanLocsOneRun.compose`
- the control-poison write semantics change is complete across spec, implementation, docs,
  proofs, and tests
- the app-specific uses of
  `typecheckExpr_clean_lookup_origin_of_pc_true`
  are in place and the `app` branch of that theorem is proved
- the risky `assign` semantics are now factored enough to support the unary plan:
  `typecheckAssign_result2_lookup_clean_back_of_pc_true`,
  `assign_write_step_preserves_inherited_final_clean_pc_true`, and
  `assign_final_clean_preservation`
  all compile
- the unary theorem work is no longer just a definition shell:
  the following case lemmas now compile in `LeanProofs/FaultRobustnessProofs.lean`:
  `stepFRSingleRunFinalCleanPcTrue_literal`,
  `stepFRSingleRunFinalCleanPcTrue_assign`,
  `stepFRSingleRunFinalCleanPcTrue_seq`,
  `stepFRSingleRunFinalCleanPcTrue_unaryop`,
  `stepFRSingleRunFinalCleanPcTrue_op`,
  `stepFRSingleRunFinalCleanPcTrue_fn`,
  `stepFRSingleRunFinalCleanPcTrue_pfn`,
  `stepFRSingleRunFinalCleanPcTrue_var`,
  and `stepFRSingleRunFinalCleanPcTrue_newRef`
- the branch-join side of the unary `ite` route is now factored enough to classify the
  current failure mode:
  `joinMemEnvsStrong_lookup_cleanUnder_left_of_contains` and
  `joinMemEnvsStrong_lookup_cleanUnder_right_of_contains`
  now compile and isolate the actual-branch clean extraction step
- that route is now considered rejected for the app effort:
  the conservative `ite` modes expose a theorem-shape problem, and `stepFR_ite_*` is both
  out of scope and independently blocked elsewhere

What still contains `sorry` on the app path:

- `StepFR_single_run`
  still ends with `sorry` for the old direct single-run wrapper path
- the induction-side companion theorem
  `StepFRSingleRunFinalCleanPcTrue`
  is now defined, but not yet proved or threaded into the app body IH
- `stepFR_app` still uses the current `StepFR_single_run` witness in the narrowed
  inherited-location `arrow` / `parrow` fallback subproofs because the companion unary
  theorem has not yet been threaded through the global induction
- `typecheckExpr_clean_lookup_origin_of_pc_true`
  still has the permanently-postponed `kwhile` branch

Build status:

- full `make lean-build` passes
- remaining warnings are `sorry` warnings only

## Main Blocker

Short version:

- `stepFR_app` needs a one-run witness for body executions under `pc = true`
- that witness must carry `PreservesInheritedFinalCleanLocsOneRun` for the same chosen
  post-run realization map `θ'`
- `StepFR_single_run_core` is too weak because it does not provide that preservation fact
- the current `StepFRSingleRunFinalCleanPcTrue` route is too broad because it still drags
  in extra post-context obligations and, in practice, pulls `ite` into the dependency cone
- closure bodies can themselves be `ite`, so this cannot be solved by assuming the app
  fallback only sees non-`ite` bodies

Planning consequence:

- replace `StepFRSingleRunFinalCleanPcTrue` in place with a narrower app-focused statement
- keep only the witness payload that `stepFR_app` actually consumes
- reuse the existing strong-induction scaffolding for that theorem
- do not take on new `ite` proof work in this branch; leave `ite` deferred under issue
  `#128` and `kwhile` permanently deferred
- if a theorem shape still requires extra joined-post-context obligations from `ite`,
  reject that shape and refactor again

For the detailed technical discussion, see `doc/app-framing-proposal.md`.

## Remaining Work For `stepFR_app`

1. split the unary route into an app-focused theorem surface
   - keep `StepFR` unchanged
   - do not revive the old `StepFR_single_run` wrapper
   - do the refactor in place: replace the current broad
     `StepFRSingleRunFinalCleanPcTrue` route rather than moving it to a separate legacy
     file
   - keep the same theorem name: replace `StepFRSingleRunFinalCleanPcTrue` in place with
     the narrower app-focused statement instead of adding a sibling theorem
   - introduce or prioritize a theorem whose critical output is:
     a chosen `θ'` together with `PreservesInheritedFinalCleanLocsOneRun`
   - keep any extra witness obligations minimal and justified by actual `stepFR_app` use
   - feasibility check:
     the narrowed theorem must avoid `ite` as an upstream proof obligation even though
     closure bodies may themselves be `ite`
   - concrete mechanism:
     reuse the current `StepFRSingleRunFinalCleanPcTrue` strong-induction route, but with
     the narrowed payload; do not attempt to solve `ite` in this branch, and keep the
     theorem shape compatible with later completion of the deferred `ite` branches

2. finish the constructor coverage needed for that narrower unary theorem
   - already covered:
     literals, `assign`, `seq`, `unaryop`, `op`, `fn`, `pfn`, `var`, `newRef`
   - still needed on the app path:
     `deref` and `vlet`
   - if a theorem shape still requires extra `ite` packaging, split the theorem again
     instead of proving `ite`
   - leave `kwhile` out of scope

3. package the covered constructor lemmas into the strong-induction theorem
   - do this for the narrowed unary theorem only
   - only widen back out later if a real downstream need appears
   - update the IH helpers in `StepFR.lean` to match the narrowed statement
   - make the threading path explicit before rewiring `stepFR_app`
   - in this branch, accept deferred `ite` and `kwhile` branches in that theorem; the
     goal is to get the theorem boundary and non-`ite` cases right for `stepFR_app`

4. update the `arrow` and `parrow` body-IH use sites in `stepFR_app`
   - stop depending on the current `StepFR_single_run` wrapper in the different-body
     fallback subproofs
   - switch those sites to the companion unary IH theorem
   - do this as soon as the theorem is available for the body forms used by `app`

5. remove the deferred `kwhile` theorem from the `stepFR_app` dependency cone
   - preferred route:
     split the app-consumed theorem surface so the body-IH theorem and the clean-origin
     theorem each have an app-relevant form that excludes `kwhile`
   - keep this split compatible with step 1, so the unary redesign does not need to be
     redone after the `kwhile` cut
   - do not prove `kwhile`

6. run full verification
   - `make lean-build`
   - reassess remaining `sorry`s reachable from `stepFR_app`

## Execution Order

1. narrow the unary theorem surface to the app-relevant preservation payload
   - success condition:
     `stepFR_app` no longer requires any new `ite` proof work on this branch

2. finish the remaining constructor cases on that narrowed theorem
   - success condition:
     `deref` and `vlet` no longer block the body-IH route

3. thread the narrowed companion unary IH through the strong induction theorem
   - success condition:
     `stepFR_app` can obtain body single-run preservation from the body IH without
     changing `StepFR`

4. rewire `stepFR_app` to consume that narrower theorem
   - success condition:
     the current `hpres₀` / `hpres₁` uses are replaced with the new theorem

5. cut `kwhile` out of the dependency cone
   - success condition:
     `stepFR_app` no longer depends on a theorem containing the deferred `kwhile` `sorry`

6. run full verification

## Design Rules

- Do not try to prove `PreservesInheritedCleanLocsOneRun` as currently stated for arbitrary
  impure bodies.
- Keep the replacement fact as narrow as possible and shaped by the current app use sites.
- If a unary theorem case stalls on joined-post-context obligations that `stepFR_app`
  never consumes, split the theorem before investing in those obligations.
- If a unary theorem route drags `ite` into the dependency cone, reject that route and
  refactor the theorem boundary instead of proving `ite`.
- Keep the replacement theorem semantically reusable: avoid app-specific hacks that would
  block or distort a later `ite` proof after the separate regime/type-system issue is
  fixed.
- Reusing the narrowed theorem with deferred `ite` branches is acceptable in this branch;
  expanding those branches is not.
- Do not keep the abandoned broad unary route around as a separate compiled legacy path;
  refactor it in place and use git history as the recovery mechanism.
- Do not widen `StepFR` unless the induction-side route collapses first.
- Do not invest more proof work in the old `StepFR_single_run` wrapper until the
  induction-side theorem is usable.
- Do not spend proof effort on `kwhile`.
- Prefer one reusable semantic theorem over duplicating local runtime arguments in both
  `arrow` and `parrow`.

## Stop / Reassess Conditions

- If the narrowed unary theorem still fails for a concrete impure overwrite example, stop
  and restate the counterexample before more proof work.
- If the narrowed unary theorem cannot be cut free of `ite`, stop and redesign the theorem
  boundary instead of proving `ite`.
- If cutting `kwhile` out of the dependency cone forces a larger refactor than the unary
  redesign, do the unary redesign first and postpone the factoring step.

## Working Set

Primary files:

- `LeanProofs/StepFRApp.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/TypeSafety.lean`

Current key lemmas:

- `stepFR_app`
- `StepFR_single_run_core`
- `StepFRSingleRunFinalCleanPcTrue`
- `StepFRSingleRunFinalCleanPcTrue_IH`
- `PreservesInheritedFinalCleanLocsOneRun.apply`
- `PreservesInheritedFinalCleanLocsOneRun.compose`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- `typecheckExpr_lookup_clean_back_of_pc_true`
- `typecheckAssign_result2_lookup_clean_back_of_pc_true`
- `assign_write_step_preserves_inherited_final_clean_pc_true`
- `assign_final_clean_preservation`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
- `PreservesInheritedCleanLocOneRun.trans`
