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
  `stepFRSingleRunFinalCleanPcTrue_newRef`, and
  `stepFRSingleRunFinalCleanPcTrue_deref`
- the different-body `arrow` / `parrow` fallback sites in `stepFR_app` already consume the
  narrowed unary IH instead of `StepFR_single_run`
- the unary `app` case is now factored into `LeanProofs/StepFRApp.lean` as
  `stepFRSingleRunFinalCleanPcTrue_app`, with private `arrow` and `parrow`
  branches that compile without depending on binary `StepFR_IH`
- the global unary theorem now calls that app-specific lemma instead of carrying a local
  `app` `sorry`
- the unary `vlet` case now compiles as
  `stepFRSingleRunFinalCleanPcTrue_vlet`
  and is wired into the global unary theorem
- generic tag-meaning update helpers
  (`PredRespectsTagMeaning`, `EnvRespectsTagMeaning_updateMemEnv`,
  `EnvRespectsTagMeaning_updateLocsetWeak`, and companions)
  now live upstream in `LeanProofs/RegimeConsistency.lean` rather than being stranded
  in `StepFRAssign`
- `typecheckExpr_preserves_wfTagMeaningCtx_main` now has its `app` branch compiled:
  the helper layer for `applyFnTClosure` / `applyPFnTClosure` is in place and the
  remaining local surface there is now only conservative `ite` mode 3 plus deferred
  `kwhile`
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
- `typecheckExpr_clean_lookup_origin_of_pc_true`
  still has the permanently-postponed `kwhile` branch
- `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree`
  still contains the deferred `kwhile` branch and therefore still carries a `sorry`
- `stepFR_ite_mode3` / `stepFR_ite_mode4` remain externally blocked under issue `#128`
- `typecheckExpr_preserves_wfTagMeaningCtx_main`
  still carries `sorry`, but the remaining local branches are now only conservative
  `ite` mode 3 and permanently-deferred `kwhile`

Build status:

- full `make lean-build` passes
- remaining warnings are `sorry` warnings only

## Main Blocker

Short version:

- the app-local witness design problem is resolved:
  `stepFR_app` now uses the narrowed unary IH, and the unary `app` and `vlet` cases both
  compile
- the remaining blocker is no longer inside `stepFR_app` or its app-specific helpers
- what remains is theorem packaging:
  the global unary assembly still contains deferred `kwhile`, and the separate `ite`
  work remains blocked under issue `#128`

Planning consequence:

- do not reopen the app-local witness design
- treat the current app implementation path as established
- accept the existing deferred `ite` / `kwhile` `sorry`s as upstream debt on this branch
- do not spend more time trying to isolate those branches away from the unary app route

For the detailed technical discussion, see `doc/app-framing-proposal.md`.

## Remaining Work For `stepFR_app`

1. treat the current app-local milestone as the target
   - `stepFR_app` itself is no longer blocked by app-specific unary reasoning
   - the remaining `sorry`s are all outside that local path
   - existing deferred `ite` / `kwhile` `sorry`s are accepted upstream debt for this branch

2. keep `ite` out of scope on this branch
   - do not do new `stepFR_ite_*` proof work
   - wait for the separate regime/type-system fix in issue `#128`

3. run full verification
   - `make lean-build`
   - reassess remaining `sorry`s reachable from `stepFR_app`

## Execution Order

1. checkpoint the current app-local success
   - success condition:
     full `make lean-build` passes and the app-local unary route remains stable
   - stopping rule:
     stop here once only deferred upstream `ite` / `kwhile` `sorry`s remain on the app path

2. keep waiting on external `ite`
   - success condition:
     no accidental `stepFR_ite_*` work is added on this branch

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
- If a proposed refactor claims to remove `ite` or `kwhile` from the app dependency cone,
  first identify the replacement theorem that can still serve as `singleIH` for arbitrary
  closure bodies. Without that replacement, reject the refactor.
- If only deferred upstream `ite` / `kwhile` `sorry`s remain after app-local work is closed,
  stop rather than opening new isolation work on this branch.

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
