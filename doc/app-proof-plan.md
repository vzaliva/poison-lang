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
- all `kwhile` proof work
- unrelated proof cleanup

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
- the branch-join side of the unary `ite` route is now factored enough for focused work:
  `joinMemEnvsStrong_lookup_cleanUnder_left_of_contains` and
  `joinMemEnvsStrong_lookup_cleanUnder_right_of_contains`
  now compile and isolate the actual-branch clean extraction step
- the remaining hard part of the unary route is no longer raw constructor coverage:
  the conservative `ite` modes expose a theorem-shape problem

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

The current unary clause

- `PreservesInheritedCleanLocsOneRun`

is too strong for arbitrary impure `Expr` bodies.

Why:

- it requires an inherited clean location to keep the same realized address/value pair after
  one run
- but an impure body can overwrite an inherited clean location
- therefore the clause is false in general for `arrow` bodies

This is not just a missing proof. It is a statement-level mismatch.

The current uses in `stepFR_app` only need a narrower fact:

- if a body is typed under poisoned control, and a final lookup at inherited location `l`
  is still clean, then the runtime cell for `l` was preserved across that run
- crucially, this narrower fact must constrain the chosen output realization map witness,
  not just prove a heap-side statement after `StepFR_single_run_core`

That narrower fact matches the strengthened control-poison semantics:

- poisoned writes strip predicates
- so a location that is finally clean under `pc = true` should be one that was not
  dirtied by the body

Current status of that blocker:

- the semantic core and the final-witness packaging are now validated for `assign`
- the next issue is not the local branch-clean reasoning
- the next issue is that the current induction-side theorem
  `StepFRSingleRunFinalCleanPcTrue`
  still asks for the full `StepFR_single_run_core` witness payload
  (`wfTagMeaningCtx`, `runtimeInstantiatesCtx`, `consistentWithRegime`,
  and `valueConsistentWithRegime` for the final joined result)
  in addition to the preservation fact that `stepFR_app` actually needs
- for conservative `ite` joins, that full payload forces reasoning about the joined
  post-context produced by both branches, even though the runtime only executes one branch
- the new left/right clean-extraction lemmas show the preservation part is still on track;
  the overreach is in the witness packaging, not the final-clean transport itself

Working conclusion:

- do not keep pushing the current full-witness theorem shape first
- split out or prioritize a preservation-focused unary theorem surface for the app path:
  it should return the chosen output realization map witness together with
  `PreservesInheritedFinalCleanLocsOneRun`
  and only the minimal side conditions that `stepFR_app` consumes
- only after the app path is unblocked should we decide whether the broader
  `StepFRSingleRunFinalCleanPcTrue` payload is worth finishing

## Remaining Work For `stepFR_app`

1. split the unary route into an app-focused theorem surface
   - keep `StepFR` unchanged
   - do not revive the old `StepFR_single_run` wrapper
   - introduce or prioritize a theorem whose critical output is:
     a chosen `θ'` together with `PreservesInheritedFinalCleanLocsOneRun`
   - keep any extra witness obligations minimal and justified by actual `stepFR_app` use

2. finish the constructor coverage needed for that narrower unary theorem
   - already covered:
     literals, `assign`, `seq`, `unaryop`, `op`, `fn`, `pfn`, `var`, `newRef`
   - still needed on the app path:
     `deref`, `vlet`, and the relevant `ite` modes
   - leave `kwhile` out of scope

3. package the covered constructor lemmas into the strong-induction theorem
   - do this for the narrowed unary theorem first
   - only widen back out if a real downstream need appears

4. update the `arrow` and `parrow` body-IH use sites in `stepFR_app`
   - stop depending on the current `StepFR_single_run` wrapper in the different-body
   fallback subproofs
   - switch those sites to the companion unary IH theorem
   - do this as soon as the theorem is available for the body forms used by `app`

5. remove the deferred `kwhile` theorem from the `stepFR_app` dependency cone
   - preferred route:
     split the app-consumed theorem surface so the body-IH theorem and the clean-origin
     theorem each have an app-relevant form that excludes `kwhile`
   - do not prove `kwhile`

6. run full verification
   - `make lean-build`
   - reassess remaining `sorry`s reachable from `stepFR_app`

## Execution Order

1. narrow the unary theorem surface to the app-relevant preservation payload
   - success condition:
     conservative `ite` modes no longer require unrelated joined-post-context packaging

2. finish the remaining constructor cases on that narrowed theorem
   - success condition:
     `deref`, `vlet`, and the app-relevant `ite` modes no longer block the body-IH route

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
- Do not widen `StepFR` unless the induction-side route collapses first.
- Do not invest more proof work in the old `StepFR_single_run` wrapper until the
  induction-side theorem is usable.
- Do not spend proof effort on `kwhile`.
- Prefer one reusable semantic theorem over duplicating local runtime arguments in both
  `arrow` and `parrow`.

## Stop / Reassess Conditions

- If the narrowed unary theorem still fails for a concrete impure overwrite example, stop
  and restate the counterexample before more proof work.
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
