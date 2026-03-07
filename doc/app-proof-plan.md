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
- the control-poison write semantics change is complete across spec, implementation, docs,
  proofs, and tests
- the app-specific uses of
  `typecheckExpr_clean_lookup_origin_of_pc_true`
  are in place and the `app` branch of that theorem is proved

What still contains `sorry` on the app path:

- `StepFR_single_run`
  still ends with `sorry` for
  `PreservesInheritedCleanLocsOneRun`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
  still has the permanently-postponed `kwhile` branch

Build status:

- `make lean-build-file FILE=LeanProofs/StepFRApp.lean` passes
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

That narrower fact matches the strengthened control-poison semantics:

- poisoned writes strip predicates
- so a location that is finally clean under `pc = true` should be one that was not
  dirtied by the body

## Remaining Work For `stepFR_app`

1. replace the unsound unary clause with the narrower preservation fact actually needed by
   `stepFR_app`
   - do this at the `StepFR` / single-run interface level, not as another app-local trick
   - the new fact should talk about inherited locations that are final-clean, not all
     inherited clean input locations

2. update the `arrow` and `parrow` body-IH use sites in `stepFR_app`
   - they currently destruct the unsound `hpres₀` / `hpres₁` witnesses
   - switch them to the narrower output-conditioned preservation theorem

3. remove the deferred `kwhile` theorem from the `stepFR_app` dependency cone
   - preferred route:
     split `typecheckExpr_clean_lookup_origin_of_pc_true` into an app-relevant theorem that
     excludes `kwhile`
   - do not prove `kwhile`

4. run full verification
   - `make lean-build`
   - reassess remaining `sorry`s reachable from `stepFR_app`

## Execution Order

1. redesign the unary preservation statement narrowly enough to be true for impure bodies
   - success condition:
     a concrete replacement statement is frozen and justified against the current
     control-poison semantics

2. prove the replacement statement where `StepFR_single_run` currently returns the unsound
   clause
   - success condition:
     `StepFR_single_run` no longer depends on the old false preservation claim

3. rewire `stepFR_app` to consume that narrower theorem
   - success condition:
     the current `hpres₀` / `hpres₁` uses are replaced with the new theorem

4. cut `kwhile` out of the dependency cone
   - success condition:
     `stepFR_app` no longer depends on a theorem containing the deferred `kwhile` `sorry`

5. run full verification

## Design Rules

- Do not try to prove `PreservesInheritedCleanLocsOneRun` as currently stated for arbitrary
  impure bodies.
- Keep the replacement fact as narrow as possible and shaped by the current app use sites.
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
- `StepFR_single_run`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- `typecheckExpr_lookup_clean_back_of_pc_true`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
