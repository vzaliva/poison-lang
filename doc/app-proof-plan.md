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
- the control-poison write semantics change is complete across spec, implementation, docs,
  proofs, and tests
- the app-specific uses of
  `typecheckExpr_clean_lookup_origin_of_pc_true`
  are in place and the `app` branch of that theorem is proved

What still contains `sorry` on the app path:

- `StepFR_single_run`
  still ends with `sorry` for the old direct single-run wrapper path
- the induction-side companion theorem
  `StepFRSingleRunFinalCleanPcTrue`
  is now defined, but not yet proved or threaded into the app body IH
- `stepFR_app` still uses the current `StepFR_single_run` witness in the narrowed
  inherited-location `arrow` / `parrow` fallback subproofs
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

## Remaining Work For `stepFR_app`

1. prove the induction-side unary theorem
   `StepFRSingleRunFinalCleanPcTrue`
   - do not touch `StepFR` itself
   - do not try to salvage the old `StepFR_single_run` wrapper first
   - prove the theorem for low-blast-radius cases first:
     literals, variables, `fn`, `pfn`, `unaryop`, `deref`
   - then use `PreservesInheritedCleanLocOneRun.trans` to handle the sequential cases:
     `seq`, `op`, `vlet`
   - leave `kwhile` out of scope

2. update the `arrow` and `parrow` body-IH use sites in `stepFR_app`
   - stop depending on the current `StepFR_single_run` wrapper in the different-body
   fallback subproofs
   - switch those sites to the companion unary IH theorem
   - do this as soon as the theorem is available for body forms used by `app`

3. remove the deferred `kwhile` theorem from the `stepFR_app` dependency cone
   - preferred route:
     split the app-consumed theorem surface so the body-IH theorem and the clean-origin
     theorem each have an app-relevant form that excludes `kwhile`
   - do not prove `kwhile`

4. run full verification
   - `make lean-build`
   - reassess remaining `sorry`s reachable from `stepFR_app`

## Execution Order

1. prove `StepFRSingleRunFinalCleanPcTrue` for the trivial / identity cases
   - success condition:
     the theorem is no longer only a definition skeleton

2. prove the sequential composition cases using
   `PreservesInheritedCleanLocOneRun.trans`
   - success condition:
     `seq`, `op`, and `vlet` no longer block the body-IH route

3. thread the companion unary IH through the strong induction theorem
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
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- `typecheckExpr_lookup_clean_back_of_pc_true`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
- `PreservesInheritedCleanLocOneRun.trans`
