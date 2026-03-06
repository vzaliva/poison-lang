# Body StepFR IH Evidence Blocker

Focused note on the remaining blocker in `stepFR_app`.

## Purpose

This document tracks the **body-IH / cross-run agreement blocker** that still needs to be
solved before we can return to [app-proof-plan.md](/work/doc/app-proof-plan.md) and continue
finishing the `app` proof in the normal flow.

It is **not** a full inventory of every remaining `sorry` in generic declarations.

## Scope

In scope:
- The dirty-internal and `¬ qtypCleanUnder` fallback branches inside `stepFR_app`
- The use of `StepFR_single_run` to recover per-run body evidence
- The remaining `agreeOnClean` obligations that are specific to those branches

Out of scope for this note:
- `stepFR_ite_*`
- `stepFR_kwhile`
- Generic preservation cleanup, except where a very narrow helper is directly needed to finish
  the blocker below

Scope guard:
- If the shortest route to closing this blocker starts requiring proofs of `stepFR_ite_*` or
  `stepFR_kwhile`, stop and reassess in the main plan instead of expanding this blocker note.

## Current Status (2026-03-06)

**Verdict**: the blocker is **partially solved, not fully solved**.

What is already solved:
- `StepFR_single_run` exists and is proved.
- The per-run workaround is implemented in the `¬ qtypCleanUnder` branches for both arrow and
  parrow.
- The cross-run `agreeOnClean` **variables conjunct** is proved in those branches.
- The clean shared-member path is proved.

What remains in `stepFR_app` itself:
- Arrow dirty-internal fallback placeholder pack
- Arrow `agreeOnClean` locations conjunct
- Parrow dirty-internal fallback
- Parrow `agreeOnClean` locations conjunct

## 1. The Blocker

The induction hypothesis for `StepFR` expects both runs to evaluate the **same expression**.
That works in the clean shared-member case, but it fails in the dirty cases when the two runs
may choose different closure bodies.

This affects two situations:
- **Dirty internal**: `p1 = false`, but `¬ internalPoisonClean`
- **Dirty outer**: `¬ qtypCleanUnder` (equivalently the path where `p1 = true` in the app proof)

The proposed fix was:
1. derive a single-run corollary `StepFR_single_run`,
2. apply it separately to each chosen body,
3. transport the resulting facts from each selected member back to the joined app result.

That approach is now validated, but not yet complete.

## 2. What Has Been Validated

### A. `StepFR_single_run` works

`StepFR_single_run` is proved via same-config self-agreement and is already being used in the
fallback machinery.

### B. Per-run body extraction works

The proof already successfully performs the following pattern:
1. extract the selected closure member for each run,
2. recover body typing from the corresponding `applyFnTClosure` / `applyPFnTClosure` map,
3. build the per-run body context,
4. apply `StepFR_single_run`,
5. transport the resulting evidence back through `joinTypeResults`.

### C. The variables half of `agreeOnClean` works

For the `¬ qtypCleanUnder` branches, the variables conjunct is already done using the expected
monotonicity and transport chain.

So the method is not speculative anymore.  The remaining work is concentrated in the parts
listed below.

## 3. Remaining Work To Clear This Blocker

### A. Dirty-internal arrow branch

The dirty-internal arrow branch still ends in a placeholder pack.

What remains:
- replace the placeholder with the same per-run body-IH structure already used in the
  `¬ qtypCleanUnder` branch,
- discharge the non-vacuous `resultAgreesIfClean` obligation that appears because `p1 = false`.

### B. Dirty-internal parrow branch

The dirty-internal parrow branch is the same conceptual problem as the arrow one, but is still
left as a top-level `sorry`.

What remains:
- mirror the arrow dirty-internal construction,
- reuse the nearby parrow `¬ qtypCleanUnder` scaffolding where possible.

### C. `agreeOnClean` locations conjuncts

The remaining cross-run blocker in the `¬ qtypCleanUnder` branches is the **locations** half of
`agreeOnClean`.

For a clean location entry in the joined result, the proof still needs to show one of:
- both runs realize the location with agreeing values, or
- both runs leave it unrealized.

This is the last unresolved cross-run obligation after the variables conjunct.

## 4. Working Hypothesis

The right path is still:
- finish dirty-internal using the same per-run `StepFR_single_run` pattern,
- then close the two locations-conjunct obligations.

Nothing in the current file suggests a different architecture is needed yet.

The main risk is narrower than before:
- the locations conjunct may require a sharper characterization of which guard-clean memory
  entries can survive the join under poisoned control flow.

That is still an app-local issue.  It should not automatically expand into proving unrelated
`ite`/`kwhile` theorems.

## 5. Exit Condition

This blocker note is finished when the four direct app-local holes are closed:
- dirty-internal arrow fallback
- dirty-internal parrow fallback
- arrow locations conjunct
- parrow locations conjunct

At that point, control returns to [app-proof-plan.md](/work/doc/app-proof-plan.md) for the
remaining `app` proof work.

## 6. Bottom Line

- The blocker is **not solved yet**.
- The `StepFR_single_run` strategy is **already validated in code**.
- The remaining work is **narrow** and still centered on the four app-local holes above.
- This document should stay focused on that blocker only; broader proof-surface cleanup belongs
  in the main plan, if needed at all.

## 7. Small Guidance

Use the existing `¬ qtypCleanUnder` branches as the primary template.

Helpful reminders:
- For the dirty-internal arrow/parrow branches, reuse the same per-run structure already used
  in the `¬ qtypCleanUnder` branches:
  - extract the chosen member with `closureCapturedVarsRegime_closure_extract` or
    `closureCapturedVarsRegime_peClosure_extract`,
  - recover body typing with `applyFnTClosure_regular_inv_of_mapM_mem` or
    `applyPFnTClosure_regular_inv_of_mapM_mem`,
  - run `StepFR_single_run` separately on each body,
  - transport the resulting facts back with the existing `joinTypeResults_transport_*_from_member`
    lemmas.
- The main difference from the `¬ qtypCleanUnder` branches is not the structure; it is that
  `resultAgreesIfClean` is **not vacuous** when `p1 = false`.  So keep the transported
  `resultAgreesIfClean` evidence instead of trying to collapse it via the poisoned/noPred path.
- For the locations conjunct, start from the same regime-monotonicity setup already used for
  the variables conjunct:
  - member monotonicity for each closure application,
  - `joinTypeResults_regime_monotone`,
  - `cleanUnder_of_monotone` to pull cleanliness back before the join.
- A useful split for clean joined locations is:
  - locations already present before the body runs,
  - locations introduced by a selected body result.
- For pre-existing locations, first try to transport the pre-call locations half of
  `agreeOnClean` through the same theta-extension / regime-monotonicity path already used for
  variables.
- For body-produced locations, first try the `both_unrealized` route rather than immediately
  trying to prove agreement of fresh values across runs.
- If either subproblem starts forcing full generic preservation cleanup or proofs of
  `stepFR_ite_*` / `stepFR_kwhile`, stop and return to [app-proof-plan.md](/work/doc/app-proof-plan.md)
  for reassessment instead of widening this blocker note.

## 8. Handoff Constraints

If this note is handed to someone as a standalone assignment, the intended contract is:

Deliverable:
- Close the four app-local holes described above.
- Keep the work localized to `stepFR_app` and closely related app-specific helper lemmas.
- Leave `stepFR_ite_*` and `stepFR_kwhile` untouched.

Preferred proof style:
- Reuse the existing `StepFR_single_run` pattern.
- Prefer inline reasoning inside the relevant `stepFR_app` branches or narrow app-specific
  helpers over new whole-syntax `typecheckExpr_preserves_<invariant>` lemmas.
- Reuse existing transport lemmas before inventing new abstractions.

Constraints:
- Do not change the statement of `StepFR`.
- Do not add new global invariant-preservation premises or conclusions to `StepFR`.
- Do not widen the task into generic typechecker-preservation cleanup.
- Avoid relying on line numbers; search by lemma names, branch comments, and nearby helper names.

Reassess triggers:
- The shortest route appears to require proving `stepFR_ite_*` or `stepFR_kwhile`.
- The shortest route appears to require finishing whole-syntax generic preservation lemmas.
- The locations conjunct appears to require a new global invariant rather than a local transport
  argument.

In those cases, stop and hand control back to [app-proof-plan.md](/work/doc/app-proof-plan.md)
instead of continuing to widen this blocker assignment.
