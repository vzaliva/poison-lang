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

**Verdict**: the blocker is **narrowed much more sharply now, but not solved**.

Latest reviewed progress:
- Upstream commit `f944f9b` (`new-new-app-approach`) expands the two dirty-internal fallback
  branches into the same per-run `StepFR_single_run` structure already used in the
  `¬ qtypCleanUnder` branches.
- The two `agreeOnClean` locations conjuncts are no longer each a single opaque `sorry`; they
  are split into explicit post-body `θ.lookup l` cases.

What is already solved:
- `StepFR_single_run` exists and is proved.
- The per-run workaround is implemented in the `¬ qtypCleanUnder` branches for both arrow and
  parrow.
- The same per-run workaround is structurally implemented for the dirty-internal arrow/parrow
  branches in `f944f9b`; those branches are no longer blocked on setup work.
- The cross-run `agreeOnClean` **variables conjunct** is proved in the different-body branches.
- The clean shared-member path is proved.

The original four app-local holes have been narrowed as follows:
- Hole 1, arrow dirty-internal: `1` top-level `sorry` -> `4` local `sorry`s
- Hole 2, arrow locations conjunct: `1` top-level `sorry` -> `3` local `sorry`s
- Hole 3, parrow dirty-internal: `1` top-level `sorry` -> `4` local `sorry`s
- Hole 4, parrow locations conjunct: `1` top-level `sorry` -> `3` local `sorry`s

So the remaining target surface is now **14 localized `sorry`s**, and they fall into exactly
two semantic blocker categories:
- **12 frame-preservation / location-agreement subgoals**
- **2 `resultAgreesIfClean` subgoals for `p1 = false`**

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

### A. Frame Preservation / Location Agreement (`12` local `sorry`s)

This is the larger blocker.

High-level explanation:
- The locations proofs now do a very concrete case split on whether `θ₀_body.lookup l` and
  `θ₁_body.lookup l` are `none` or `some`.
- The easy subcase is when both are `none`; then `agreeLocUnder.both_unrealized` closes
  immediately.
- The hard subcases are:
  - run 0 unrealized / run 1 realized,
  - run 0 realized / run 1 unrealized,
  - both realized.
- To close those cases, the proof needs a fact of the form:
  - if a location is still typed as clean after the body runs, then the body did not freely
    create or mutate that location in a way that breaks agreement.

Why this is blocked:
- In the earlier shared-member proof, both runs selected the **same** closure body, so we could
  transport everything from one common source member and use `theta_not_contains_if_not_in_memEnv`
  on that shared source.
- In the different-body branches, there is no single common source member to transport from.
- `wfExtendsMap` is not enough here: it preserves existing realizations, but it does **not**
  tell us that `none` stays `none`.
- For arrow bodies, this is genuinely harder because bodies are impure and may allocate or write.
- For parrow bodies, the static side is somewhat nicer because pure typing should keep
  `memEnv' ⊆ result1.memEnv'`, but that still does not by itself prove anything about runtime
  realization maps or heap contents.

Friendly intuition:
- The proof is trying to say: "if this location still counts as clean at the end, then the two
  runs must still line up on it."
- Right now we know how to prove that when both runs came from the same body.
- We do **not** yet know how to prove it when the runs took different bodies, because we are
  missing a precise theorem saying "untouched clean locations stay untouched" or "fresh clean
  locations cannot appear here."

Suggested ways to fix:
- Best narrow fix:
  - prove a frame lemma specialized to this app/body setting saying that a location which is
    still clean after body evaluation must come from the pre-body context and must keep the same
    runtime content unless the body explicitly wrote it.
- Likely needed ingredients:
  - a static source lemma for clean post-body locations,
  - a runtime lemma that unwritten addresses keep their values,
  - possibly a realization-map lemma saying pure/non-writing evaluation does not newly realize
    pre-existing clean locations.
- Parrow may admit a narrower first step:
  - use pure-context memory-subset reasoning to rule out genuinely new typed locations,
  - then prove the remaining realization-map / runtime frame fact.
- If this starts turning into a whole-program generic preservation theorem for arbitrary
  expressions, trigger reassessment rather than continuing to widen.

### B. `resultAgreesIfClean` When `p1 = false` (`2` local `sorry`s)

This is the smaller blocker, but conceptually deep.

High-level explanation:
- When `p1 = true`, `normalizeAppResultByProvenance` forces the final result to be poisoned with
  `noPred`, so `resultAgreesIfClean` becomes vacuous.
- When `p1 = false`, that shortcut disappears.  The final result may still carry a live
  predicate, so the proof must show a **real cross-run agreement fact** about `o₀` and `o₁`.

Why this is blocked:
- The per-run `StepFR_single_run` machinery gives only unary facts for each run separately:
  - `valueHasETyp`,
  - `runtimeInstantiatesCtx`,
  - `consistentWithRegime`,
  - `valueConsistentWithRegime`.
- Those are enough to rebuild the unary parts of the output pack.
- They are **not** enough to manufacture a cross-run `resultAgreesIfClean` when the two runs may
  have selected different closure bodies.
- The existing clean-sync helpers only split into:
  - shared-body witness, or
  - `¬ internalPoisonClean result1.qualType`.
- In the dirty-internal branch we are already in the second case, so the helper gives no shared
  body relation to continue with.

Friendly intuition:
- `StepFR_single_run` tells us: "run 0 is okay by itself" and "run 1 is okay by itself."
- But `resultAgreesIfClean` asks for more: "do the **two runs agree with each other** on the
  final result?"
- For `p1 = false`, nothing currently bridges that gap when the selected bodies differ.

Suggested ways to fix:
- Best local fix:
  - prove an app-specific cross-run lemma for dirty-internal application saying that if the final
    app result is clean-under-regime even though internal poison is dirty, then the two outputs
    still agree in exactly the way `resultAgreesIfClean` needs.
- Another possible route:
  - prove a more operational theorem that, under `p = true` and `p1 = false`, any final result
    that is still clean must collapse to a non-function/non-reference case where equality is
    forced.
- If neither statement is actually true, then the spec or theorem shape may need adjustment.
  That is a design issue, not just missing proof search.

### C. What This Means For The Original Four Holes

The original four app-local `sorry`s are no longer the right unit of work.

They now reduce to two semantic facts:
- frame preservation for clean locations across different body executions,
- cross-run result agreement for the `p1 = false` dirty-internal case.

That is useful progress: the remaining work is much clearer than before.

## 4. Working Hypothesis

The old plan of "just mirror the `¬ qtypCleanUnder` branches and finish the four holes" is no
longer the right description.

What the recent narrowing work shows is:
- the **structural** app-local proof engineering is mostly done,
- the **remaining** work is now concentrated in two facts that are plausibly outside the original
  handoff budget.

Current best hypothesis:
- one narrow frame-preservation theorem (or a very small cluster of them) may unlock most or all
  of the 12 location subgoals,
- one app-specific cross-run result-agreement lemma may unlock the 2 `p1 = false` subgoals.

But these blockers now match the reassess triggers much more closely than before:
- the location subgoals may force generic runtime/frame infrastructure,
- the `p1 = false` subgoals may force a stronger cross-run theorem than the current app-local
  setup provides.

## 5. Exit Condition

This blocker note is finished when the four direct app-local holes are closed:
- dirty-internal arrow fallback
- dirty-internal parrow fallback
- arrow locations conjunct
- parrow locations conjunct

Immediate milestone before that:
- discharge the 14 narrowed `sorry`s from `f944f9b`, or
- conclude that doing so really does require widening into one of the reassess-trigger areas
  below.

At that point, control returns to [app-proof-plan.md](/work/doc/app-proof-plan.md) for the
remaining `app` proof work.

## 6. Bottom Line

- The blocker is **not solved yet**.
- The proof has nevertheless made real progress: the four original holes have been reduced to
  **14 localized subgoals**.
- Those 14 subgoals are not random cleanup; they cleanly expose **two** real remaining blockers:
  frame preservation for clean locations, and non-vacuous cross-run result agreement when
  `p1 = false`.
- `StepFR_single_run` and the member-transport strategy are now clearly validated.
- The open question is no longer "what proof shape should we try?" but rather "can these two
  semantic gaps be solved without widening scope?"

## 7. Small Guidance

Use the existing `¬ qtypCleanUnder` branches as the primary template, and use `f944f9b` as the
current best decomposition of the dirty-internal branches.

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
- In the dirty-internal branches, do **not** assume the last conjunct is vacuous:
  `resultAgreesIfClean` is only automatically vacuous in the `p1 = true` path.
- For the location subgoals, the current best local shape is the explicit case split on:
  - `θ₀_body.lookup l = none` / `some _`
  - `θ₁_body.lookup l = none` / `some _`
- For the locations conjunct, start from the same regime-monotonicity setup already used for
  the variables conjunct:
  - member monotonicity for each closure application,
  - `joinTypeResults_regime_monotone`,
  - `cleanUnder_of_monotone` to pull cleanliness back before the join.
- Do not expect `wfExtendsMap` by itself to solve the asymmetric `none/some` location cases.
  It preserves existing realizations, but it does not prove that `none` stays `none`.
- Arrow and parrow should be treated differently here:
  - arrow likely needs a real frame argument because bodies can write,
  - parrow may admit a narrower source-of-location argument first because pure typing should keep
    `memEnv'` inside the pre-body `memEnv`.
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
