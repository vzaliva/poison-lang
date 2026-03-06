# `stepFR_app` Status After The Proposed Fixes

This note updates the earlier blocker analysis under the following assumptions:

- the typing change from [app-typing.proposal](/work/doc/app-typing.proposal) is accepted and
  implemented
- the framing/location fix from [app-framing-proposal.md](/work/doc/app-framing-proposal.md) is also
  accepted and implemented

For the framing fix, there are two allowed routes:

- prove the needed app/body lemmas directly
- or strengthen `StepFR` so the needed clean-location preservation fact is carried as part
  of the invariant

This is therefore a **forward-looking completion note**: it describes what should remain
once those decisions are made.

## Purpose

Record whether any app-specific conceptual blocker remains after the two identified
problems have been addressed.

Short answer:

- **no remaining app-specific semantic blocker is currently expected**

What should remain is proof integration and closure work, not a new unresolved design
question inside `stepFR_app`.

## What The Two Fixes Remove

The earlier narrowed surface had two conceptual problems:

- dirty-internal `resultAgreesIfClean` for the `p1 = false` non-function case
- post-body clean-location agreement across different body executions

Under the accepted fixes:

- the typing change removes the first problem by preventing the bad retained-predicate
  path
- the framing fix removes the second problem, either by local lemmas or by baking the
  needed fact into `StepFR`

So the old “two remaining blockers” picture should disappear.

## Expected Status Of The Original Four Holes

Under these assumptions, the original four app-local holes should no longer represent
open semantic questions.

They should reduce to ordinary proof completion:

- thread the new typing rule shape through the relevant app branches
- use the chosen framing solution
- close the localized `sorry`s

In other words:

- if both fixes are sound and implemented, the four holes should be **closable**
- any remaining difficulty should be about proof plumbing or scope, not about whether the
  theorem shape is wrong

## Remaining Work If The Two-Lemma Route Is Chosen

If the framing fix is implemented by app/body lemmas, the remaining work should stay
fairly local.

Expected steps:

1. thread the typing change through Ott, implementation, and the app proof
2. prove the static inheritance lemma and the typed-evaluation preservation lemma
3. use those lemmas to close the remaining locations conjuncts
4. discharge any now-trivial dirty-internal leftovers

Expected character of the work:

- mostly app-local
- mostly confined to `stepFR_app` and narrow helper lemmas
- no new conceptual blocker expected

## Remaining Work If The `StepFR`-Invariant Route Is Chosen

If the framing fix is implemented by strengthening `StepFR`, the remaining work is still
expected to be conceptually straightforward, but it is no longer app-local.

Expected steps:

1. strengthen the `StepFR` statement/package with the chosen clean-location preservation
   fact
2. update the helper lemmas and downstream case proofs that depend on `StepFR`
3. revisit `stepFR_app` and consume the strengthened invariant there
4. rebuild the step theorem chain

Expected character of the work:

- broader proof refactor
- more files touched
- still no new app-specific semantic blocker expected

So this route changes **scope**, not the diagnosis.

## What Could Still Go Wrong

Even under these assumptions, there are still practical risks:

- the two-lemma route may turn out not to stay narrow and local
- the strengthened-`StepFR` route may cause a larger-than-expected downstream proof
  refactor
- an attempted lemma may need to be restated more carefully than first expected

But these would be engineering/scope problems, not evidence of a new theorem-level flaw
in `stepFR_app`.

## Current Best Reading

Assuming the proposals from [app-typing.proposal](/work/doc/app-typing.proposal) and
[app-framing-proposal.md](/work/doc/app-framing-proposal.md) are accepted:

- `stepFR_app` no longer has a known app-specific conceptual blocker
- the remaining task is to finish the proof by integration
- the main choice is now:
  - keep the fix local with app/body lemmas, or
  - widen scope and carry the preservation fact inside `StepFR`

## Handoff Guidance

If this note is handed off as a standalone assignment, the intended contract is:

Deliverable:

- assume both proposed fixes are accepted
- finish `stepFR_app`
- close the remaining app-local `sorry`s

Preferred order:

1. implement the typing change
2. choose one framing route
3. close the app branches using that route
4. rebuild and verify the affected proof chain

Decision rule:

- prefer the two-lemma route if it stays narrow
- switch to the strengthened-`StepFR` route only if the local lemma route starts turning
  into duplicated whole-syntax preservation work

Reassess trigger:

- the chosen route starts exposing a new theorem-level inconsistency rather than ordinary
  proof plumbing

If that happens, return to [app-proof-plan.md](/work/doc/app-proof-plan.md).
