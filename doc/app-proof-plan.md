# `stepFR_app` Proof Plan

Notes:
- This is the active planning document and current source of truth for next proof work.
- The focused blocker memo for the different-body framing issue is
  `doc/app-framing-proposal.md`.
- Design history and failed routes are in `doc/app-proof-history.md`.
- Avoid relying on line numbers; they drift frequently. Use lemma names / TODO tags and `rg`.

## 1. Goal

Complete the remaining obligations in the `app` case of the fault-robustness step theorem
(`stepFR_app`) in `LeanProofs/StepFRApp.lean`, together with only the dependencies that are
actually needed to finish that proof.

Out of scope:

- `stepFR_ite_*`
- `stepFR_kwhile`
- `memEnv_lookup_etyp_int` as a primitive / issue #70

Scope guard:

- if app-proof work starts requiring `stepFR_ite_*` or `stepFR_kwhile` as immediate
  prerequisites, stop and reassess the architecture instead of absorbing them into this plan

What makes `stepFR_app` hard:

- runtime picks a specific closure alternative
- typing returns a joined result across alternatives
- the proof must transport runtime/agreement facts from the selected member to the joined
  result

## 2. Current Status and Plan

### Checkpoint: 2026-03-07 — Step 5 classified: current unary clause is not enough for `arrow`

Build: **clean** (no errors; sorry-only warnings).

What was checked:

- the remaining inherited dirty-to-clean `arrow` branch was compared against the actual
  `ioFree` typing rules (`typecheckVar`, `typecheckDeref`, `typecheckAssign`)
- the bounded falsification target was not “the theorem is false”, but “can the body make an
  inherited location final-clean without that location being pre-body clean?”

What this showed:

- yes, in principle: an impure body under `pc = true` can write an inherited location `l`
  from a source value that is already clean-under-regime even when the pre-body entry at `l`
  is not clean
- the key shape is a write from a value whose guard tag is active in `regime` but not
  syntactically known in `tagEnv`; in that case `typecheckVar` / `typecheckDeref` preserve
  the guard predicate, and `typecheckAssign` can leave `l` final-clean-under-regime even
  though `qt'` at `l` was not pre-body clean
- this does **not** give a counterexample to fault-robustness by itself; the source value may
  still agree across runs because it is clean
- but it does show the current unary fact
  `PreservesInheritedCleanLocsOneRun ...`
  is not sufficient to finish the inherited dirty-to-clean `arrow` branch locally:
  it only talks about locations that were already clean before the run, while the remaining
  `arrow` case needs a summary about locations that become clean by being overwritten from a
  clean source during the run

Plan consequence:

- keep the current unary clause for `parrow`; it was the right fix there
- do **not** start proving the new conjunct in `StepFR` yet
- the next design step is now to decide on a second unary/body-summary fact for impure
  `arrow` bodies, rather than trying to force the current clause through the remaining
  `arrow` branch

### Checkpoint: 2026-03-07 — `arrow` validation paused at inherited dirty-to-clean case

Build: **clean** (no errors; sorry-only warnings).

What changed since the previous checkpoint:

- the narrowed outer-not-clean `arrow` locations hole was decomposed into two explicit
  residual subcases instead of one broad `sorry`
- the inherited-clean subcase is now proved and follows the same pattern as `parrow`
- the remaining `arrow` work is no longer just the fresh-location question

What this revealed:

- the fresh-location subcase is still a local `stepFR_app` obligation
- but the inherited dirty-to-clean subcase is the actual plan-level fork:
  an inherited location can be pre-body dirty, become final-clean after body updates, and
  then the current `PreservesInheritedCleanLocsOneRun` interface does not directly apply
- this means the earlier Step 4 summary (“`arrow` only needs a fresh-location cleanliness
  fact”) was too optimistic
- before proving the new unary conjunct in `StepFR`, we must first classify this inherited
  dirty-to-clean `arrow` subcase as either:
  1. locally solvable from existing assignment/update transport machinery, or
  2. a genuine obstruction showing the current unary interface is too weak for `arrow`

### Checkpoint: 2026-03-07 — strengthened unary interface validated on `parrow`; keep the shape

Build: **clean** (no errors; sorry-only warnings).

What is now settled:

- `PreservesInheritedCleanLocOneRun` / `PreservesInheritedCleanLocsOneRun` were added in
  `LeanProofs/StepFR.lean`
- `StepFR_single_run` was strengthened with the extra unary conjunct, and the downstream
  destructuring sites needed by app were updated
- the narrowed outer-not-clean `parrow` locations hole now accepts the strengthened unary
  interface cleanly
- the `parrow` proof no longer needs an app-local ad hoc witness trick; it works by:
  impossible fresh-clean case via pure mem-subset, then inherited-clean transport back to
  the pre-body context, then `hpres₀ / hpres₁` plus pre-body `agreeOnClean`
- the helper needed on the `parrow` side turned out to be a pure typing bridge
  (`typecheckExpr_pure_mem_lookup_bridge_of_toPExpr`), not evidence that
  `StepFR_single_run` needs a broader semantic interface

What the assessment showed:

- the added `StepFR_single_run` clause did solve the blocker it was meant to solve:
  the different-body `parrow` location proof now has the unary fact it needed
- the remaining narrowed `arrow` hole is different in kind: it needs a fact of the form
  “under poisoned body `pc`, freshly introduced locations cannot remain clean in the final
  typed result”
- that remaining `arrow` gap does **not** currently look like missing data in the new
  unary interface, so the strengthened conclusion should stay as-is
- proving the new `PreservesInheritedCleanLocsOneRun ... θ θ'` conjunct itself will still
  require changes in the proof-producing `StepFR` induction / case proofs, not just in the
  `StepFR_single_run` wrapper

### Checkpoint: 2026-03-06 — app-local framing route stopped; move to broader unary infrastructure

Build: **clean** (no errors; sorry-only warnings).

What is settled:

- shared-member transport is good enough
- final recombination is not the blocker anymore:
  `join_transport_agreeOnClean_from_member` already packages the joined clean-location proof
  once a branch can supply either a source-member witness or final `none / none`
- the remaining different-body app blocker is the unary fact needed to produce that final
  `none / none` for inherited clean locations
- the missing shape now looks more specific: a strengthened `StepFR_single_run`-style
  theorem in `StepFR.lean` that keeps the same existential post-map witness `θ'` but adds
  inherited clean-location preservation facts for that same `θ'`

Why the app-local route stopped:

- `StepFR_single_run` only exposes an existential post-run `θ'`
- `wfExtendsMap` preserves existing `some` bindings, not `none`
- `runtimeInstantiatesCtx` permits realizing old typed locations
- `freshLoc_not_realized` only applies to fresh `l >= nextLoc`
- the only obvious local `parrow` escape hatch, reusing the pre-body maps as final
  witnesses, also stalls because the library has extension transport such as
  `valueHasETyp_extends`, but no reverse/shrink transport for `valueHasETyp` or
  `valueConsistentWithRegime`

Decision:

- stop local proof edits aimed only at the narrowed `stepFR_app` holes
- move the active plan to broader unary proof infrastructure
- the goal is to make single-run body results expose the realization-map fact the app proof
  needs by strengthening the `StepFR_single_run` package in `StepFR.lean`, rather than
  reconstructing it ad hoc inside the app branches

See [app-framing-proposal.md](app-framing-proposal.md) for the
focused blocker memo.

### New active plan: strengthen the unary interface

Target shape:

- for an inherited clean location in one body run, the unary output should expose enough to
  conclude:
  - if the location was unrealized before the run, it is still unrealized after the run
  - if the location was already realized before the run, the post-run state preserves the
    realization information needed later for `agreeLocUnder`
- this fact should live on a broader unary interface, not as a local app-branch lemma that
  depends on choosing ad hoc witnesses

Execution sequence:

1. **Freeze the exact strengthened conclusion** — done
   - Extend `StepFR_single_run` with one extra conjunct
     `PreservesInheritedCleanLocsOneRun ... θ θ'` exactly as described in
     [app-framing-proposal.md](app-framing-proposal.md).
   - Do not invent a separate public theorem.
   - Keep the property scoped to inherited clean input locations; the symmetric-fresh case
     remains in `stepFR_app`.
   - Deliverable:
     one precise theorem statement in `LeanProofs/StepFR.lean`.

2. **Change `StepFR_single_run` to that signature and leave only the new conjunct as `sorry`** — done
   - Update the theorem statement in `LeanProofs/StepFR.lean`.
   - Propagate the stronger result shape through the minimum downstream surface needed for
     app.
   - Do not try to prove the new conjunct yet.
   - Deliverable:
     the code compiles with the strengthened `StepFR_single_run`, with the new conjunct as
     the only new `sorry`.

3. **Plug the stronger result into the outer-not-clean `parrow` location hole first** — done
   - Use the strengthened `StepFR_single_run` result in the narrowed `parrow` hole.
   - Prove the downstream app steps that use the new conjunct.
   - Treat the new conjunct itself as an assumption coming from the temporary `sorry`.
   - Outcome:
     the `parrow` hole now closes structurally; the only extra dependency was a pure
     typing bridge for `memEnv.lookup`, not a further extension of the unary interface.

4. **Assess after `parrow` before doing anything broader** — done
   - Result:
     keep the strengthened `StepFR_single_run` shape unchanged.
   - `parrow` accepted the interface cleanly.
   - The narrowed `arrow` review exposed a different missing fact about fresh locations
     under poisoned body `pc`; it did not expose a missing field in the unary interface.
   - Do not widen the unary theorem further at this point.

5. **Classify the inherited dirty-to-clean `arrow` subcase before doing more unary work** — done
   - Result:
     the current unary clause is not enough for this branch.
   - The missing shape is no longer “preserve an already-clean inherited location”, but
     rather “explain why a final-clean inherited location is clean after the run”.
   - In particular, the remaining `arrow` branch needs a way to summarize writes from
     clean sources during an impure body, not just preservation of pre-body-clean cells.

6. **Design the additional unary/body summary needed by impure `arrow` bodies**
   - Candidate direction:
     for an inherited location that is final-clean after one run, expose either
     1. a pre-body clean witness for the same location, or
     2. a clean source/witness explaining the final value written there.
   - Reuse the assignment-specific “final clean after update” reasoning from
     `StepFRAssign` as the template.
   - Stop point:
     freeze the exact new statement before more local app proof work.

7. **Use the new summary to finish the inherited dirty-to-clean `arrow` branch**
   - Replace the current local dead-end at the inherited-location `sorry`s with the new
     unary fact.
   - Do not spend effort on the fresh-location `arrow` branch until this inherited branch
     accepts the revised summary.

8. **Only after that, finish the narrowed `arrow` fresh-location subcase**
   - Prove or isolate the local fact needed on the fresh `arrow` side:
     under poisoned body `pc`, any location newly introduced by the body cannot become
     final-clean in the problematic way.

9. **Then return to proving unary facts in `StepFR`**
   - Prove both unary summaries inside the proof-producing `StepFR` pipeline.
   - Keep the current `PreservesInheritedCleanLocsOneRun` result for the `parrow` path
     unless the new summary cleanly subsumes it.

## 3. Working Rules

- Keep this route focused on the specific `stepFR_app` blocker.
- Do not reopen resolved app-typing questions.
- Do not widen the task into generic proof cleanup unless the strengthened unary route truly
  requires it.
- Do not silently drift into the old witness-substitution idea; if reverse/shrink transport
  becomes necessary, write that down as a separate infrastructure choice.

## 4. Stop / Reassess Conditions

- If the frozen unary property already fails on `newRef` or assignment, stop and restate the
  fallback target before changing theorem interfaces.
- If the new interface would force unrelated `stepFR_ite_*` / `stepFR_kwhile` work as an
  immediate prerequisite, pause and reassess before paying that cost.
- If the only viable route becomes reverse/shrink witness transport, turn that into a new
  explicit plan rather than folding it into this one by accident.

## Appendix A: Working Set

Primary proof sites:

- `LeanProofs/StepFRApp.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/TypeSafety.lean`

Likely key lemmas / definitions for the current track:

- `stepFR_app`
- `join_transport_agreeOnClean_from_member`
- `StepFR_single_run`
- `theta_not_contains_if_not_in_memEnv`
- `wfExtendsMap`
- `runtimeInstantiatesCtx`
- `freshLoc_not_realized`
- `applyFnTClosure`
- `applyPFnTClosure`
- `valueHasETyp_extends`
