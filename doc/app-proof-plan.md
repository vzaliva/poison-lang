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

### Checkpoint: 2026-03-07 — origin theorem now proved through structural, write, and `if` cases; only `app` and `while` remain

Build: pending full `lean-build` for checkpoint verification.

What changed:

- `typecheckExpr_clean_lookup_origin_of_pc_true` is no longer a blanket `sorry`
- it now has a real strong-induction proof covering:
  - literals / variables / functions / pure functions
  - `op`, `unaryop`, `deref`, `seq`, `vlet`
  - `newRef`
  - `assign`
  - all four `if` modes
- added local proof support in `StepFRApp.lean`:
  - `list_fold_joinPredicates_init_noPred`
  - `joinMemEnvsStrong_lookup_cleanUnder_left_or_right`
- strengthened the shared helper
  `typecheckAssign_memEnv_formula` in `LeanProofs/TypeSafety.lean`
  so it now also returns the post-`regime'` equation

What remains inside the theorem:

- `app`
- `kwhile`

Interpretation:

- the theorem debt is now concentrated exactly where the semantics are genuinely global:
  closure-result joins and the while fixpoint
- the previous broad uncertainty about assignment / poisoned writes / conditional joins is
  now discharged in the theorem body itself

### Checkpoint: 2026-03-07 — generic `assign` memory-shape helper proved; origin theorem still the active blocker

Build: pending full `lean-build` for checkpoint verification.

What changed:

- added a proved generic helper in `LeanProofs/TypeSafety.lean`:
  `typecheckAssign_memEnv_formula`
- this packages the exact post-`memEnv'` formula for successful `assign` typing, including
  the strengthened control-poison predicate erasure rule
- the helper is intended to remove duplicated local re-unfolding in
  `typecheckExpr_clean_lookup_origin_of_pc_true`, especially its `assign` case

What this means for the plan:

- the remaining blocker is still
  `typecheckExpr_clean_lookup_origin_of_pc_true`
- but one of its nastier subcases now has the right shared infrastructure in `TypeSafety`
  instead of being reconstructed ad hoc inside `StepFRApp`
- likely next supporting helper after this:
  a `restrictMemEnv` lookup theorem for the eventual `while` case, if the induction reaches
  that point

### Checkpoint: 2026-03-07 — both narrowed `arrow` wrappers are now resolved; one origin theorem remains

Build: **clean** (`make lean-build` passes; sorry-only warnings).

What changed:

- `typecheckExpr_lookup_clean_back_of_pc_true` is no longer a direct `sorry`; it is now a
  proved wrapper around `typecheckExpr_clean_lookup_origin_of_pc_true`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1_true` is also no longer a direct `sorry`;
  it is now a proved wrapper using closure inversion plus the same origin theorem
- the generic lookup-back helper
  `assign_memEnv_formula_lookup_eq_of_not_mem`
  was moved into `LeanProofs/TypeSafety.lean`, together with
  `updateLocsetWeak_lookup_eq_of_not_mem`, so the remaining induction can use them without
  `StepFRAssign`-local duplication

Current state of the narrowed `arrow` work:

- the wrapper layer is done
- the only remaining theorem-shaped blocker for this slice is now
  `typecheckExpr_clean_lookup_origin_of_pc_true`

Interpretation:

- the previous two overlapping `arrow` obligations have been successfully collapsed
  into one stronger semantic statement
- no change of proof architecture is needed at this point; the next work is still the
  planned induction over `typecheckExpr`

Next step:

- prove `typecheckExpr_clean_lookup_origin_of_pc_true`
- once that is done, the narrowed `arrow` locations branch is expected to close without
  further redesign

### Checkpoint: 2026-03-07 — `arrow` theorem debt reduced from two obligations to one stronger origin theorem

Build: **clean** on affected files (`TypeSafety`, `StepFRAssign`, `StepFRApp`); full
`lean-build` pending for checkpoint verification.

What changed:

- the generic helper `assign_memEnv_formula_lookup_eq_of_not_mem` was moved into
  `LeanProofs/TypeSafety.lean`
- the previous two `arrow` theorem-shaped obligations
  - `typecheckExpr_lookup_clean_back_of_pc_true`
  - `applyFnTClosure_fresh_lookup_not_clean_of_p1_true`
  have been refactored so that only one stronger theorem remains as a direct hole:
  `typecheckExpr_clean_lookup_origin_of_pc_true`
- the old two statements are now proved wrappers around that stronger origin theorem

Why this is better:

- the remaining proof debt now matches the actual semantic question under poisoned control:
  any final clean memory lookup should come from a clean pre-body lookup
- the fresh and inherited `arrow` subcases are no longer treated as unrelated obligations
- this reduces the local `sorry` surface in `StepFRApp.lean` by one and gives a clearer
  target for the next induction

Next step:

- prove `typecheckExpr_clean_lookup_origin_of_pc_true` by induction on `typecheckExpr`
- use the moved `assign_memEnv_formula_lookup_eq_of_not_mem` helper in the `assign` case
- once that theorem is proved, both current `arrow` wrappers close automatically

### Checkpoint: 2026-03-07 — narrowed `arrow` location proof now reduced entirely to two theorem-shaped obligations

Build: **clean** (no errors; sorry-only warnings).

What changed:

- the app-local fresh-location `arrow` `sorry` in the main locations conjunct is gone
- that branch now dispatches through one reusable closure-body theorem-shaped obligation:
  `applyFnTClosure_fresh_lookup_not_clean_of_p1_true`
- together with the earlier inherited-location theorem
  `typecheckExpr_lookup_clean_back_of_pc_true`, the narrowed `arrow` locations proof no
  longer contains ad hoc local `sorry` branches

What remains for the narrowed `arrow` locations branch:

- `typecheckExpr_lookup_clean_back_of_pc_true`
- `applyFnTClosure_fresh_lookup_not_clean_of_p1_true`

Interpretation:

- this is a better plan state than the earlier mixed local/global situation
- the remaining work is now classified cleanly:
  - one theorem for inherited locations becoming clean under `pc = true`
  - one theorem ruling out fresh final-clean locations under `p1 = true`
- no further widening of the `StepFR_single_run` interface is indicated by the current code

Next step:

- prove `applyFnTClosure_fresh_lookup_not_clean_of_p1_true` first
- then decide whether `typecheckExpr_lookup_clean_back_of_pc_true` can be proved from the
  same underlying typing invariants or needs separate induction

### Checkpoint: 2026-03-07 — `arrow` inherited-location split collapsed to one reusable typing-side theorem; fresh-location branch remains

Build: **clean** (no errors; sorry-only warnings).

What changed:

- the remaining inherited-location `arrow` work in `StepFRApp.lean` was refactored so the
  two local subcases
  - pre-body entry has no guard tag, and
  - pre-body entry has an inactive guard tag
  are no longer separate app-local `sorry`s
- instead, that reasoning is now factored into one reusable theorem-shaped obligation:
  `typecheckExpr_lookup_clean_back_of_pc_true`
- this theorem currently lives in `LeanProofs/StepFRApp.lean` because it depends on
  `qtypCleanUnder` (so it cannot live in `TypeSafety.lean` without introducing the wrong
  dependency direction)

What is now clearer:

- under the strengthened control-poison write semantics, the inherited-location part of the
  narrowed `arrow` blocker is no longer best understood as two ad hoc local proof holes
- the real shape is one generic statement:
  if an inherited location is clean in the post-body typing result under `pc = true`, then
  the corresponding pre-body entry was already clean under the pre-body regime
- the only remaining app-local location hole in the narrowed `arrow` branch is now the
  **fresh-location** case

Plan consequence:

- treat the fresh-location case as the next local `arrow` target
- after that, decide whether `typecheckExpr_lookup_clean_back_of_pc_true` should be proved
  in place in `StepFRApp.lean` or moved into a more shared FR-layer file

### Checkpoint: 2026-03-07 — control-poison write semantics strengthened; `arrow` architecture must be reassessed on the new rules

Build: **clean** (no errors; sorry-only warnings). Implementation tests: **80 passed, 0 failed**.

What changed:

- the language spec, documentation, Lean typechecker, and proof infrastructure were updated
  so writes under poisoned control strip stored predicates instead of preserving them
- concretely:
  - `ref` now stores `AppPred pc P`
  - clean-reference `assign` now stores `AppPred pc P2` / `JoinP AppPred pc P2 P3 = P4`
  - the corresponding Lean typing and proof lemmas were updated to match

Why this matters for the app plan:

- the earlier architectural concern for `arrow` relied on the possibility that an impure
  body under `pc = true` could preserve a guard predicate through a write and thereby make an
  inherited location final-clean-under-regime even when it was not pre-body clean
- that specific route is now blocked by the typing rules
- as a result, the previous Step 5 conclusion
  (“the current unary clause is not enough for `arrow`”) is no longer current guidance; it
  must be re-validated against the strengthened write semantics before we design any new
  unary/body summary

Plan consequence:

- keep the current unary clause added to `StepFR_single_run`; it remains validated for
  `parrow`
- return to `StepFRApp.lean` and reassess the narrowed `arrow` residual cases under the new
  semantics
- only if a real `arrow` blocker survives that reassessment should we reopen the unary
  interface design

Historical note:

- the next two checkpoints below were recorded **before** the control-poison write semantics
  change and are kept as design history, not as current architectural direction

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

5. **Reassess the narrowed `arrow` residual cases under the strengthened control-poison write semantics**
   - Re-check the inherited dirty-to-clean branch.
   - Re-check the fresh-location branch.
   - Treat the old “guard preserved through poisoned-control write” route as obsolete unless
     it reappears in a different form under the new rules.
   - Deliverable:
     an updated classification of the remaining `arrow` obligations in `StepFRApp.lean`.

6. **Try to finish the remaining `arrow` holes locally before widening the unary interface**
   - Prefer local proof closure in `StepFRApp.lean` using the strengthened typing rules and
     the current `PreservesInheritedCleanLocsOneRun` interface.
   - If the inherited branch now reduces to the already-known inherited-clean pattern, close
     it directly.
   - If the fresh branch simplifies to a local impossibility argument, close it directly.

7. **Only if `arrow` still blocks, freeze the exact remaining missing fact**
   - Write down the precise statement that is still missing after the semantic change.
   - Do not reuse the old pre-change “final-clean inherited location” summary unless the new
     rules still force it.
   - Stop point:
     freeze the exact missing statement before changing `StepFR` interfaces again.

8. **If needed, redesign the unary/body summary from the new semantics, not the old ones**
   - Any new unary fact should be justified by the post-change typing rules, not by the
     pre-change guard-preservation path.
   - Reuse `StepFRAssign` only if the new residual `arrow` goal actually has the same shape.

9. **Then return to proving unary facts in `StepFR`**
   - First prove whatever unary facts remain genuinely necessary after the new `arrow`
     reassessment.
   - Keep the current `PreservesInheritedCleanLocsOneRun` result for the `parrow` path
     unless a replacement clearly subsumes it.

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
