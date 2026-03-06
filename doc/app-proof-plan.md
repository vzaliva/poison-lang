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

### Checkpoint: 2026-03-06 — app-local framing route stopped; move to broader unary infrastructure

Build: **clean** (no errors; sorry-only warnings).

What is settled:

- shared-member transport is good enough
- final recombination is not the blocker anymore:
  `join_transport_agreeOnClean_from_member` already packages the joined clean-location proof
  once a branch can supply either a source-member witness or final `none / none`
- the remaining different-body app blocker is the unary fact needed to produce that final
  `none / none` for inherited clean locations

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
  needs, rather than reconstructing it ad hoc inside the app branches

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

1. **Freeze the new unary property and where it lives**
   - Decide whether the new fact belongs on `StepFR`, `StepFR_single_run`, or a new wrapper
     theorem around the body-execution pipeline.
   - Keep the property scoped to inherited clean locations; the symmetric-fresh case still
     belongs to the app proof.
   - Deliverable: one precise theorem statement that the rest of the fallback path will aim
     to prove and consume.

2. **Attack the semantic risk cases first**
   - Validate the target property against the expression forms that can actually realize or
     overwrite memory: at minimum `newRef` and assignment-style updates.
   - Do this before committing to broad theorem plumbing.
   - Go/no-go: if the target property fails, or only survives in a much weaker form, restate
     it before touching the wider proof infrastructure.

3. **Thread the property through the unary pipeline**
   - Extend the chosen unary interface so body-step results carry the new preservation fact.
   - Update the helper layer used by `applyFnTClosure` / `applyPFnTClosure` so the app proof
     can consume the strengthened result directly.
   - Avoid reverse/shrink witness transport as the primary mechanism; the goal is to expose
     the needed post-run fact directly.

4. **Return to the app holes in risk order**
   - Close the outer-not-clean `parrow` location hole first.
   - Then close the outer-not-clean `arrow` location hole.
   - Only after those are done, reuse the same strengthened unary fact inside the broader
     dirty-internal arrow/parrow branches.

5. **Only widen further if the strengthened unary route proves coherent**
   - If proving the new interface starts forcing unrelated invariants or major theorem
     reshaping outside the body-execution path, pause and reassess before paying that cost.

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
- `wfExtendsMap`
- `runtimeInstantiatesCtx`
- `freshLoc_not_realized`
- `applyFnTClosure`
- `applyPFnTClosure`
- `valueHasETyp_extends`
