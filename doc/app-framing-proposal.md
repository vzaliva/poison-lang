# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

Status:

- this is a focused blocker memo, not the active planning document
- the active next-step plan now lives in `doc/app-proof-plan.md`
- design history for attempted framing routes lives in `doc/app-proof-history.md`

Scope of this note:

- in scope: the post-body `agreeOnClean` locations conjunct in the different-body app
  branches
- in scope for dirty-internal app branches: only the locations/framing subproblem inside
  the broader branch `sorry`
- out of scope: other app-proof issues

## 1. Exact Remaining Obligation

The remaining target is the **locations half** of `agreeOnClean`:

```lean
def agreeOnClean ... : Prop :=
  (∀ l qt, ctx.memEnv.lookup l = some qt → qtypCleanUnder R qt →
    agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)) ∧
  ...
```

and the relevant location relation is:

```lean
inductive agreeLocUnder ... : (Loc × QTyp) → Prop where
  | agree_values ...
      (hreal1 : θ₁.lookup l = some a₁)
      (hreal2 : θ₂.lookup l = some a₂)
      ...
  | both_unrealized ...
      (hreal1 : θ₁.lookup l = none)
      (hreal2 : θ₂.lookup l = none)
```

So for each clean post-body location, the proof must show **one** of only two things:

- both runs still leave the location unrealized, or
- both runs realize it and the two heap values agree in the required way

There is no third escape hatch.

Because memory stores only integers in this language, the second case is simpler than it
looks:

- once both runs realize the clean location, the remaining value-side obligation is just
  equality of the two realized integers

The proof still has to establish the realization facts first, but there is no richer
heap-value structure hiding here.

## 2. Where This Arises In `stepFR_app`

The framing blocker does **not** arise in every app branch.

There are really two phases in the proof:

- first, `stepFR_app` tries to recover a **shared body** for the two runs
- only if that fails does it switch to two separate single-run body proofs

The shared-body path is available when the callee-side function agreement is strong
enough to say:

- both runs selected the same closure body
- with agreeing captured environments on the clean captured entries

That is the easy case from the framing point of view, because both runs are then traced
through one common body result, and the existing transport lemmas can reuse one common
source member.

The blocker in this note starts only when that shared-body recovery fails.

Concretely, that happens in two situations inside `stepFR_app`:

### A. Dirty-internal function case

Here the callee is still outer-clean enough to enter function agreement, but its
**internal arrow poison is dirty**.

Then FR uses `dirty_internal_arrow` / `dirty_internal_parrow`, which intentionally do
**not** give:

- a common body
- a common binder
- captured-environment agreement

So the proof cannot continue with one common body IH.

### B. Outer-not-clean function case

Here the callee is not even clean enough to enter the strong function-agreement path at
all:

- the proof is in the `¬ qtypCleanUnder result1.qualType` fallback
- for function-typed callees, this is the branch that corresponds to outer poison being
  too dirty to recover shared-body agreement

Again, there is no common body witness.

### Program situations behind those branches

Semantically, both branches cover the same kind of runtime phenomenon:

- the same source callee expression may evaluate to different runtime closures in the two
  runs

That can happen when the function value came from dirty control or other dirty function
selection earlier, for example through a previously merged typing-closure set.

Once the proof is in either fallback family above, it must switch to two separate
single-run body proofs.

That recovers useful unary facts for each run, but at the end we still need to prove
`agreeOnClean` for the joined app result. For locations, that means:

- take a location `l` that is still typed as clean in the final post-body context
- show that the two post-body realization maps and memories still line up on `l`

This is exactly the part that stays open in the narrowed different-body branches.

There are therefore four relevant `sorry` sites behind this discussion:

- two narrowed location-only holes in the outer-not-clean arrow/parrow families
- two broader dirty-internal arrow/parrow branch holes where the same locations issue
  reappears as one sub-obligation, but does not by itself close the full branch

One useful narrowing is that these branches also force the **body typing `pc` to be
poisoned**:

- dirty-internal case: `p = true`, so `join p join p1 pc = true`
- outer-not-clean case: for function-typed callees this is the `p1 = true` family, so
  again `join p join p1 pc = true`

That poisoned-body-`pc` fact is likely important for the proposal below.

## 3. Why Existing Transport Stops Here

Final recombination is no longer the blocker.

The shared-body case already has the right proof shape in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), via
`join_transport_agreeOnClean_from_member`.

That lemma already packages the joined clean-location proof once the branch can supply
either:

- a source-member lookup for the clean final location, or
- final `θ₀.lookup l = none ∧ θ₁.lookup l = none`

In the shared-body case this is easy, because both runs can be traced back to one common
source member, so for a clean final location the proof can show either:

- it came from that shared source member, or
- it was unrealized in both runs, using `theta_not_contains_if_not_in_memEnv`

The different-body case loses exactly that common source.

Once the two runs execute different bodies, the narrowed proof is forced into explicit
post-body realization-map cases:

- `none / none`
- `none / some`
- `some / none`
- `some / some`

The `none / none` case is easy. The blocker is the other three.

What is still missing is not a final-result typing fact. It is a **frame fact** about
clean locations across two different body executions:

- can an unrealized clean location become realized in only one run?
- if both runs realize a clean location, must it come from a pre-body clean source?
- if a clean location is realized before the body, can either run overwrite the stored
  integer?

This is also why `wfExtendsMap` is insufficient:

- it preserves existing realizations
- it does not prove `none` stays `none`

So the remaining gap is a real unary clean-location preservation fact, not a missing
final recombination step.

## 4. Current Outcome

The narrowed different-body app proof is no longer blocked on final recombination.

The remaining blocker is the unary fact needed to feed that recombination:

- when pre-body agreement gives `both_unrealized` for an inherited clean location, the
  chosen post-body maps must also leave that location unrealized

That fact is not available from the current local interfaces:

- `StepFR_single_run` only exposes an existential post-run `θ'`
- `wfExtendsMap` preserves existing `some` bindings, not `none`
- `runtimeInstantiatesCtx` permits realizing old typed locations
- `freshLoc_not_realized` only applies to fresh `l >= nextLoc`
- the only obvious local `parrow` escape hatch, reusing the pre-body maps as final
  witnesses, also stalls because the library has extension transport such as
  `valueHasETyp_extends`, but no reverse/shrink transport for `valueHasETyp` or
  `valueConsistentWithRegime`

So this note stops here: the next move is no longer an app-local proof edit inside
`stepFR_app`.


## 5. Action Plan

Stop condition reached:

- do not continue local proof edits in `stepFR_app` on this path
- move the active plan to
  [app-proof-plan.md](app-proof-plan.md)
- the next track should strengthen broader unary proof infrastructure so the needed
  post-run realization-map fact is exposed directly, rather than reconstructed inside the
  app branches
