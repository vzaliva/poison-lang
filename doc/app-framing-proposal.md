# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

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

The shared-body case already has the right proof shape in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), via
`join_transport_agreeOnClean_from_member`.

That works because both runs can be traced back to one common source member, so for a
clean final location the proof can show either:

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

So the gap is a real unary clean-location preservation fact, not a missing transport
step.

## 4. Proposal

Current status after the first validation gate:

- the inheritance-only version of Lemma A is false
- under poisoned `pc`, `typecheckVar` can preserve a guard predicate when its tag is
  unknown, `typecheckNewRef` stores that predicate on the fresh location, and
  `joinMemEnvsStrong` preserves it on two-sided entries
- so a fresh clean location can survive the final join if both bodies allocate it with
  matching guard predicates

This changes the shape of the decision.

### Approach 1: restated app-driven helper lemmas

Approach 1 remains plausible, but no longer as a pure "every clean final location is
inherited" story.

Informal reading:

- first classify each clean final location as either inherited from the pre-body context
  or fresh on both sides of the join
- then handle inherited locations with unary preservation facts, and handle symmetric
  fresh locations directly in the `some / some` branch

Required pieces:

1. a static classification step for clean final locations: inherited or symmetric fresh
2. a unary preservation lemma for one inherited clean location in one body run
3. a direct `some / some` argument for the symmetric fresh case
4. a short recombination step that rebuilds `agreeLocUnder`

What failed:

- the earlier inheritance-only Lemma A is false as stated
- the concrete counterexample is `newRef (var x)` under poisoned `pc`, with `x`
  carrying a preserved guard predicate and both body typings allocating the same fresh
  logical location

What still looks promising:

- the symmetric fresh case no longer threatens the asymmetric `none / some` branches;
  it lands directly in `some / some`
- for `parrow`, the fresh-location classification is no longer the immediate blocker:
  pure bodies preserve memory / `nextAddr`, and `applyPFnTClosure` keeps typed memory
  inside the pre-body memory typing
- the current blocker is instead the inherited-location `none → none` bridge:
  `StepFR_single_run` only returns an existential `θ'`, and its current interface does
  not imply that an old unrealized inherited location stays unrealized
- the `arrow` write-preservation argument for already-realized clean locations remains a
  later risk point, but it is no longer the first blocking one

Costs:

- Approach 1 is no longer a pure unary decomposition
- it needs an explicit symmetric-fresh case split at the final join
- it may also need a new theorem about realization-map growth that is not exposed by the
  current `StepFR_single_run` interface
- the direct `some / some` fresh case may still require nontrivial value agreement work

### Approach 2: broaden `StepFR` more aggressively

The inheritance-only `StepFR` invariant sketched earlier is false for the same reason as
the original Lemma A.

So a viable `StepFR` route would need a broader invariant that distinguishes:

- inherited clean output locations
- clean output locations freshly introduced by the step

This is still a possible fallback, but it is now more expensive than the original
version because the broader invariant would have to be maintained across the whole
`StepFR` proof, not just exposed from the existing unary output.

Current recommendation:

- keep Approach 1 as the primary path, but only in the restated inherited-vs-symmetric-
  fresh form
- treat the missing unary `θ` bridge as the immediate go/no-go item for Approach 1
- treat Approach 2 as fallback only if that broader two-case story looks conceptually
  right but too awkward to keep app-local


## 5. Action Plan

Objective:

- finish the different-body app location proof by a restated Approach 1

Do not do this:

- do **not** try to prove the old inheritance-only Lemma A
- that statement is false and should be treated as dead

Current status:

- steps 1-2 of the earlier plan are no longer the immediate blocker for `parrow`
- the current blocker is step 3: there is no bridge yet from `StepFR_single_run`'s
  existential `θ'` to "old unrealized inherited locations stay unrealized"
- this is not a cosmetic gap in the proof script; the current interfaces really allow
  countermodels where an old inherited location moves from unrealized to realized while
  preserving `wfExtendsMap`, `wfTypeContext`, and `runtimeInstantiatesCtx`

Execution sequence:

1. Freeze the static side of the plan.
   Deliverable:
   a precise statement that classifies each clean final location as either:
   - inherited from the pre-body memory typing environment, or
   - fresh on both sides of the join
   Go/no-go:
   if this classification statement cannot be written cleanly, stop and reassess the
   whole Approach 1 path.

2. Resolve the missing unary `θ` bridge before doing more branch work.
   Deliverable:
   either:
   - a local theorem showing that an inherited location unrealized before one body run
     stays unrealized after that run, or
   - a clear decision that this cannot be derived from the current unary interface
   Why the current interface is insufficient:
   - `wfExtendsMap` preserves existing `some` bindings but says nothing about preserving
     `none`
   - `runtimeInstantiatesCtx` permits realizing any old typed location
   - `freshLoc_not_realized` only applies to fresh locations `l >= nextLoc`, not to old
     inherited locations `l < nextLoc`
   Go/no-go:
   if this bridge cannot be obtained locally, treat that as the main signal that
   Approach 1 is blocked on the current interfaces.

3. Only after the unary `θ` bridge is resolved, return to the symmetric-fresh branch.
   Deliverable:
   a proof sketch, or a small prototype lemma, for the `some / some` case created by a
   fresh-on-both-sides location.
   What must be shown:
   - both runs realize the location
   - the realized integers can be related strongly enough to build `agreeLocUnder`
   Go/no-go:
   if this already expands into a large new binary proof, treat that as evidence that
   Approach 1 is losing its locality.

4. Use `parrow` as the validation branch for the inherited case.
   Deliverable:
   close the outer-not-clean `parrow` location hole using:
   - the resolved unary `θ` bridge for inherited locations, and
   - the symmetric-fresh `some / some` argument if needed
   Reason:
   - pure evaluation removes the write-preservation risk
   - success here validates the restated proof shape before more `arrow` investment

5. Attack the inherited-location write-preservation half for `arrow`.
   Deliverable:
   a proof sketch or prototype lemma for:
   - if an inherited clean location was already realized before the body, the `arrow`
     body does not disturb the stored integer in the way that matters for
     `agreeLocUnder`
   This is the main risk point.
   Go/no-go:
   if this turns into broad assignment-style heap-update analysis, that is the main
   signal to switch away from app-local lemmas.

6. Recombine for the narrowed outer-not-clean holes.
   Deliverable:
   direct construction of final `agreeLocUnder` from:
   - the inherited-case unary results, or
   - the symmetric-fresh `some / some` argument, plus
   - the pre-body `agreeLocUnder` fact where relevant

7. Only then lift the machinery into dirty-internal arrow/parrow branches.
   Deliverable:
   reuse the location-framing work inside those broader branch proofs.
   Reminder:
   - these branches still have non-location obligations
   - the dirty-internal `parrow` branch also has a non-vacuous
     `resultAgreesIfClean` obligation

Fallback:

- if the unary `θ` bridge cannot be obtained from the current local interfaces, that is
  the strongest evidence so far for moving to a broader `StepFR`-level invariant; if
  that happens, update [app-proof-plan.md](/home/lord/src/poison-lang/doc/app-proof-plan.md)
  before continuing
