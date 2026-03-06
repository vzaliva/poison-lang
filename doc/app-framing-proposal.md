# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

It assumes the typing-side fix from [app-typing.proposal](/work/doc/app-typing.proposal) is
accepted, so the old dirty-internal `resultAgreesIfClean` issue is no longer the main
problem.

Scope of this note:

- in scope: the post-body `agreeOnClean` locations conjunct in the different-body app
  branches
- out of scope: the earlier body-IH disconnect and final-result predicate issue

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

One useful narrowing is that these branches also force the **body typing `pc` to be
poisoned**:

- dirty-internal case: `p = true`, so `join p join p1 pc = true`
- outer-not-clean case: for function-typed callees this is the `p1 = true` family, so
  again `join p join p1 pc = true`

That poisoned-body-`pc` fact is likely important for the proposal below.

## 3. Why The Shared-Body Case Works

There is already a successful transport pattern for the shared-member case in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), centered around
`join_transport_agreeOnClean_from_member`.

That pattern works because both runs can be traced back to one common source member.
Then the proof can show:

- the clean final location came from that one source member, or
- it was unrealized in both runs

And if the source member does not contain the location in its memory typing environment,
the proof can use:

```lean
theta_not_contains_if_not_in_memEnv :
  runtimeInstantiatesCtx ctx μ ρ θ →
  ¬ ctx.memEnv.contains l →
  θ.lookup l = none
```

That is enough to close the `both_unrealized` branch in the shared-source situation.

## 4. Why The Different-Body Case Is Hard

In the remaining app branches, the two runs may execute **different bodies**.

That changes the proof shape in one crucial way:

- there is no longer one common source member from which both runs inherit their location
  facts

So the old transport pattern no longer gives what we need.

More concretely, the narrowed proof now reduces the hard part to explicit post-body
realization-map cases:

- `θ₀_body.lookup l = none`, `θ₁_body.lookup l = none`
- `θ₀_body.lookup l = none`, `θ₁_body.lookup l = some _`
- `θ₀_body.lookup l = some _`, `θ₁_body.lookup l = none`
- `θ₀_body.lookup l = some _`, `θ₁_body.lookup l = some _`

The first case is easy:

- `none / none` closes immediately with `agreeLocUnder.both_unrealized`

The real blocker is the other three cases.

## 5. What We Still Do Not Know

The proof currently lacks exactly the facts needed to rule out or handle the nontrivial
lookup cases.

What is missing is not about the final app predicate anymore. It is about **post-body
frame behavior**:

- can a previously unrealized clean location become realized in only one run?
- if both runs realize a clean location, must it come from a pre-existing clean source?
- if a clean location was not written by the body, do the heap contents at its realized
  address stay the same?
- how do we prove those facts when the two runs executed different bodies?

This is why `wfExtendsMap` is not enough:

- it preserves existing realizations
- but it does **not** prove that `none` stays `none`

So it cannot by itself close the asymmetric `none / some` cases.

## 6. Why The Typing Fix Does Not Solve This

The typing fix from [app-typing.proposal](/work/doc/app-typing.proposal) removes one old source
of final-result agreement pressure:

- the final non-function app result no longer stays clean only because of a retained
  guard predicate from an internally dirty callee

But that change says nothing about:

- realization-map growth
- fresh realization of logical locations
- writes to pre-existing clean addresses
- preservation of agreement on clean locations across two different body executions

So the typing fix is orthogonal to this blocker.

It removes the old final-result problem, but the locations conjunct still needs a real
frame argument.

## 7. Why "Allow `some / none` If Poisoned" Is Not A Simple Fix

Probably not.

The reason is that this note is already about locations that satisfy:

- `ctx.memEnv.lookup l = some qt`, and
- `qtypCleanUnder R qt`

So these are exactly the locations that the step theorem is treating as **clean enough
to require agreement**.

There are two important cases:

- if `qt` is simply dirty and **not** clean-under-regime, then `agreeOnClean` does not ask
  for anything about `l` in the first place
- if `qt.poison = true` but `qtypCleanUnder R qt` holds via a guard, then the theorem is
  still deliberately treating `l` as clean enough to require location agreement

So allowing `some / none` just because the underlying `qt.poison` bit is `true` would mean:

- a location may count as clean-under-regime,
- but still be realized in only one run

That is not a local proof trick. It is a semantic weakening of what `agreeOnClean` means.

In the current design, `agreeLocUnder` intentionally has only:

- both realized with agreeing values, or
- both unrealized

There is no asymmetric constructor, and that is consistent with the intended reading:
for a location that still counts as clean, the two runs must line up on whether that
logical location exists and, if it exists, what value it carries.

So:

- allowing `some / none` for truly dirty locations is unnecessary, because those locations
  are already outside `agreeOnClean`
- allowing `some / none` for guard-clean locations would be a broader spec change, not a
  narrow fix for this blocker

That is why the current blocker still points toward a frame lemma, not toward relaxing
`agreeLocUnder`.

## 8. Proposal

The most plausible next step is still a **narrow app/body frame argument**, not a broad
new FR reformulation.

The most useful refinement is to specialize the missing lemmas to the branches where the
**body `pc` is already poisoned**.

Why that might help:

- in exactly the branches discussed in this note, the body is typed under poisoned `pc`
- under poisoned `pc`, the existing typing rules already push direct memory effects
  toward dirty memory typing:
  - `ref e` stores `join pc p { P }`, so with poisoned `pc` the new cell is poisoned
  - assignment updates also join with `pc`, so writes under poisoned `pc` become poisoned
  - assignment through poisoned references already forces `poisoned { no_pred }`

So a location that is still **clean** after such a body probably has a much narrower
explanation:

- it was inherited from the pre-body clean context, not created or retyped as clean by
  the poisoned body

That suggests the missing work may reduce to the following two lemmas.

### A. Static inheritance lemma under poisoned body `pc`

If the body is typed under poisoned `pc` and a location `l` is still clean in the
post-body memory typing environment, then `l` already came from the pre-body clean memory
typing environment.

Informally:

- poisoned-body effects do not create new **clean** locations
- poisoned-body writes do not leave a touched location **clean**

If true, this would immediately rule out many candidate sources of the bad `some / none`
cases.

This looks especially promising on the parrow side, where pure typing already constrains
the post-body memory typing environment more tightly.

### B. Typed-evaluation preservation lemma for inherited clean locations

This should **not** be phrased as a runtime-only lemma, because "clean" is not a runtime
notion. It is a property of:

- a location's qualified type in the typing context, together with
- `qtypCleanUnder` for the relevant regime

So the second lemma has to combine:

- the pre-body typing context
- the post-body typing result
- the body evaluation result
- and the realization maps / memories produced by that evaluation

The intended shape is:

- assume `l` is inherited from the pre-body context by Lemma A
- assume `l` is clean in the post-body context
- assume the body evaluation and typing evidence produced by the app proof

Then conclude exactly what the locations conjunct needs for that `l`, namely either:

- `θ_body.lookup l = none` on both runs, or
- both runs realize `l` and the realized heap values satisfy `agreeLocUnder`

Informally:

- once Lemma A says that `l` is an inherited clean location, `l` should be treated as
  part of the pre-body clean state that the two runs were already required to agree on
- it should not break agreement on this inherited clean `l`
- so the combined typing-plus-evaluation evidence should force one of the two acceptable
  outcomes for `l`:
  - either both runs still leave `l` unrealized
  - or both runs realize `l`, and because clean memory entries are integer-typed here,
    the realized integers must be exactly equal

This is especially needed on the arrow side, where evaluation may still allocate or write
elsewhere.

So the proposal is not to prove a fully general frame theorem first. It is to try a
strictly narrower path:

1. prove that under poisoned body `pc`, any post-body **clean** location must be inherited
2. prove typed-evaluation preservation only for those inherited clean locations

If both steps work, the location blocker is probably just missing lemmas rather than a
deeper design problem.

### Alternative proposal: strengthen `StepFR` itself

There is also a wider but potentially cleaner option:

- instead of proving Lemma A and Lemma B as standalone facts outside the main step
  invariant, add the needed clean-location preservation fact directly to the `StepFR`
  package

High-level idea:

- make inherited-clean-location preservation a first-class `StepFR` obligation, with the
  usual step-style shape of:
  - an assumption about the incoming state/context
  - and a matching guarantee about the outgoing state/result

Why this might help:

- each syntax-case proof would carry the same preservation fact together with the rest of
  the `StepFR` pack
- the app case could consume that fact directly instead of proving separate induction
  lemmas on the side
- the strengthened invariant could reuse other data already threaded through `StepFR`,
  such as:
  - `agreeOnClean`
  - `runtimeInstantiatesCtx`
  - `wfExtendsMap`
  - `consistentWithRegime`

Potential advantage:

- avoids having to prove the framing property by a separate large syntax induction that
  duplicates much of the structure already present in the `StepFR` proof

Potential cost:

- this is a wider-scope change
- it would affect the statement of `StepFR` and therefore many downstream lemmas and case
  proofs, not just `stepFR_app`
- it also cuts against the current preference to keep the fix app-local if possible

So this should be treated as an explicit alternative, not the default plan:

- if the two-lemma route stays narrow and local, it is likely preferable
- if the two-lemma route starts turning into a parallel whole-syntax preservation
  development anyway, then strengthening `StepFR` may become the cleaner design

## 9. Practical Reading Of The Open Cases

The remaining open lookup cases can be read informally like this:

- `none / some`:
  explain why one run cannot suddenly realize a location that still counts as clean at
  the end unless the other run can match it
- `some / none`:
  symmetric version of the same problem
- `some / some`:
  explain why the two realized addresses still carry the same integer for that clean
  location after different body executions

So the blocker is not about syntax, closure typing, or final app-result predicates
anymore.

It is now purely about **preserving clean-location agreement across two different body
executions**.

## 10. Bottom Line

Assuming the typing fix from [app-typing.proposal](/work/doc/app-typing.proposal), the remaining
conceptual blocker in `stepFR_app` is:

- prove the locations conjunct of `agreeOnClean` after two different body executions

The shortest plausible route is:

- a narrow static source lemma for clean post-body locations, plus
- a narrow typed-evaluation preservation lemma for inherited clean locations

If that route turns into a demand for whole-language generic preservation cleanup, then
the blocker is larger than this note assumes and should be escalated back to
[app-proof-plan.md](/work/doc/app-proof-plan.md).
