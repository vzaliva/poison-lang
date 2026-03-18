# Lessons From The `mode 3` Proof Attempt

This note is a retrospective for restarting the `mode 3` `if` proof from
`main`. It is based on:

- the full `issue-128-rebase-invariant` history since it diverged from
  `issue-128-rebase-main`
- the current diff between that branch and `main`
- the evolution of `doc/issue-128-proposal.md`
- the relevant source on `main` (`Typecheck`, `StepFR`, `StepFRIte`,
  `FaultRobustness`, `RegimeConsistency`, `TypeSafety`, and the Ott spec)

It is intentionally self-contained. It does not assume access to the
abandoned branch.

Most other branch-vs-main drift (while-loop work, parser/doc changes, general
proof churn outside the guard-coherence path) was not relevant to the `mode 3`
`if` blockage and is intentionally omitted here.

## 1. Current `main` starting point

On `main`, the remaining two `sorry`s are both the `mode 3` / unknown-regime
case for `if`:

- `stepFRSingleRun_ite_mode3_maskedReg`
- `stepFR_ite_mode3`

They correspond to the branch of `typecheckIf` where:

- `matchGuard e1 ctx.memEnv ctx.varEnv fuel = .ok (k, deps)`
- `ctx.regime.lookup? k = none`

and `typecheckIf` still typechecks the branches under:

- `tagEnv[k := true]`, `regime.map[k := true]` for the then branch
- `tagEnv[k := false]`, `regime.map[k := false]` for the else branch

with the final result joined conservatively.

One subtlety on `main` matters a lot:

- `Regime.lookup? k` is not raw `map.get?`.
- It first checks `k < regime.bound`.
- So an insert into `regime.map` is visible only when `k < bound`.

That forces a real split between:

- visible activation: `k < bound`
- invisible activation: `k >= bound`

Any proof that ignores that split eventually runs into a wall.

## 2. Main conclusion

The branch work strongly suggests that the two remaining `sorry`s on `main`
are not just missing local tactics.

The current proof interfaces on `main` are too weak for the existing `mode 3`
typing rule. In particular:

- the old single-run theorem is too weak to prove the `mode 3` helper
- the two-run theorem has an additional cross-run gap even after the
  single-run issue is fixed

More bluntly: with the current `mode 3` rule, the proof obligation is about
global tag-wide de-poisoning, but the existing hypotheses only justify a fact
about one matched owner.

## 3. Root cause

### 3.1. `mode 3` de-poisons by tag, not by owner

`matchGuard` proves that one owner with tag `k` matched the condition.
But in `mode 3`, once the branch context inserts `k := true` or `k := false`,
the typechecker treats every carrier with guard tag `k` as affected.

That is the semantic jump that the current `StepFR` premises do not justify.

The simplest bad shape is:

```text
if (x == x) then y else 0
```

where:

- `x` is clean enough for `matchGuard` to succeed
- `y` is dirty
- `x` and `y` carry the same guard information for tag `k`
- the outer regime satisfies `R.lookup? k = none`

The then-branch context sets `k := true`, so `y` becomes clean by tag, even
though the runtime check only looked at `x`. At runtime the result is still
the actual value of `y`. Two runs can therefore disagree on the result even
though the result is typed clean.

This is the basic soundness problem.

### 3.2. `agreeOnClean` is too weak before the branch

`agreeOnClean` only constrains entries already clean under the pre-branch
regime. In `mode 3`, the interesting tag satisfies `R.lookup? k = none`, so
the relevant carriers are not clean yet. That means the pre-branch two-run
hypothesis gives no cross-run agreement for them.

So even if each run is internally coherent, that does not imply the two runs
agree on the newly activated `k`-carriers.

### 3.3. `guardOnly` is a real gap, not a corner case

This turned out to be one of the most important findings.

On `main`:

- `matchGuard` only matches `guardClosure`, never `guardOnly`
- `typecheckVar` and `typecheckDeref` de-poison both `guardClosure k ...` and
  `guardOnly k`
- `qtypCleanUnder` treats `guardOnly k` as clean when `R.lookup? k = some true`
- but `locsRegime.guardOnly_ok` and `varsRegime.guardOnly_ok` impose no value
  constraint at all

So `guardOnly` can be cleaned by `mode 3` without any semantic relation to the
matched owner.

Also, `guardOnly` is not just a join artifact. It is used deliberately to
model linked values. Removing its de-poisoning would lose intended precision.

### 3.4. `wfTagMeaningCtx` does not solve `guardOnly`

It was tempting to reuse the existing tag-meaning infrastructure and hope that
it already pins down the relevant descriptor for `guardOnly k`. That is false.

`wfTagMeaningCtx` only constrains `guardClosure`-style descriptor-carrying
entries. It is effectively vacuous for `guardOnly`.

So any repair that needs a descriptor behind `guardOnly k` must add that fact
explicitly somewhere else.

### 3.5. `k >= bound` is not a nuisance; it changes the proof shape

When `k >= ctx.regime.bound`, the branch-local insert into `regime.map` is
invisible through `Regime.lookup?`.

That creates the exact mismatch:

- `tagEnv[k] = true` or `false` in the branch context
- but `regime.lookup? k = none`

This breaks the ordinary unmasked `regimeConsistentWithCtx` interfaces.
The branch only got past this by using masked variants of the interface for
the `k >= bound` cases.

### 3.6. Closure depth matters

A top-level invariant about tags in `ctx.varEnv` and `ctx.memEnv` is not
enough. Closure application can expose captured environments that were not
top-level before, and `newRef` can later copy their guard tags into memory.

This is why the obvious boundedness invariant
`predTagsBoundedInCtx` turned out to be false as a preserved property.

The concrete obstruction found in the branch was:

- start with `regime.bound = 0`
- keep a function in the context whose captured environment contains
  `guardOnly 5`
- apply the function so the captured variable becomes visible in the body
- then `newRef` that value

The result contains a guard-tagged memory cell with tag `5`, but the regime
bound is still `0`.

So any successful invariant has to account for deep captured values, not only
top-level bindings.

### 3.7. Separate deep facts do not compose well after joins

Another deep obstruction came from joined function closures.

After `joinETyps`, the same apparent closure shape may be represented by
multiple `FnTClosure.regular` entries with different captured environments.
That means two separately-produced deep properties can choose different
captured environments and fail to line up.

In practice, this killed attempts to prove one deep fact for regime reasoning
and another deep fact for canonical/coherence reasoning and then combine them
later. The branch only made progress once those facts were bundled together.

## 4. What seemed necessary if we keep the current `mode 3` rule

The branch did not finish the two-run proof, but it did identify a coherent
repair direction. The following ingredients looked close to necessary, not
just convenient.

### 4.1. A runtime coherence invariant keyed by guard information

The successful direction was to add a global runtime invariant saying, in
effect:

- all live carriers with the same guard information denote the same runtime
  value

The branch represented this by a canonical witness function
`canon : Tag -> GuardDesc -> Value`, with a coherence predicate of the form:

- `guardClosure k d` carriers must equal `canon k d`
- `guardOnly k` carriers must equal `canon k d` for some `d` with
  `tm.lookup k = some d`

The exact names on the branch were not the important part. The important part
was that the proof needed an explicit semantic object witnessing the shared
value behind a tag/descriptor.

### 4.2. The witness must be shared across the two runs

Per-run existential witnesses are not enough.

If run 0 has `canon0 k d = x0` and run 1 has `canon1 k d = x1`, nothing
relates `x0` and `x1`. That still allows cross-run disagreement.

This was a real blocker. The branch initially tried per-run coherence and
found a counterexample-shaped obstruction immediately. Progress resumed only
after switching to a shared witness for both runs.

### 4.3. `guardOnly` must be covered by the same coherence story

Trying to repair only `guardClosure` is insufficient. Any coherence predicate
must explicitly cover `guardOnly` as well, because `mode 3` can clean it.

### 4.4. Guard-tagged memory realization must be a separate premise

The proof repeatedly needed:

- if `ctx.memEnv` says a memory cell carries guard tag `k`, then `θ` already
  realizes that cell

This is not derivable from the existing initial-state assumptions on `main`.
`runtimeInstantiatesCtx` is one-way on memory (`θ -> memEnv`), not the reverse.
And when `R.lookup? k = none`, `consistentRegimeSpec` is vacuous at tag `k`.

So a repair that keeps the current typing rule probably needs a new explicit
premise for guard-tagged memory realization.

### 4.5. The deep closure invariant has to be bundled

The branch only got traction after threading one combined deep property
through recursive proofs, bundling:

- captured-vars regime facts
- canonical/coherence facts
- captured-vars typing facts

Trying to reconstruct the combination later was repeatedly blocked by closure
member-matching problems after joins.

### 4.6. Post-state monotonicity of the witness is needed

Even after evaluating the condition `e1`, the proof still needs to transfer
facts obtained from the matched owner before the branch to the post-`e1`
state used by the branch proof.

That required an output-side monotonicity property:

- the post-state canonical witness must preserve the equalities established by
  the pre-state witness

Without such a property, the transfer principle lands on the wrong witness.

### 4.7. The masked interface needs the stronger premise `masked k -> k >= bound`

An older idea was to keep the mask semantics in terms of
`masked k -> regime.lookup? k = none`. That was not strong enough.

The branch eventually switched to:

- `masked k -> k >= regime.bound`

This is better aligned with the actual meaning of masked tags in `mode 3`:
they are exactly the tags whose regime inserts are invisible because of the
bound check.

### 4.8. The old single-run theorem on `main` is the wrong vehicle

The old single-run stack on `main` only threads `consistentWithRegimeMasked`.
That is not enough to feed the stronger canonical/coherence proof.

The branch eventually proved a stronger canonical single-run theorem in
parallel, rather than trying to derive it from the old one.

So if the restart keeps the strong-invariant route, it should expect to
replace or bypass the old single-run theorem, not merely finish its `sorry`.

### 4.9. A small typechecker change that likely helps: stricter `vlet` shadowing

The branch strengthened `typecheckVlet` to reject shadowing any outer
`guardClosure` binding, not only an already-active one.

This was not the core `mode 3` issue, but it removed one source of canonical
witness instability around rebinding and restored closures. It looked like a
reasonable supporting change.

## 5. Candidate proof-side changes worth reconsidering

If a restart keeps the current `mode 3` typing rule, the following proof-side
changes looked the most defensible.

### 5.1. Strengthen the step theorem interface

The branch moved toward a stronger step theorem carrying:

- the shared canonical witness
- coherence for both runs under that witness
- deep captured-env coherence/regime facts
- guard-tagged memory realization

This was expensive, but it matched the real proof obligation.

### 5.2. Add targeted helper lemmas for the visible `k < bound` cases

Two visible-branch helpers were especially valuable conceptually:

- a lemma that activates a previously-vacuous tag in `consistentWithRegime`
  once the branch makes `k` visible
- a lemma that transfers the matched-owner fact from the pre-condition witness
  to the post-`e1` witness

Those helpers did not solve the whole theorem, but they localized the most
delicate reasoning.

### 5.3. Consider a new top-level premise

The branch analysis suggests that the repaired top-level theorem may need a
new premise bundling:

- runtime guard coherence
- guard-tagged memory realization

This is a real weakening of the theorem statement. The existing premises on
`main` do not appear to imply it.

If that weakening is unacceptable, then a semantics/typechecker change will
probably be needed instead.

## 6. Dead ends and gotchas

These consumed significant time and should not be retried blindly.

### 6.1. `predTagsBoundedInCtx` preservation is false

This was one of the clearest dead ends. The invariant fails because closure
application can expose deep captured tags, and later operations can reify them
into top-level memory.

Do not build a new plan around preserving `predTagsBoundedInCtx`.

### 6.2. Bumping `regime.bound` in `mode 3` is possible but costly

One semantics idea was:

- when entering a `mode 3` branch, also raise the bound so the insert is always
  visible

This would simplify the `k >= bound` story, but it breaks the very widely-used
`Regime.monotoneStep` invariant on `main`, which currently requires equal
bounds. The branch rejected this as too invasive for the surrounding proof
infrastructure.

### 6.3. Per-owner de-poisoning would make the proof much easier, but at a price

Another semantics idea was:

- in `mode 3`, clean only the owner matched by `matchGuard`, not every carrier
  sharing the tag

That would remove most of the transfer problem. It was rejected because it
substantially weakens the language's intended precision.

If proof simplicity becomes the primary goal, this remains the cleanest
semantics escape hatch, but it is a real design change.

### 6.4. Disabling `guardOnly` de-poisoning is also the wrong fix

This would repair the proof by brute force, but it breaks the intended use of
`guardOnly` for linked values and loses desirable precision.

### 6.5. Strengthening `locsRegime.guardOnly_ok` was a trap

It seemed natural to make `guardOnly` demand realization evidence. That
collides with the two-run joined-memory setup:

- joined `memEnv` can mention cells from a branch that was not taken at runtime
- requiring realization for every such `guardOnly` cell makes
  `consistentRegimeSpec` too strong

The branch concluded that `guardOnly` value constraints belong in the new
coherence predicate, not in `locsRegime` / `varsRegime`.

### 6.6. A separate `guardOnlyTagsInTagMeaning` bridge predicate is not enough

This idea tried to say:

- every `guardOnly k` in the context has some backing `tm.lookup k = some d`

The problem is not that such a predicate is meaningless. The problem is that
it is not derivable from the existing `main` premises. So it only relocates
the gap.

### 6.7. Direct projection from a stronger single-run theorem back into the old one failed

The canonical single-run theorem on the branch needed stronger inputs for each
specific runtime state. The old `singleIH` interface on `main` is universally
quantified over arbitrary states and does not carry those stronger inputs.

So the stronger theorem could not simply be "plugged into" the old interface.

### 6.8. Building a universal `singleIH` out of state-specific evidence failed

This was a subtler version of the previous point. Even inside the stronger
dispatcher, the available coherence evidence was for the current state, not an
arbitrary future one. That is not enough to manufacture the universally
quantified `singleIH` expected by the old consumers.

### 6.9. Per-run coherence without a shared witness is still unsound

This was not just inconvenient. It directly fails in the two-run setting.

### 6.10. Output-side deep-property fan-out grows very fast

Pushing the full deep property into every output tuple caused a large proof
explosion and did not immediately help the active `mode 3` work. The branch
backed off and only kept the input-side pieces needed by the blocked proof.

## 7. What the branch actually achieved

The branch did not finish the two-run `mode 3` proof, but it did establish a
few useful facts.

- The strong-invariant route is not obviously impossible. With enough extra
  structure, the branch did prove the stronger canonical single-run `mode 3`
  case.
- The two-run proof reduces naturally to four subcases:
  - `k < bound`, same branch
  - `k < bound`, different branches
  - `k >= bound`, same branch
  - `k >= bound`, different branches
- The hardest subcase was consistently the visible different-branch case
  (`k < bound`, different branches). That is where most of the real semantic
  burden sits.

My read of the final branch state is:

- the original `main` interfaces are genuinely insufficient
- the stronger shared-canonical route removed the known semantic counterexample
  pattern
- the remaining blockers were mostly proof-engineering complexity inside the
  four-way two-run split

The last bullet is an inference from the branch state, not a formal proof that
the strong route is complete.

## 8. Practical takeaways for a clean restart

If the restart stays on `main` and keeps the current `mode 3` typing rule, the
working assumptions should be:

- expect to strengthen proof interfaces, not just fill the existing holes
- expect a new semantic/coherence premise at the top level unless you change
  the typing rule
- treat `guardOnly`, `k >= bound`, and deep captured environments as first-class
  concerns from the start
- do not spend time trying to rescue `predTagsBoundedInCtx`
- do not assume the old single-run theorem is salvageable without interface
  changes

If those costs are unacceptable, the only clearly simpler alternatives are
semantics changes, chiefly:

- per-owner de-poisoning in `mode 3`, or
- a more invasive redefinition of regime visibility/bounds

Both are real design tradeoffs, not proof refactorings.
