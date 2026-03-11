# Proposal for Issue #128

GitHub issue: https://github.com/vzaliva/poison-lang/issues/128

## 1. Scope

This note is only about the remaining blocker for the mode-3 `if`
proof on the rebased branch.

- mode 1, mode 2, and mode 4 are already proved
- `while` is out of scope for this iteration
- the only live issue-128 proof work is the remaining mode-3 `if`
  blocker

The goal of this document is to explain that blocker in semantic
terms, not to record all proof progress that led to it.

## 2. Typing Picture

In the special mode-3 `if` case, `matchGuard` succeeds on a tag `k`,
but the incoming regime has `R(k) = none`.

The intended branch-local typing story is still:

- type the true branch under `L[k |-> true]` and `R[k |-> true]`
- type the false branch under `L[k |-> false]` and `R[k |-> false]`
- keep `R.bound` unchanged

These branch assumptions are local.  After the `if`, `JoinR` drops the
disagreeing entry for `k`, so the post-`if` regime does not keep the
mode-3 branch fact.

So the semantic shape is:

1. temporarily activate `k` inside each branch
2. forget that activation at the final join

This branch-local `R` update is the original issue-128 fix idea, and it
is still the intended local semantics.

## 3. Remaining Blocker

The blocker is the **in-bound `none`** case:

- `R(k) = none`
- but `k < R.bound`

In that situation, inserting `k |-> true` or `k |-> false` into `R.map`
makes `k` active inside the branch.  Once `k` is active, the recursive
proof obligations no longer talk only about the single value whose guard
matched the condition.  They must justify regime-consistency for **all**
currently live occurrences of tag `k`.

That is the missing semantic step.

This is not about the post-`if` join failing to drop `k`.  The join does
drop it.  The problem appears earlier, inside the branch context where
`k` has been re-activated.

## 4. Why One Matched Owner Is Not Enough

The existing `PredSatLaws.match_iff` story is owner-specific:

- `matchGuard` finds one owner whose guard matches the condition
- evaluating the condition tells us whether `predSat k` holds for that
  owner's runtime value

That is enough for the matched owner.  It is not enough for every other
var / mem / closure-captured entry that also carries tag `k`.

So the missing implication is:

- from "the condition matched owner `v` with tag `k`"
- to "every other live entry with tag `k` should be treated the same way"

That implication is exactly the coherence problem.

## 5. What "Coherence" Means

Same-tag uses are **coherent** if learning `k = true` from one live
occurrence of tag `k` is enough to justify treating every other live
occurrence of tag `k` as true as well.

Same-tag uses are **incoherent** if the truth of `k` can differ across
two live values that both carry tag `k`.

The important point is that coherence is not about two entries being the
same runtime value.  It is about them agreeing on the truth of the
predicate represented by `k`.

## 6. Incoherent Contextual Example

The smallest example shape is:

```poison
if x > 0 then y else 0
```

Assume the current typing/runtime context contains:

- `x : int` carrying tag `k` for predicate "arg > 0"
- `y : int` carrying the same tag `k` for the same predicate shape
- runtime values `x = 5` and `y = -3`

Then:

1. `matchGuard` can match the condition `x > 0` to the occurrence of
   tag `k` on `x`
2. mode 3 types the true branch under `k = true`
3. inside that branch, the generic variable rule would treat `y` as
   clean too, because `y` also carries tag `k`

But that is not justified:

- `x > 0` being true tells us something about `x`
- it tells us nothing about `y`

So this is an incoherent same-tag use.  One matched owner does not
justify all live occurrences of the same tag.

This example is meant as a contextual counterexample shape.  It need not
be a closed IO-free source program from an empty context.  It is enough
to show the semantic gap in the current mode-3 theorem target.

## 7. Where Same-Tag Uses Can Survive

The problem is not that the current branch creates a new stale tag out
of nowhere.  The problem is that a tag can survive in multiple places,
and a later mode-3 branch activation would need to justify all of them.

The main surviving surfaces are:

- current variable entries in `varEnv`
- current memory entries in `memEnv`
- closure-captured typing data

So even if the final `JoinR` drops `k`, a later context may still
contain several live mentions of `k`.

## 8. Consequence for the Remaining Mode-3 Proof

To finish the remaining mode-3 proof while keeping the branch-local
`R[k |-> true]` / `R[k |-> false]` design, we need one of two things:

### A. A real coherence principle for same-tag uses

This would say that all live uses of the same tag `k` form one coherent
owner family, so proving the condition for one matched owner is enough
to transfer to all of them.

This could be packaged as a stronger semantic law, but it would be a
real design commitment, not just proof plumbing.

### B. A lifecycle rule that prevents unsafe re-activation

This would allow surviving uses of `k`, but stop them from being
re-matched later in a way that turns `k` back into an active in-bound
regime fact without a coherence guarantee.

This is the "repair the tag lifecycle" direction:

- keep branch-local `R` activation
- but prevent dropped tags from later being re-used in the wrong shape

## 9. Recommended Focus

The remaining design work should focus only on the live mode-3 blocker:

1. catalogue exactly where same-tag uses of `k` can survive
2. decide whether the intended language semantics wants:
   - true same-tag coherence, or
   - surviving uses without later unsafe re-activation
3. write the minimal spec/typechecker change needed for that choice
4. only then return to the remaining mode-3 proof holes

At the current checkpoint, the remaining issue-128 proof surface is
just the two mode-3 holes:

- `StepFRIte.lean`: `stepFR_ite_mode3`
- the corresponding single-run mode-3 hole in
  `FaultRobustnessProofs.lean`
