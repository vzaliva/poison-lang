# Proposal for Issue #128

GitHub issues:

- #128: https://github.com/vzaliva/poison-lang/issues/128
- #131: https://github.com/vzaliva/poison-lang/issues/131

## 1. Scope

This note is now centered on the issue-131 analysis.  The original
issue-128 idea was:

- in mode 3, type the branches under a branch-local regime update
  `R[k |-> true]` / `R[k |-> false]`

That local branch update is still the intended typing move.  But issue
131 shows that the remaining mode-3 theorem is false under the current
semantics.  So the live question is no longer "how do we finish the old
proof?" but rather:

- what design or theorem change is needed to make mode 3 sound again?

This document incorporates the analysis from issue 131 so that future
work can proceed from one local note.

We use the following terminology throughout:

- `tag-only`: `guard k`
- `tag+predicate`: `guard k pred_closure pcl`

`tag-only` occurrences are purely logical: the carrier value does not
matter.  `tag+predicate` occurrences are the ones whose meaning still
depends on the carrier value via the attached predicate closure.

## 2. Why `stepFR_ite_mode3` Is False

This section explains why the current mode-3 `if` proof is not
salvageable as stated, and how the formal counterexample works. This
counterexample is based on the `issue-128-rebase-main` branch. This note
is a further clarification of the issue mentioned in this document, with
aim to document a formal counterexample construction and provide an
insight into the core issue.

The short version is:

- mode 3 types the branches under a branch-local regime update
  `R[k |-> true]` / `R[k |-> false]`
- the semantic premises available to `StepFR` do not justify applying
  that update to every other `tag+predicate` occurrence of the same tag
  `k`
- therefore the typing rule can derive a clean result for an expression
  whose runtime output still depends on a dirty input

The formal proof of a counterexample is implemented. So this is not just
"the proof is hard". The theorem is false.

## 3. What mode 3 is trying to say

`typecheckIf` has four cases. Mode 3 is the case where:

- `matchGuard e1 ... = .ok (k, deps)`
- the outer regime lookup is `R.lookup? k = none`

Intuitively:

- the condition `e1` matched a guard predicate carrying tag `k`
- but the outer regime does not yet interpret `k`
- so the typechecker explores both branches conservatively

The current rule does that by typing:

- the true branch under `R[k |-> true]`
- the false branch under `R[k |-> false]`

and then joining the two branch results.

That looks reasonable if one reads the successful guard match as
"inside the true branch, tag `k` is known true".

The problem is that the semantics available to `StepFR` do not justify
that reading for all same-tag `tag+predicate` values. They only justify
it for the matched owner.

## 4. Where the unsoundness comes from

`StepFR` starts from an outer runtime-consistency assumption:

- `consistentWithRegime predSat R ctx ...`

That assumption is intentionally selective. It only constrains variables
and memory cells whose guard tag is already interpreted by the outer
regime, that is, tags `k` with `R.lookup? k ≠ none`.

In mode 3 we are exactly in the opposite case:

- `R.lookup? k = none`

So before entering the branches, the outer hypotheses say nothing about
other `tag+predicate` occurrences of tag `k`.

That is the critical gap.

The typechecker then moves into a branch context where `k` suddenly
becomes active:

- in the true branch, every same-tag occurrence is read under
  `R[k |-> true]`
- in the false branch, every same-tag occurrence is read under
  `R[k |-> false]`

This is stronger than what the semantics gave us. A successful
`matchGuard` tells us something about one matched owner witness. It does
not imply that every other variable, memory cell, or captured value
carrying a `tag+predicate` occurrence of the same tag should now be
treated as clean.

This distinction matters because only `tag+predicate` occurrences
participate in `matchGuard` and `predSat`.  `tag-only` occurrences are
purely logical and do not depend on the runtime value of the carrier.
The unsoundness discussed here is about same-tag `tag+predicate`
occurrences, not `tag-only` ones.

That is exactly the mismatch exploited by the counterexample.

## 5. Counterexample idea

The counterexample uses two variables with the same tag:

- `x`: clean
- `y`: dirty

Both carry the same guard-closure predicate for tag `k = 0`:

- `Predicate.guardClosure 0 "a" (a == a) []`

The expression is:

```text
if (x == x) then y else 0
```

This condition is chosen so that the successful `matchGuard` witness is
unique:

- for `x`, instantiating the predicate body `a == a` at the owner gives
  `x == x`, which matches the condition
- for `y`, the same predicate body instantiated at the owner gives
  `y == y`, which does **not** match `x == x`

So mode 3 is triggered by a single matched owner (`x`).  If both
occurrences matched, `matchGuard` would report multiple matches and the
special mode-3 rule would not apply.

The outer regime is:

- `bound = 1`
- empty map

So `k = 0` is in range, but `R.lookup? 0 = none`.

That is exactly the mode-3 case.

The two runs are:

- run 0: `x = 0`, `y = 1`
- run 1: `x = 0`, `y = 2`

The two runs agree on every clean input:

- `x` is clean and equal in both runs
- `y` is dirty, so it is allowed to differ

If the result is really clean, fault robustness should force the two
outputs to be equal. But this expression returns `y`, so the outputs are
different.

## 6. The exact witness used in the formal proof

The formal counterexample in `LeanProofs/StepFRIte.lean` uses:

- tag `iteCounterTag = 0`
- predicate
  `Predicate.guardClosure 0 "a" (a == a) []`
- context:
  - `x : int`, poison `false`, same predicate
  - `y : int`, poison `true`, same predicate
- outer regime:
  - `bound = 1`
  - `map = {}`
- expression:
  - `iteCounterE1 = x == x`
  - `iteCounterE2 = y`
  - `iteCounterE3 = 0`

The runtime states are:

- `iteCounterRho0 = [("x", 0), ("y", 1)]`
- `iteCounterRho1 = [("x", 0), ("y", 2)]`

The tag meaning and predicate-satisfaction model are chosen so that:

- the descriptor attached to tag `0` is exactly the self-equality guard
  `a == a`
- the `PredSatLaws` proof for that meaning is valid
- any successful `matchGuard` for this descriptor implies the condition
  evaluates to `true`

So the counterexample is not exploiting a fake or vacuous `predSat`. It
works with a real `PredSatLaws` witness.

## 7. Why the expression typechecks

The condition `x == x` matches the guard predicate attached to `x`, so
the typechecker enters mode 3.

It is important that `y` does not also match the condition:

- both `x` and `y` carry the same stored predicate
  `Predicate.guardClosure 0 "a" (a == a) []`
- during `matchGuard`, that predicate body is instantiated at the owner
- for `x`, the instantiated body is `x == x`
- for `y`, the instantiated body is `y == y`

Only the former is syntactically identical to the condition `x == x`.

The key branch-local effect is:

- true branch context uses `R[0 |-> true]`

Inside that context, reading `y` no longer sees an unknown guard tag.
Because `y` carries the same tag `0`, the variable rule treats `y` as
de-poisoned and returns:

- `y : int`, poison `false`, `noPred`

The else branch is just:

- `0 : int`, poison `false`, `noPred`

So the joined result of the whole `if` is:

- `int`
- poison `false`
- `Predicate.noPred`

This is the crucial bad typing judgment: the entire expression is
classified as clean.

## 8. Why the runtime outputs disagree

Semantically, the condition is true in both runs:

- `x == x` evaluates to `true`
- both runs have the same clean `x`

So both runs take the true branch.

The true branch returns `y`.

Therefore:

- run 0 returns `1`
- run 1 returns `2`

The outputs differ only because `y` differs, and `y` is dirty in the
outer context. That part is fine.

What is not fine is that the typechecker classified the final result as
clean. Once that happens, `StepFR` must prove output agreement, and that
is impossible.

## 9. The formal contradiction

The proof of `stepFR_ite_counterexample_exists` does the following.

First, it instantiates the full `StepFR` premises on the two runs:

- well-formed realization maps
- runtime instantiation of the typing context
- regime consistency
- agreement on all clean inputs
- successful evaluation of the same `if` expression in both runs

Then it uses the `StepFR` conclusion to obtain:

- a final result-agreement witness
  `resultAgreesIfClean ... res.qualType (Value.num 1) (Value.num 2)`

Next it proves from the mode-3 typing derivation that:

- `res.qualType.poison = false`

So the result is clean under the output regime.

Applying `resultAgreesIfClean` to that clean-result proof yields:

- `agreeValueUnder ... res.qualType (Value.num 1) (Value.num 2)`

Since the result type is a clean non-reference non-function `int`,
`agreeValueUnder_nonref_eq_of_clean` forces:

- `Value.num 1 = Value.num 2`

which is absurd.

That contradiction finishes the proof.

## 10. Why the final join does not save the rule

One possible reaction is:

"But the final branch join drops the temporary regime entry for `k`, so
the output regime is conservative again."

That is true, but it is irrelevant to the bug.

The unsoundness already happened while typing the true branch:

- `y` was de-poisoned under `R[k |-> true]`
- the final result inherited that branch-local clean type

Dropping `k` from the joined regime afterward does not retroactively
justify the de-poisoning of `y`.

The branch-local assumption was stronger than the semantic hypotheses,
and the clean output type survived the join.

## 11. What the counterexample really shows

The counterexample does not say that every branch-local regime update is
wrong.

It says something more specific:

- successful matching of one guard owner is not enough to activate the
  same tag for every other `tag+predicate` carrier of that tag

So one of the following must change:

- the theorem statement
- the typing rule
- the underlying tag discipline
- the semantic invariants

For example, a sound repair could require some stronger global
same-tag-coherence invariant, or a discipline where tags are unique to
a single owner, or a weaker mode-3 typing rule that does not de-poison
arbitrary same-tag `tag+predicate` values.

But without such a repair, the current mode-3 theorem is false.

## 12. Consequences for the repository

The formal situation is now:

- the remaining `sorry` in `stepFR_ite_mode3` is not merely unfinished
  proof work; it corresponds to a false statement

So the correct next step is not "finish the old proof". The correct next
step is to change the design or statement so that the theorem becomes
true again.

## 13. Coherence Interpretation

The core semantic gap can be stated in the language we have been using
in this document:

- same-tag uses are **coherent** if learning `k = true` from one live
  occurrence of tag `k` is enough to justify treating every other live
  occurrence of tag `k` as true as well
- same-tag uses are **incoherent** if the truth of `k` can differ across
  two live values that both carry tag `k`

The important point is that coherence is not about two entries being the
same runtime value. It is about them agreeing on the truth of the
predicate represented by `k`.

This coherence question only concerns `tag+predicate` carriers.
`tag-only` carriers are already defined to follow the logical truth of
`k` without any value-based `predSat` obligation.

The issue-131 counterexample is exactly an incoherent same-tag use:

- `x` and `y` both carry tag `0`
- `x == x` matches the guard on `x`
- the branch then de-poisons `y` too, only because `y` has the same tag
- but the semantics never justified transferring the fact from `x` to
  `y`

So issue 131 is not just a proof counterexample. It is a concrete
demonstration that the current mode-3 design lacks a sound coherence
principle for same-tag `tag+predicate` reuse.

## 14. Proposed Solutions

Two candidate repairs are under consideration.  They differ in whether
the current mode-3 typing rule is preserved (§14.2) or weakened (§14.1).
They are not mutually exclusive: §14.1 could serve as a pragmatic first
step and §14.2 as a later strengthening.

### 14.1. Restrict De-Poisoning to the Matched Owner

The simplest sound repair is to stop mode 3 from de-poisoning arbitrary
same-tag carriers.  Instead, only the specific variable or reference
that `matchGuard` matched would be cleaned.

#### Current behavior

`matchGuard` returns `Tag × Deps` and discards the identity of the
matched owner.  Mode 3 inserts `k |-> true/false` into both the tag
environment and the regime map, which causes `typecheckVar` (line 729)
and `typecheckDeref` (line 1355) to de-poison every carrier of tag `k`.

#### Required changes

1. **Extend `matchGuard`** to return the matched owner identity
   alongside `Tag × Deps`.  For variable owners, the identity is the
   variable name.  For reference owners, the identity is the variable
   name holding the reference.  This information is already available
   internally (lines 643–648 for variables, 651–690 for references)
   but is currently discarded before the return at line 694.

2. **Replace the global tag/regime insertion** with a local context
   rewrite.  Instead of inserting `k |-> true` into the tag environment
   and regime map, mode 3 would directly update the matched owner's
   type in the branch context:

   - true branch: `ctxTrue.varEnv[x] := ⟨etyp, ctx.pc, noPred⟩`
     (de-poisoned, predicate consumed)
   - false branch: `ctxFalse.varEnv[x] := ⟨etyp, true, noPred⟩`
     (forced poisoned)

   All other variables with tag `k` keep their existing types unchanged.
   The tag environment and regime stay unchanged (`R.lookup? k = none`).

   **Reference owners are more complex.**  A naive approach — rewriting
   the memory type entries at the locations in the owner's `LocSet` —
   is unsound as an "owner only" mechanism: any other variable whose
   `LocSet` overlaps those locations would also see the rewritten
   entries, and with non-singleton locsets the rewrite can clean
   locations not actually realized by the matched owner.  (This follows
   from how `matchGuard` matches `deref x` by merging predicates across
   the whole locset, and how `typecheckDeref` reads merged memory
   predicates.)

   A correct mechanism for reference owners would need to track the
   owner reference identity into `typecheckDeref` — for example, an
   owner token that `typecheckDeref` checks before de-poisoning.  That
   is more invasive than the variable case.  A simpler initial version
   of §14.1 could restrict owner-only de-poisoning to variable owners
   and leave reference owners conservatively dirty.

3. **Adapt the proof** for `stepFR_ite_mode3`.  The branch-local
   regime update disappears, so the proof no longer needs to justify
   `consistentWithRegime` under an extended regime.  Instead it needs
   to justify the single rewritten variable, which is the matched owner
   whose `predSat` is already implied by `PredSatLaws.match_iff`.

#### Precision impact

This approach loses de-poisoning power in several ways.  The detailed
comparison is in §14.3, but the main costs are:

- multi-carrier same-tag families stay dirty (copies, aliases)
- reference owners stay dirty unless an owner-token mechanism is added
- the matched owner's predicate is consumed (`noPred`), so inner
  if-expressions in the same branch can no longer syntactically rematch
  the owner (the current rule preserves the original `guardClosure` in
  the env and only adds tag/regime knowledge)

#### Engineering cost

- Changes to `Typecheck.lean`: `matchGuard` signature and mode 3
  rewrite (variable owners only in the initial version; reference
  owners require additional owner-token mechanism)
- Changes to proof lemmas about mode 3 typing structure
- **No new runtime invariant**, no changes to `consistentWithRegime`
  (71 use sites untouched), no preservation proofs
- No changes to `FaultRobustnessSpec` or the top-level theorem statement

This is significantly cheaper than §14.2.

#### Implementation staging: variable owners first

The simplest sound implementation of §14.1 defers the reference-owner
problem entirely and only handles variable owners.

**Step 1: Restrict `matchGuard` to variable owners.**  Skip the
reference matching loop (Typecheck.lean lines 651–690).  Only the
variable matching loop (lines 643–648) runs.  If the only match was
through a reference, `matchGuard` returns an error, and `typecheckIf`
falls through to mode 4 (standard if — no de-poisoning).  The
uniqueness check at line 694 stays as-is but only sees variable matches.

**Step 2: Return the matched variable name.**  Extend `matchGuard` to
return the matched variable name alongside `Tag × Deps`.  The name is
already available at line 646 but currently discarded.

**Step 3: Rewrite the matched variable instead of inserting into the
regime.**  Mode 3 replaces:

```
-- Current (unsound): global regime/tagEnv insertion
let regimeTrue := { ctx.regime with map := ctx.regime.map.insert k true }
let ctxTruePoisoned := { ctxTrue with pc := branchPc, regime := regimeTrue }
```

with:

```
-- Variable-only §14.1: rewrite matched variable only
let varEnvTrue := ctx.varEnv.insert x ⟨etyp, ctx.pc, Predicate.noPred⟩
let ctxTruePoisoned := { ctx with pc := branchPc, varEnv := varEnvTrue }
```

The regime and tag environment stay unchanged.  Only the matched
variable `x` is touched.  The false branch rewrites `x` to
`⟨etyp, true, Predicate.noPred⟩` (forced poisoned).

**What this handles.**  The single-variable-owner pattern — the most
common case:

```
let x = sensor_read()       -- guarded by tag k
if (guard_check(x)) then
    use(x)                   -- x is clean here
```

`matchGuard` matches `x`, mode 3 rewrites `x` to clean in the true
branch.  No other variable is affected.

**What this defers.**  Reference owners (`if (guard_check(!r)) ...`)
fall through to mode 4.  Same-tag aliases (`let y = x`) stay dirty.
Inner re-matching is lost because the predicate is consumed.

**Why the proof simplifies.**  Because the regime stays at
`R.lookup? k = none`, the proof never needs to justify
`consistentWithRegime` under an extended regime.  The entire mode-3
argument reduces to: `PredSatLaws.match_iff` justifies the rewrite
for the matched owner; all other types and invariants are inherited
from the outer context unchanged.

### 14.2. Coherence Invariant: Strengthen the Semantics

The alternative is to preserve the current mode-3 typing power by
adding a semantic invariant that justifies the global de-poisoning.
This requires two complementary pieces: a value-equality invariant for
same `tag+predicate` carriers, and a companion discipline that prevents
structurally different `tag+predicate` closures from coexisting under
the same tag.

#### The invariant

A new deep coherence invariant:

- for any fixed runtime state, if two live carriers have the same exact
  `tag+predicate` combination, then their runtime values are equal

Here "same exact `tag+predicate` combination" means the same tag and the
same structural predicate closure, not merely the same tag.  `tag-only`
occurrences are outside this invariant.

This directly blocks the issue-131 shape.  In the counterexample, `x`
and `y` both carry:

- `Predicate.guardClosure 0 "a" (a == a) []`

So the invariant would force `x` and `y` to have the same runtime value
whenever they are both live with that exact `tag+predicate`.  That
removes the bad state where mode 3 matches `x`, cleans `y`, and `y`
still differs.

The intended proof argument for mode 3 would then be: when mode 3
inserts `k |-> true` into the branch regime, every same-tag carrier
that gets de-poisoned either (a) is a `tag-only` carrier, which is
purely logical and carries no `predSat` obligation, or (b) is a
`tag+predicate` carrier with the same exact closure as the matched
owner.  In case (b), the coherence invariant guarantees the carrier has
the same runtime value as the matched owner, so the `predSat` fact
established by `PredSatLaws.match_iff` for the owner transfers to
the carrier.

This value-equality form is stronger than strictly necessary.  A weaker
predicate-agreement statement (same tag+predicate implies same `predSat`
outcome) could also justify mode 3.  But value equality is the better
first target:

- it is simpler to state
- it is easier to use in proofs
- it already matches how `agreeValueUnder` reasons about first-order
  values

#### Companion same-tag discipline

The equality invariant alone is not sufficient, because mode 3
de-poisons by tag alone.  Both `var_guard_true` and `deref_guard_true`
inspect only the tag `k` — they do not check whether the carrier's
predicate closure matches the one that `matchGuard` matched.

This is harmless for `tag-only` carriers: they are purely logical and
carry no value-dependent `predSat` obligation.

The gap that remains is:

- two live `tag+predicate` carriers may share the same tag `k` but have
  structurally different predicate closures

Mode 3 would clean both of them, but the equality invariant only relates
carriers with the same exact closure.  So the invariant needs a
companion discipline:

- structurally different `tag+predicate` closures must not remain live
  under the same tag

The preferred enforcement mechanism is downgrading to `tag-only`:
whenever a typing rule would introduce a `guardClosure` for tag `k`
into a context that already contains a structurally different
`guardClosure` for the same `k`, **both** entries should be collapsed
to `Predicate.guardOnly k`.  This already happens at join points:
`joinPredicates` collapses unequal same-tag closures to `guardOnly`.
The remaining work is to extend this discipline to the other rules
where a same-tag conflict can arise:

- assignment to a memory cell that already carries a different closure
  for the same tag
- function capture, when the captured environment snapshot introduces
  a closure that conflicts with an existing one in the outer context
- context accumulation across sequential statements

For each such rule, the implementation must detect the conflict and
normalize both sides to `guardOnly`.

**Precision cost of downgrading.**  Downgrading to `guardOnly` has a
real consequence: `matchGuard` does not match `guardOnly` predicates
(Typecheck.lean line 631).  So once the companion discipline fires,
future predicate-sensitive matching on that tag is lost.  The guard tag
still supports branch-local de-poisoning if already active in the
regime, but no new `matchGuard` can discover it.  This means §14.2 does
not fully preserve the current mode-3 power — it preserves de-poisoning
for tags that survive without conflict, but loses future matching
ability whenever the companion discipline triggers.

**Structural equality is brittle.**  "Same exact predicate closure" is
a structural notion: it compares the tag, argument name, body, and
captured typing environment inside
`Predicate.guardClosure k arg body σcap`.  Two predicates with the same
body but different captured environments count as different closures.

In practice this is more restrictive than it appears.  Closures capture
full typing-environment snapshots via `VarTypeEnv.toCaptured`
(Typecheck.lean lines 825, 1172).  This means that semantically "the
same guard" created at two different program points will often compare
structurally unequal just because the surrounding context grew or
changed between the two capture sites.  If this happens frequently, the
companion discipline will fire often, downgrading to `guardOnly` and
losing future `matchGuard` ability.  The effective precision of §14.2
therefore depends on how stable capture environments are across the
program points that share a tag — which may be hard to predict in
advance.

#### Implementation plan

The implementation should be deep from the start.  In this repository,
shallow properties that ignore captured closures have repeatedly turned
out to be too weak.  The existing deep closure machinery provides the
template:

- `deepValueQTypProperty` (RegimeConsistency.lean) — generic
  combinator that recurses through closure values
- `closureCapturedVarsRegime` (RegimeConsistency.lean) — tracks
  regime consistency inside captured environments
- `agreeCapturedEnv` (FaultRobustness.lean) — tracks agreement
  inside captured environments

The plan is:

1. Define a new deep runtime coherence predicate for same
   `tag+predicate` carriers, modeled after the machinery above.

2. Introduce it as a **sibling predicate** alongside
   `consistentWithRegime`, not as a new conjunct inside it.  This
   keeps the existing `consistentWithRegime` reasoning (71 use sites)
   mostly intact and localizes the new proof burden.

3. Add the predicate as a premise and conclusion of `StepFR`.

4. Prove preservation: each evaluation rule must maintain the
   invariant in the post-evaluation context (`ctxAfter ctx res`).

5. Thread the predicate into
   `TypeSystemEnforcesFaultRobustness_step_IOFree` and likely into
   `FaultRobustnessSpec` / `FaultRobustnessSpec_ioFree` /
   `TypeSystemEnforcesFaultRobustness_IOFree`.

#### Open questions

**Definition of "live carrier."**  The invariant quantifies over "live
carriers" of the same `tag+predicate`, which informally means variables,
memory cells, and captured values inside live closures.  The predicate
will be hard to state and preserve until the notion of "live carrier" is
made precise.  It likely needs to cover:

- top-level variable bindings (`ctx.varEnv`)
- memory cell types (`ctx.memEnv`)
- captured typing environments inside closure values, recursively

This aligns with the three scopes already tracked by
`consistentWithRegime`.

**Preservation burden.**  The invariant must be preserved across every
evaluation rule.  The hardest cases are:

- assignment, which can overwrite `tag+predicate` carriers in memory
- function application, which introduces new runtime bindings from
  captured environments
- mode-3 branches themselves, which type sub-expressions under a
  changed regime and then join the results — branch bodies can
  allocate, assign, capture closures, and create new same-tag
  carriers, so preservation through "type each branch, then join" is
  a substantial proof obligation, not a cheap corollary

**Reference equality.**  Literal value equality is straightforward for
integers and booleans, which already covers the issue-131 witness.  For
references, requiring raw location equality may be stronger than
necessary — it may suffice to require equality of the content at the
referenced address.  This should be decided explicitly when the
predicate is formalized.

**Source of the invariant.**  The top-level theorem needs the coherence
invariant to hold at the initial state.  There are three possible
sources, with different proof and usability costs:

1. **Explicit premise on initial runtime states.**  The simplest
   option: add the invariant as a precondition of `FaultRobustnessSpec`.
   This narrows the class of admissible states and puts the burden on
   the caller to establish coherence.

2. **Derived from context well-formedness.**  If a stronger
   `ctxMatchesInputSpec` or context well-formedness fact already implies
   the invariant, no new premise is needed — but such a derivation
   would require proving that well-formed contexts cannot produce
   incoherent same-tag carriers.

3. **Proved from typing plus the companion normalization.**  If the
   companion same-tag discipline (downgrade to `guardOnly` on conflict)
   is strong enough, it may be possible to prove that any typechecked
   program satisfies the invariant by construction.  This is the most
   satisfying outcome but also the hardest to achieve.

This choice should be made explicitly before implementation begins, as
it determines whether the top-level theorem statement changes.

#### Engineering cost

This approach preserves mode-3 de-poisoning for tags that survive
without same-closure conflict, but at substantial proof-engineering
cost:

- New deep predicate definition in `RegimeConsistency.lean`
- New premise and conclusion in `StepFR` (affects every case proof)
- Preservation proofs for every evaluation rule (assignment, application,
  if-expression, etc.)
- Likely changes to `FaultRobustnessSpec` and the top-level theorem
- Risk that the invariant turns out to be unprovable if the type system
  does not actually enforce the required same-tag discipline

### 14.3. Comparison and staging

The two approaches are not mutually exclusive.  A pragmatic path is:

1. Implement §14.1 first to obtain a sound mode 3 with minimal proof
   disruption.
2. If the precision loss from §14.1 proves limiting in practice,
   upgrade to §14.2 later by adding the coherence invariant and
   restoring the global de-poisoning rule.

#### Precision analysis

Both approaches lose some precision relative to the current (unsound)
rule.  Neither is strictly better than the other in all scenarios.

**§14.1 precision losses.**  Under §14.1, mode 3 only de-poisons the
specific variable that `matchGuard` matched.

| Scenario | §14.1 | Current | Notes |
|----------|-------|---------|-------|
| Single variable owner | clean | clean | Most common case; identical |
| Copy of matched owner | **dirty** | clean | Copy has same value but is not the matched owner |
| Reference owner | **dirty** | clean | Ref matching unsupported without owner-token mechanism |
| Inner re-check on same owner | **dirty** | clean | Predicate consumed to `noPred` at branch entry; current rule preserves `guardClosure` and only adds tag knowledge |
| Unrelated same-tag carrier | dirty | "clean" | §14.1 correct; current rule unsound |

The predicate-consumption issue deserves emphasis.  Under §14.1, the
matched owner's type is rewritten to `noPred` at branch entry.  This
means an inner `if` in the same branch cannot syntactically rematch the
same owner, because `matchGuard` needs a `guardClosure` predicate to
match against.  The current rule does not have this problem: it leaves
the original `guardClosure` in the environment and only adds
`tagEnv`/regime knowledge.

**§14.2 precision losses.**  Under §14.2, mode 3 de-poisons every
same-tag carrier globally, but the companion discipline can degrade
predicates before mode 3 gets to use them.

| Scenario | §14.2 | Current | Notes |
|----------|-------|---------|-------|
| Coherent same-tag family | clean | clean | Preserved by the invariant |
| Same tag, different closure (after downgrade) | tag-only | guardClosure | Companion discipline fires; `matchGuard` can no longer match this tag |
| Structural σcap divergence | tag-only | guardClosure | Capture-env snapshot grew between two sites; structurally unequal |

The `matchGuard` loss is significant: `matchGuard` does not match
`guardOnly` predicates (Typecheck.lean line 631).  So once the companion
discipline fires, the tag can still participate in branch-local
de-poisoning if it is already active in the regime, but no new
`matchGuard` can discover it.  And because structural equality on
`guardClosure` includes the full captured typing environment via
`VarTypeEnv.toCaptured`, this downgrade may fire more often than
expected — the same guard created at two different program points will
compare unequal whenever the surrounding context changed between the
two capture sites.

**Head-to-head.**  The approaches have complementary strengths:

| Scenario | §14.1 | §14.2 |
|----------|-------|-------|
| Single variable owner | clean | clean |
| Coherent copy/alias | **dirty** | clean |
| Reference owner | **dirty** | clean |
| Inner re-check on same owner | **dirty** | clean |
| After companion-discipline downgrade | n/a | **tag-only** (loses future matching) |

The single-owner case is the most common pattern.  Both approaches are
identical there.

The practical impact depends on program structure: §14.1 is worse when
programs copy or alias guarded values; §14.2 is worse when programs
create guards at different program points with divergent capture
environments.

#### Engineering trade-off

| Dimension | §14.1 (weaken mode 3) | §14.2 (coherence invariant) |
|-----------|-----------------------|-----------------------------|
| De-poisoning power | Matched variable only | Coherent same-tag family (minus companion downgrades) |
| Reference owners | Dirty (or needs owner-token) | Clean |
| Inner re-matching | Lost (predicate consumed) | Preserved |
| Future matching after conflict | n/a | Lost (downgrade to `guardOnly`) |
| Proof cost | Low | High |
| Changes to `Typecheck.lean` | Yes (`matchGuard` + mode 3) | Companion discipline rules |
| Changes to proof infrastructure | Local (mode 3 lemmas) | Global (new invariant everywhere) |
| Risk | Low | Moderate (invariant may be unprovable) |
| Top-level theorem statement | Unchanged | Likely strengthened |
