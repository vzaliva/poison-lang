# Mode 3: Analysis, Counterexample, and Repair

This document is a self-contained reference for understanding and resolving
the mode-3 `if` soundness problem.

**Terminology:**

- **tag-only** (`guardOnly k`): a guard tag with no predicate closure.
  Cannot be matched by `matchGuard`.
- **tag+predicate** (`guardClosure k arg body cap`): a guard tag with a
  predicate closure.  Can be matched by `matchGuard`.
- **mode 1 / mode 2**: `R.lookup? k = some true` / `some false`.
- **mode 3**: `R.lookup? k = none` (regime-unknown; the focus of this
  document).
- **mode 4**: `matchGuard` fails; standard `if`.

---

## 1. What Mode 3 Does

Mode 3 is the case of `typecheckIf` where `matchGuard` succeeds with tag `k`
but the outer regime has no entry for it (`R.lookup? k = none`).

The typechecker:

1. Types `e1` under `pureCtx := true` (the condition is pure).
2. Sets `branchPc := join ctx.pc p1` (condition poison flows into both
   branches).
3. Types the true branch under `tagEnv[k := (true, deps)]`,
   `regime.map[k := true]`, and `pc := branchPc`.
4. Types the false branch under `tagEnv[k := (false, deps)]`,
   `regime.map[k := false]`, and `pc := branchPc`.
5. Joins results conservatively with `pred = noPred`.

The regime inserts **do not bump `regime.bound`**.  Since
`Regime.lookup?` returns `none` when `k >= bound`, the insert is visible
only when `k < regime.bound`.  This creates a fundamental `k < bound` vs
`k >= bound` split in the proof (§3.4).

### 1.1. The two sorrys on `main`

- `stepFRSingleRun_ite_mode3_maskedReg` — single-run variant.  What remains
  is proving the masked-regime result for the taken branch.
- `stepFR_ite_mode3` — two-run variant.  What remains is handling the four
  branch-selection combinations (`b₀, b₁ ∈ {true, false}`) and proving
  agreement on the joined output.

Both are in `StepFRIte.lean`, after the IH has been applied to `e1`.

---

## 2. The Soundness Problem

The mode-3 sorry is **not just missing proof work** — `StepFR` is false under
the current invariant.  This section constructs the counterexample and
explains why.

### 2.1. Counterexample

The counterexample is a proof-level construction: an assumed initial typing
context fed to `StepFR`, not a source-language program.  Two variables share
guard tag `0`:

- `x`: clean `bool`, `guardClosure 0 "a" a []` (tag+predicate)
- `y`: dirty `int`, `guardOnly 0` (tag-only)

This models the linked-value pattern where a checkable status value is linked
to some other data via a shared tag (for example, `ok = validate(buf)` where
`ok` is a boolean and `buf` is linked to it).

```text
if x then y else 0
```

Initial `pc = false` (clean).  Regime: `bound = 1`, empty map — so
`R.lookup? 0 = none`, exactly mode 3.

`matchGuard` skips tag-only predicates, so `y` is never a match candidate.
For `x`, the predicate body instantiates to `x`, matching the condition.
Exactly one match; mode 3 fires.

Two runs: `x = true` in both (clean, must agree); `y = 1` vs `y = 2` (dirty,
may differ).

The counterexample works for any guarded predicate on `y` sharing tag `0`
— whether `guardOnly 0` or any `guardClosure 0 ...`.  The de-poisoning is
driven by the tag alone.

### 2.2. Why it typechecks as clean

The true-branch context inserts into both `tagEnv` and `regime.map`.  The
de-poisoning comes from `tagEnv`: `typecheckVar` inspects `ctx.tagEnv.get? k`
and finds `(true, deps)` for tag `0`.  Both tag-only and tag+predicate
carriers share the same match arm:

```lean
| Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
    match ctx.tagEnv.get? k with
    | some ⟨true, _deps⟩ =>
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
```

So `y` is de-poisoned to `⟨int, branchPc, noPred⟩`.  Since `x` is clean,
`p1 = false`, so `branchPc = ctx.pc`.  The else branch returns
`0 : int :> clean`.  The joined result is typed clean.

### 2.3. Why the outputs disagree

Both runs evaluate `x` to `true`, take the true branch, and return `y`.
Run 0 returns `1`; run 1 returns `2`.  But the result is typed clean, so
`StepFR` would require `1 = 2` — a contradiction.

All `StepFR` premises are satisfiable: regime consistency is trivial (the
regime has no entry at `k`), and `agreeOnClean` only requires agreement on
clean inputs (`y` is dirty, so it is unconstrained).

### 2.4. Why the join does not help

The final branch join drops the temporary `tagEnv`/regime entry for `k`.
But the unsoundness already happened: `y` was de-poisoned inside the true
branch via `tagEnv`, and the clean output type survived the join.

### 2.5. What the counterexample really shows

Fault robustness says poisoned *values* must not leak into clean outputs.
De-poisoning a value declares it clean — the FR theorem then requires both
runs to agree on it.

`matchGuard` success does not force a branch in mode 3.  The regime is still
unknown, so either branch may be taken.  In the FR proof, it justifies a
**same-branch fact for a particular pair of runs**: if the checked owner
agrees across runs, then both runs evaluate the condition the same way and
take the same branch.

But taking the same branch is still not enough to make the result clean.  A
clean result requires the value actually returned by that branch to agree
across runs.

In the counterexample, `x` is clean so branch selection works.  The leak is
through `y`: mode 3 de-poisons every carrier of tag `k` without evidence of
cross-run agreement.

Returning the checked owner itself is not the bug: if the owner is dirty,
its poison flows into the condition, then into `branchPc`, and the result
stays poisoned.  The bug is that a check on `x` causes mode 3 to de-poison
a *different* same-tag value `y` whose content may differ across runs.

### 2.6. Follow-up stress case: same-type exact-closure sharing

This subsection is not needed to establish unsoundness — §2.1 already does
that.  It is a narrower follow-up case that explains why older
coherence-style repairs looked tempting, and tests whether a fix for the
basic boolean/tag-only problem is actually strong enough.

Consider this variant:

- `x`: clean `int`, `guardClosure 0 "a" (a == a) []`
- `z`: dirty `int`, `guardClosure 0 "a" (a == a) []`

```text
if (x == x) then z else 0
```

Two runs:

- Run 0: `x = 0`, `z = 1`
- Run 1: `x = 0`, `z = 2`

This is also unsound on `main` by the same mechanism:

- `x` is clean, so both runs agree on the condition and `branchPc` stays clean.
- Mode 3 then de-poisons `z` by tag.
- The result is typed clean, but the runs return `1` and `2`.

Unlike §2.1, the checked owner and the returned carrier have the same type and
the same exact guard descriptor.  That makes it plausible to rescue with a
stronger coherence invariant saying such carriers agree on their runtime
value.  `main` does not have such an invariant.  So §2.6 is not a second root
problem; it is a stress case for evaluating whether a proposed repair to the
basic cross-type/tag-only bug is really complete.

---

## 3. Root Causes

### 3.1. De-poisoning by tag, not by owner

`matchGuard` returns only `(k, deps)` — it does not retain the matched
owner's identity.  But mode 3 inserts `k := true` into `tagEnv`, causing
`typecheckVar` and `typecheckDeref` to de-poison **every** carrier with tag
`k`.  Both tag+predicate and tag-only share the same code path.

This tag-based de-poisoning is intentional: it is the linked-value mechanism
that shared tags were designed to support.  The soundness gap is not that mode
3 de-poisons by tag, but that the current FR invariant does not justify
extending evidence obtained from the matched owner to other same-tag carriers.

### 3.2. `agreeOnClean` does not cover newly activated tags

`agreeOnClean` constrains entries already clean under the pre-branch regime.
In mode 3, `R.lookup? k = none`, so tag-`k` carriers are not yet clean and
the two-run hypothesis says nothing about them.

### 3.3. The tag-only gap

Tag-only carriers are doubly unprotected:

1. De-poisoned by tag alone — their value is never checked.
2. `locsRegime.guardOnly_ok` and `varsRegime.guardOnly_ok` impose zero
   semantic constraint, so even in modes 1/2 they have no `predSat`-based
   protection.

Tag-only predicates model linked values (e.g., `ok = validate(buf)` where
`buf` carries `guardOnly k`).  Disabling their de-poisoning would remove a
core language capability.

### 3.4. `Regime.bound` and visibility

When `k >= regime.bound`, the `regime.map` insert is invisible through
`Regime.lookup?`.  This breaks `tagEnvConsistentWithRegime`:

```lean
∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

The branch context has `tagEnv[k] = true` but `regime.lookup? k = none`, so
neither `StepFR_IH` nor any guard-coherent IH can be applied.  The
`k < bound` vs `k >= bound` split is unavoidable.

### 3.5. `wfTagMeaningCtx` says nothing about tag-only entries

`wfTagMeaningCtx` ensures that all tag+predicate entries sharing tag `k`
carry the same predicate closure.  This makes each tag have a single
unambiguous meaning.  It says nothing about tag-only entries.

A tag-only entry for tag `k` can exist even if no predicate for `k` is
registered.  Any transfer principle that needs to know what predicate `k`
refers to cannot get that from `wfTagMeaningCtx` — a separate invariant
is needed.

### 3.6. Deep closures can surface arbitrary tags

A top-level invariant about tags in `ctx.varEnv` and `ctx.memEnv` is not
enough.  Closure application exposes captured environments, and `newRef` can
copy their guard tags into memory.  A captured `guardOnly 5` can surface as
a top-level memory cell while `regime.bound` is still `0`.

Any invariant must account for deep captured values, not only top-level
bindings.

### 3.7. Separate deep facts do not compose after joins

After `joinETyps`, the same closure shape may have multiple
`FnTClosure.regular` entries with different captured environments.  Two
separately-produced deep properties can pick different entries and fail to
line up.

The only successful approach was bundling regime and coherence facts into a
single combined deep property from the start.

---

## 4. Dead Ends

This section documents approaches that were tried on the abandoned branch and
failed.  It is kept as a reference so that future repair attempts do not
repeat the same mistakes.  The entries are technical and assume familiarity
with the proof infrastructure.

### 4.1. `predTagsBoundedInCtx` — FALSE

**Idea:** Assert all guard tags in the context are below `regime.bound`.

**Why false:** Closure application exposes deep captures; `newRef` can copy
them into memory.  Tags can be arbitrarily large while `regime.bound`
stays at 0.

### 4.2. Bumping `regime.bound` in mode 3

**Idea:** Raise the bound so the insert is always visible.

**Why rejected:** Breaks `Regime.monotoneStep`, which requires
`R'.bound = R.bound` and is used extensively across the proof files.

### 4.3. Strengthening `locsRegime.guardOnly_ok`

**Idea:** Require θ-realization evidence for tag-only entries.

**Why rejected:** `consistentWithRegime` requires `locsRegime`/`varsRegime`
evidence for every entry whose guard tag is active in the regime
(`R.lookup? k ≠ none`).  Strengthening `guardOnly_ok` to require
θ-realization would make this evidence mandatory for all active tag-only
entries.  In the two-run proof, the joined `memEnv` may reference cells
whose realization depends on which branch was taken, making this obligation
unsatisfiable.

**Lesson:** Keep `guardOnly_ok` zero-obligation; put value constraints in
a separate coherence predicate.

### 4.4. `guardOnlyTagsInTagMeaning` bridge predicate

**Idea:** Assert every tag-only entry has a backing `tm.lookup k = some d`.

**Why rejected:** Cannot be derived from current premises —
`wfTagMeaningCtx` ignores tag-only entries (§3.5).  Fold the requirement
into the coherence predicate instead.

### 4.5. Extending `wfTagMeaningCtx` to cover tag-only entries

**Idea:** Require tag-only entries to have a registered meaning.

**Why rejected:** Existing preservation proofs rely on tag-only entries
being unconstrained.  Changing this cascades through them.

### 4.6. Projection from canonical single-run into old single-run

**Idea:** Replace `singleIH` with a call to a stronger canonical single-run
theorem.

**Why rejected:** The canonical theorem requires `guardClosureCoherentWith`
and `guardTaggedMemRealized` as input.  `StepFR_IH` does not carry these;
cannot construct strong inputs from weak premises.

### 4.7. Combined dispatcher with universal `singleIH`

**Idea:** Build `singleIH` inside the combined dispatcher by calling the
canonical single-run.

**Why rejected:** `singleIH` is universally quantified over all runtime
states.  The canonical single-run needs state-specific coherence inputs.
Cannot build a universal function from specific evidence.

**Lesson:** Upgrade the `singleIH` parameter type to require strong inputs.

### 4.8. Per-run coherence without a shared witness

**Idea:** Independent per-run witnesses (`∃ canon₀` and `∃ canon₁`).

**Why rejected:** Allows `canon₀ k d ≠ canon₁ k d`.  The transfer principle
needs cross-run agreement; per-run witnesses do not provide it.

### 4.9. Output-side deep-property fan-out

**Idea:** Add the combined deep property to the OUTPUT of `StepFR`.

**Why problematic:** Mode-4 branch assemblies (4 combinations) each need ~90
lines.  Mode-1/mode-2 take `IH : StepFR_IH` (not IHGC), so they cannot produce
it without additional parameter changes.

**Lesson:** Restrict deep property threading to the INPUT side during initial
construction.  Output-side should be deferred to the combined dispatcher.

### 4.10. Restrict de-poisoning to the matched owner only

**Idea:** Stop mode 3 from de-poisoning arbitrary same-tag carriers and only
clean the matched owner (variable or dereferenced reference).

**Why rejected:** This eliminates the linked-value mechanism that tag-only
predicates were designed for.  The core use case — checking a status value
(e.g., `ok`) to de-poison linked data (e.g., `buf`) via a
shared tag — would no longer work.  Tag-only carriers can never be matched
owners (since `matchGuard` skips them), so they could never be de-poisoned
through mode 3 at all.  This is not a minor precision loss; it removes a
fundamental language capability.

### 4.11. Naive transfer principle

**Idea:** Justify tag-based mode-3 de-poisoning by a general transfer
principle: if one owner with tag `k` was checked, transfer that value-level
reasoning to other same-tag carriers.

**Why rejected:** Shared tags are not type-indexed.  The same tag can link
carriers of different types (for example, an `int` and a `bool`).  In that
setting there is no general value-equality or value-transport principle to
transfer from one carrier to another.  Any such argument only makes sense in
same-type cases, so a naive global transfer principle is not viable.

---

## 5. What a Repair Needs to Justify

The counterexample shows that one of the following must change: the theorem
statement, the typing rule, the underlying tag discipline, or the semantic
invariants.

Mode 3 de-poisons every carrier of tag `k` after checking one owner.  For
the FR theorem, every de-poisoned carrier must agree across runs.  A sound
repair must provide evidence of that cross-run agreement.  The difficulty
depends on the relationship between the checked owner and the de-poisoned
carrier.

### 5.1. The easy case: returning the checked owner

If the branch returns the checked owner itself and the owner is dirty, its
poison flows into the condition, then into `branchPc`, and the result stays
poisoned.  No new invariant is needed — the existing PC-poisoning mechanism
handles this.

### 5.2. Same-type same-closure carriers (§2.6 shape)

When the de-poisoned carrier has the same type and the same exact
tag+predicate closure as the matched owner, a **value-equality coherence
invariant** could work: require all carriers sharing the same exact
(tag, descriptor) to have the same runtime value.  If `x` and `z` are both
`int` with `guardClosure 0 "a" (a == a) []`, the invariant forces them to
hold the same value, so checking `x` implicitly checks `z`.

This was the approach explored on the abandoned branch.  It made progress on
the same-type case but never completed the full two-run proof.

Key lessons from that attempt:

- The witness must be **shared** across both runs (per-run existentials allow
  disagreement; see §4.8).
- The witness must be **deep** — accounting for captured environments inside
  closures, not just top-level bindings (§3.6).
- Regime and coherence facts must be **bundled** in a single deep property to
  avoid member-matching failures after joins (§3.7).
- The `k < bound` vs `k >= bound` split (§3.4) is unavoidable and requires
  masking infrastructure.

### 5.3. Cross-type and tag-only carriers (§2.1 shape)

This is the primary counterexample and the harder problem.  The checked owner
is `bool`, the leaked carrier is `int` with `guardOnly 0`.  Value equality
between a bool and an int is meaningless — there is no general transfer
principle across types (§4.11).

This is also the **intended** use case of tag-only predicates: `ok = validate(buf)`
where `ok` is a checkable boolean status and `buf` is linked data of a
different type.

For the FR theorem, de-poisoning `buf` requires both runs to agree on it.
What could justify that?

- **Causal relationship**: `ok` and `buf` were produced by the same operation.
  If both runs call `validate` with the same inputs, they get the same `ok`
  and the same `buf`.  But the type system does not track causality — tags
  are just numbers linking entries.

- **Cross-run agreement on all same-tag carriers**: a stronger invariant
  asserting that for any tag `k`, all carriers (regardless of type or
  predicate kind) agree across runs.  This is stronger than value equality
  (which only applies within a type) and would need a different formulation.

- **Typing rule change**: restrict what mode 3 can de-poison.  For example,
  only de-poison carriers whose type matches the matched owner's type, or
  require same-tag carriers to share a type.  This would reduce language
  expressiveness.

### 5.4. Open questions

The core design question is: **what semantic property of the initial state
and the typing rules guarantees that same-tag carriers agree across runs?**

Any proposed repair should address:

1. The cross-type tag-only case (§2.1) — the primary counterexample.
2. The same-type same-closure case (§2.6) — the stress test.
3. Deep closures (§3.6) and join composition (§3.7).
4. The `k < bound` / `k >= bound` split (§3.4).
5. Whether the top-level theorem statement needs new premises, and whether
   those premises are satisfiable for the intended use cases.

---

## 6. Summary

### The bug

Mode 3 de-poisons every carrier of a tag after checking only one owner.
The FR theorem requires de-poisoned values to agree across runs, but no
existing invariant justifies that agreement for non-owner carriers.  The
primary counterexample (§2.1) uses cross-type tag-only sharing — the
intended use case of the linked-value mechanism.

### What we know does not work

See §4 for the full list.  The most important rejections:

- Restricting de-poisoning to the matched owner eliminates the linked-value
  mechanism (§4.10).
- A naive global transfer principle fails because tags are not type-indexed
  (§4.11).
- Value-equality coherence (`canon k d = v`) does not extend to cross-type
  carriers.

### What partially works

The value-equality coherence approach (explored on the abandoned branch)
addresses the same-type same-closure case (§5.2) but not the cross-type
tag-only case (§5.3).

### What is needed

A repair that justifies cross-run agreement for all carriers de-poisoned by
mode 3, including cross-type tag-only carriers.  This likely requires either
a new semantic invariant that goes beyond value equality, or a change to the
typing rule that restricts what mode 3 can de-poison.

### Proof-level facts that remain relevant

Regardless of the repair chosen:

- The `k < bound` vs `k >= bound` split is unavoidable (§3.4).
- Deep closure invariants must account for captured environments (§3.6).
- Bundled deep properties are needed to avoid join composition failures (§3.7).
- `wfTagMeaningCtx` cannot be extended to tag-only entries (§4.5).
- The existing `StepFR` interfaces will need strengthening.
