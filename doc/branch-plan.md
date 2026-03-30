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

## 1. Background

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

On the current main-based branch, those inserts are only visible when the tag
is below `R.bound`, because `Regime.lookup?` still respects the bound.

### 1.1. Scope Assumption

This document assumes the current `.ioFree` fault-robustness theorem setting
throughout.  In particular, the discussion below is about the proof environment
in which no fresh guard tags are generated during execution.

### 1.2. The Two Remaining Mode-3 Sorries

- `stepFRSingleRun_ite_mode3_maskedReg` — single-run variant.
- `stepFR_ite_mode3` — two-run variant.

On the current main-based branch, both remain as theorem-level `sorry`s in
`StepFRIte.lean`, after the IH has been applied to `e1`.

### 1.3. When Mode 3 Arises In FR

The mode-3 machinery — `tagEnv` inserts, `regime.map` inserts, branch
joins — does real work inside the branches.

At the raw `StepFR` level, mode 3 arises exactly when `match_guard` succeeds on
tag `k` but the current regime has no entry for it (`R(k) = none`).

In the top-level FR theorem setting considered here, this can happen in the
following ways:

1. **Initial absence for non-spec tags already present in the context.**
   `wfRegime` constrains the regime exactly on the tags coming from
   `InputSpec`, while `ctxMatchesInputSpec` allows extra non-spec entries in the
   initial context as long as they do not reuse spec tags.  Such extra tags may
   therefore start with `R(k) = none`.

2. **Regime invalidation after assignment.**  `invalidateRegimeDeps` drops
   regime entries when their dependency locations are written.  A previously
   known tag can therefore lose its regime entry before a later guarded `if`.

3. **Regime loss at joins.**  `joinRegimes` is only a conservative merge: it
   keeps a tag exactly when both incoming branch regimes already contain the
   same entry for it.  So after earlier control flow, a later join can make a
   tag unknown whenever the incoming branch regimes differ for that tag, for
   example because one branch invalidated it or because an earlier mode-3 split
   gave the two branches different branch-local values.

For tags that come from `InputSpec`, initial absence is ruled out by
`wfRegime` together with `ctxMatchesInputSpec`.  So within the top-level
theorem setting considered here, a spec tag can reach mode 3 only by later invalidation or
join-loss.

Under the current rule, the FR precision impact is that guard-based
de-poisoning only works for tags
that still have an active regime entry at the point of the `if`.  When a tag
reaches mode 3 by any of the routes above, the poisoned half of the current
proof shape is as conservative as not matching at all; the clean half is
narrower, but it still does not give the straightforward linked-value
de-poisoning behaviour available in modes 1/2.

### 1.4. Contrast With Modes 1 And 2

Modes 1 and 2 (`R.lookup? k = some true/false`) are different: they do NOT
flow `p1` into `branchPc`.  Mode 1 uses `poison := join ctx.pc p2` (only
the taken branch's poison, not the condition's).  So mode 1 CAN produce
clean results even with a poisoned matched owner.

Mode 1 is safe because it is regime-determined — both runs take the same
branch.  And `qtypCleanUnder` has a `guard` constructor that makes tagged
carriers clean when `R.lookup? k = some true`, so `agreeOnClean` forces
both runs to agree on those carriers in the initial context.

Mode 3 cannot use this argument because the regime has no entry for `k`.

### 1.5. Current Main-Based Starting Point

This branch is intentionally based on `main`.

In particular:

1. `Regime.lookup?` still respects `R.bound`.
2. The `predOnlyOnPoisonedNonRef*` invariant package is absent.
3. The mode-3 proof state is therefore the original `main` proof state, not
   the later no-bound / invariant refinements recorded in §4.

---

## 2. Chosen Repair

### 2.1. Current Proof Environment

On the current main-based branch, mode 3 is still the original special
unknown-regime rule, and both proof holes are still present at theorem level.

The important change in direction is that we are no longer trying to prove the
existing unknown-regime rule sound by adding more proof machinery around it.
The chosen repair is to change the rule itself.

So the central question is no longer how to complete the current mode-3 proof
script.  It is whether mode 3 should remain a distinct branch-local
de-poisoning mechanism when `R(k) = none`.  The answer adopted here is no.

### 2.2. Unknown-Regime Ott Rules

For reference, the general unknown-regime rule captures the conceptual mode-3
shape we care about here.  The reference and function variants have the same
branch-local `R[k |-> ...]` / `L[k |-> ... using LS]` structure and differ only
in result-type plumbing, so we omit them in this section.

```text
match_guard e1 G S = k with LS
R(k) = none
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L ; R
pm ; R[k |-> true] ; join pc p1 ; G ; S ; L[k |-> true using LS] |- e2 : T :> p2 { P2 } -| G2 ; L2 ; R2
pm ; R[k |-> false] ; join pc p1 ; G ; S ; L[k |-> false using LS] |- e3 : T :> p3 { P3 } -| G3 ; L3 ; R3
----------------------------------  :: if_depoison_R_unknown
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3 : T :> join pc join p1 join p2 p3 { no_pred } -| JoinGStrong G2 G3 ; JoinL L2 L3 ; JoinR R2 R3
```

The omitted variants share the same branch-local shape:

- in the `then` premise, branch-local reasoning proceeds as if the matched tag
  were true;
- in the `else` premise, branch-local reasoning proceeds as if the matched tag
  were false.

### 2.3. High-Level Diagnosis

The root problem is semantic, not tactical.

As currently written, the unknown-regime rule turns a successful check on one
carrier into branch-local facts about the whole tag class.

That is too strong for fault robustness.  At the point where mode 3 arises, the
outer regime explicitly says the tag is unknown.  So linked values with that
tag are still allowed to differ across the two runs.  Yet the current rule can
still:

- de-poison same-tag carriers in the `then` branch, and
- assert false-side tag facts in the `else` branch.

Those are exactly the facts the proof is unable to justify.

The old design-space analysis tried to preserve some unknown-regime branch-local
benefit while weakening it.  The chosen conclusion is simpler: once `R(k) =
none`, the type system should not create any branch-local tag fact at all.

The presence or absence of `R.bound` only changes how visible the current
branch-local inserts are in a given proof configuration.  It does not change
the underlying mismatch.  The chosen repair therefore does not try to finesse
the visibility story; it removes unknown-regime branch-local tag reasoning.

### 2.4. Chosen Direction

We adopt the strong form of Idea A.

When `match_guard` succeeds but `R(k) = none`, the type system should not
create any branch-local tag fact.  The unknown-regime case should therefore
fall through to ordinary conservative `if` typing.

Concretely, this means:

- no branch-local `tagEnv[k := ...]` updates;
- no branch-local `regime.map[k := ...]` updates;
- no branch-local de-poisoning of either the checked carrier or linked
  same-tag carriers;
- no branch-local false-side regime assertions for `guardClosure` entries.

Modes 1 and 2 stay unchanged.  The repair is local to the `R(k) = none` case.

### 2.5. Strong Idea A: Collapse Mode 3 Into Mode 4

The chosen rule change is:

> If `match_guard` succeeds but `R(k) = none`, do not use the
> `if_depoison_*_R_unknown` branch-local rule.  Instead, type the conditional
> exactly as an ordinary conservative `if`.

At the level of branch typing, this means the unknown-regime case should use
the same context flow as mode 4:

1. Type `e1` under the ordinary incoming context.
2. Build the post-condition context from `res1` in the standard way.
3. Set `pc := join pc p1`.
4. Type both branches under that conservative branch context, with no
   branch-local tag updates.
5. Join branch results in the ordinary way.

So a successful unknown-regime match is still detected, but it is discarded for
branch-local reasoning purposes.

This is intentionally stronger than "owner-sensitive then-side de-poisoning".
It removes the entire unknown-regime branch-local mechanism rather than trying
to weaken it.

It also means the current mode-3-specific join-loss source disappears: the rule
no longer creates opposite branch-local regime entries for the matched tag.

### 2.6. Semantic Impact On De-Poisoning Precision

Strong Idea A removes one corner of the system: regime-unknown conditional
reasoning.

What remains intact:

- mode 1 / mode 2 regime-determined de-poisoning;
- all ordinary tag-linked reasoning when the regime already knows the tag;
- the rest of the FR theorem structure.

What is lost:

- any branch-local benefit from a matched guard when `R(k) = none`;
- both checked-carrier and linked-tag de-poisoning in that case.

This is a real precision loss, but it is tightly scoped.  It only affects the
case where a matched guard is encountered after the tag has become regime-
unknown by one of the routes in §1.3.

---

## 3. Plan

### 3.1. Change `typecheckIf`

Replace the current `R(k) = none` branch in `typecheckIf` with the same
conservative typing pattern used by mode 4.

In particular:

- keep the current `match_guard` / `R.lookup?` control-flow order;
- when `R.lookup? k = none`, do not build branch-local `ctxTrue` / `ctxFalse`
  with remembered tag facts;
- instead, reuse the standard `if` branch typing logic.

### 3.2. Update the Ott Story

Remove the separate unknown-regime branch-local interpretation from the current
design story.

The unknown-regime case should be described as:

- guard recognized, but regime has no fact for the tag;
- therefore no branch-local tag fact is introduced;
- the conditional is typed conservatively, like an ordinary `if`.

### 3.3. Simplify the Proof Obligations

After the typechecker change, the goal is to eliminate the special mode-3
proof burden rather than repair it.

Concretely:

- `stepFR_ite_mode3` should disappear or reduce to a thin wrapper around the
  conservative `if` proof;
- `stepFRSingleRun_ite_mode3_maskedReg` should likewise disappear or become a
  trivial delegation;
- any mode-3-specific masked transport that is only there to support the old
  unknown-regime rule should be removed if it becomes dead code.

### 3.4. Document the Precision Tradeoff

Once the implementation is changed, update the surrounding prose to state
clearly:

- mode 3 no longer provides branch-local de-poisoning;
- this is an intentional conservative repair;
- higher-precision unknown-regime alternatives were considered and are kept in
  §4 for future reference, not for the current branch.

---

## 4. History

This section is retrospective context.  The main conclusions for current use
are collected in §2.

### 4.1. Axiom validation experiment (discarded)

**Branch:** `last2`, stash `Snapshot backup 2026-03-26 14:28:10`
(138 insertions in `StepFRIte.lean`; not committed).

**What we tried.**  Before PR #133 landed, we tested whether a targeted
axiom could close the mode-3 agreement argument.  We added a global
`axiom matchGuard_mode3_condition_poisoned` stating:

> If `matchGuard` succeeds with tag `k`, and `regime.lookup? k = none`,
> and the condition typechecks to `res1`, then `res1.qualType.poison = true`.

We then threaded `singleIH` and `htc` into `stepFR_ite_mode3`, derived
`hp1 = true → branchPc = true → hresPoison = true → hpred = noPred`,
and closed `resultAgreesIfClean` with `resultAgreesIfClean_of_poison_noPred`.
The four-case branch split was laid out with sorrys for transport.

**What it validated.**  All the axiom-dependent derivations compiled.  The
chain `hp1 → branchPc = true → resultAgreesIfClean vacuous` worked
exactly as hypothesised, confirming that poisoned-condition is indeed the
right fact for the vacuous-agreement half of mode 3.  The remaining
sorrys were purely mode-4-analogous join transport — nothing
axiom-specific.

**Why it was discarded.**  When we later attempted to replace the axiom
with a real theorem (the "bridge theorem"
`matchGuard_mode3_condition_poisoned_from_inv`), we discovered a
counterexample: the axiom is **false** for pathological predicate bodies.
A predicate body such as `let y = x + 1 in true` passes the `usesArg`
syntactic check (the carrier `x` appears in the bound expression) but
does not propagate the carrier's poison into the result (the body always
returns `true` with `poison = ctx.pc`).  Concretely, if `ctx.pc = false`
and `x` is poisoned, `typecheckExpr` on this expression gives
`res1.qualType.poison = false`.

**What it taught us.**  The axiom's *consequence* — vacuous agreement
when the condition is poisoned — is sound.  It is the axiom's
*hypothesis* that is too strong: the condition is not *always* poisoned
in mode 3.  This led directly to a later proof strategy on the invariant
branch: case-split
on `res1.qualType.poison` instead of asserting it is `true`.  In the
`poison = true` case the original vacuous-agreement argument applies
unchanged; in the `poison = false` case the invariant forces
`pred = noPred`, so the condition is clean, both runs agree on the
boolean, and the mixed-branch cases are impossible.  The split is
strictly more general than the axiom and handles all predicate bodies
correctly.

### 4.2. Counterexample showing mode-3 de-poisoning is unsound

**Source:** `issue-128-rebase-invariant` branch retrospective (commits
a0eb5d7–7860bfa of this document).

This counterexample predates the merged invariant from PR #133.  It is kept
here because it explains why the older mode-3 design was unsound and why the
proof work pivoted in §4.5; it is not reproducible once the invariant is
assumed.

**The counterexample.**  Two variables share guard tag `0`:

- `x`: clean `bool`, `guardClosure 0 "a" a []` (tag+predicate)
- `y`: dirty `int`, `guardOnly 0` (tag-only)

Expression: `if x then y else 0`.  Initial `pc = false`, regime
`bound = 1`, empty map — so `R.lookup? 0 = none`, exactly mode 3.

`matchGuard` matches `x` (it skips tag-only predicates).  Mode 3 fires.  In
the true branch, `tagEnv[0] = true` causes `typecheckVar` to de-poison `y`
to `⟨int, branchPc, noPred⟩`.  Since `x` is clean, `p1 = false`,
`branchPc = false`, and the result is typed clean.

Two runs with `x = true` (clean, must agree) and `y = 1` vs `y = 2` (dirty,
may differ) both take the true branch and return different values for a
clean-typed result — contradicting `StepFR`.

**What it shows.** Mode 3 de-poisons by tag, not by owner.  A check on `x`
causes mode 3 to de-poison `y`, whose content may differ across runs.  No
existing `main` premise prevents this because `agreeOnClean` is vacuous at
tag `k` when `R.lookup? k = none`.

**Follow-up stress case.**  A same-type variant with `x` clean int
`guardClosure 0 "a" (a == a) []` and `z` dirty int same guard, expression
`if (x == x) then z else 0`, demonstrates the same leak even when both
carriers share the exact closure.

This counterexample is what motivated both the coherence-invariant approach
(§4.3) and, later, the simpler "only poisoned non-ref values carry
predicates" invariant (§4.5).

### 4.3. Coherence-invariant approach (abandoned)

**Source:** `issue-128-rebase-invariant` branch; documented in versions
4280a0d–7860bfa of this document.

**Idea.** Preserve mode-3 typing power by adding a deep semantic
invariant:

> For any fixed runtime state, if two live carriers have the same exact
> tag+predicate combination (`guardClosure k arg body cap`), then their
> runtime values are equal.

Tag-only carriers would be covered separately: for each `guardOnly k`,
there must exist a descriptor `d` with `tm.lookup k = some d` such that
the carrier's value equals the canonical witness `canon k d`.

The witness must be **shared across both runs** (per-run existential
witnesses are insufficient — see §4.4 item 8).

**Why it was abandoned.**

- Engineering cost was very high: new deep predicate in
  `RegimeConsistency.lean`, new premise/conclusion in `StepFR` affecting
  every case proof, preservation proofs for every evaluation rule.
- Structural equality for closures is brittle: semantically "the same guard"
  created at different program points often compares unequal because the
  captured environment snapshots differ.
- The companion same-tag discipline (downgrade structurally-different
  closures with the same tag to `guardOnly`) fires often in practice,
  losing future `matchGuard` ability.
- Separate deep facts do not compose after joins (see §4.4 item 6).
- Risk that the invariant is unprovable if the type system does not actually
  enforce the required same-tag discipline.
- The abandoned branch partially proved a canonical single-run theorem but
  never completed the two-run proof.

### 4.4. Dead ends catalog

These approaches consumed significant time and should not be retried.

1. **`predTagsBoundedInCtx` preservation is FALSE.**
   The invariant "all guard tags in varEnv/memEnv lie below `regime.bound`"
   fails because closure application can expose deep captured tags and later
   operations (e.g., `newRef`) can reify them into top-level memory.  The
   concrete obstruction: start with `bound = 0`, keep a function with
   `guardOnly 5` in its capture, apply it, then `newRef` the result — memory
   now has tag 5 but bound is still 0.

2. **Bumping `regime.bound` in mode 3.**
   Raising the bound so the `regime.map` insert is always visible would
   simplify the `k ≥ bound` story, but it breaks the
   `Regime.monotoneStep` invariant (which requires equal bounds) and is too
   invasive for the surrounding proof infrastructure.

3. **Strengthening `locsRegime.guardOnly_ok`.**
   Requiring realization evidence for `guardOnly` cells collides with the
   two-run joined-memory setup: joined `memEnv` can mention cells from a
   branch not taken at runtime, making the strengthened condition unsatisfiable.

4. **`guardOnlyTagsInTagMeaning` bridge predicate.**
   A predicate saying every `guardOnly k` has backing `tm.lookup k = some d`
   only relocates the gap — it is not derivable from the existing `main`
   premises.

5. **Extending `wfTagMeaningCtx` to cover tag-only entries.**
   The existing `wfTagMeaningCtx` is effectively vacuous for `guardOnly`.
   Adding coverage would require a deep restructuring not justified by the
   mode-3 problem alone.

6. **Separate deep facts do not compose after joins.**
   After `joinETyps`, the same closure shape may be represented by multiple
   `FnTClosure.regular` entries with different captured environments.
   Separately-produced deep properties can choose different members and fail
   to line up.  The abandoned branch only made progress once regime and
   coherence facts were bundled into a single combined deep property.

7. **Projection from canonical single-run into old single-run.**
   The canonical single-run theorem needed stronger inputs (per-state
   coherence evidence).  The old `singleIH` is universally quantified over
   arbitrary states and cannot accept those stronger inputs.

8. **Per-run coherence without a shared witness.**
   Per-run existential witnesses `canon₀`, `canon₁` with no cross-run
   relation directly fail in the two-run setting — they allow
   `canon₀ k d ≠ canon₁ k d`.

9. **Naive transfer principle.**
   Shared tags are not type-indexed.  The same tag can link carriers of
   different types (e.g., `int` and `bool`), so no general value-transport
   principle exists.

10. **Per-owner de-poisoning (restrict to matched owner only).**
    This would eliminate the linked-value mechanism that tag-only predicates
    were designed for.  The core use case — checking a status value to
    de-poison linked data via a shared tag — would no longer work.  This
    removes a fundamental language capability.

11. **Output-side deep-property fan-out.**
    Pushing the full deep property (coherence + regime + typing) into every
    output tuple caused a large proof explosion and did not immediately help
    the active mode-3 work.

### 4.5. Pivot to the "only poisoned non-ref values carry predicates" invariant

**Source:** commit 306a760 ("new approach") of this document.

**The discipline introduced in this phase.**

> **Only poisoned non-reference values carry predicates.**  For any
> non-reference qualified type in `varEnv` or `memEnv`, if `pred ≠ noPred`,
> then `poison = true`.

Reference types were excluded from this discipline: `typecheckLocation`
returns a clean reference that preserves the stored predicate from `memEnv`,
so clean references with predicates remain a normal part of the type system.

**Key insight.**  Instead of strengthening the proof interfaces to justify
mode-3 de-poisoning for all same-tag carriers (the coherence-invariant
approach), we observed that under a simpler discipline — only poisoned
non-reference values carry predicates — the counterexample from §4.2
cannot arise at all.

In the counterexample, `x` is a **clean** boolean with a `guardClosure`
predicate.  The invariant says non-reference values with predicates must be
poisoned.  So `x.poison = true`, which forces `p1 = true` and
`branchPc = true`.  Then everything inside the branch stays poisoned, and
the result is poisoned with `pred = noPred`.  `resultAgreesIfClean` is
vacuous.

What this repair did **not** do was remove the later branch-local obligations
that appear once the proof tries to reason inside a mode-3 branch under
branch-local tag facts.  In particular, it blocks the old clean-`guardClosure`
counterexample, but it does not by itself solve the then-side `agreeOnClean`
problem for `guardOnly` entries or the regime-consistency problem that later
appears for branch-local `guardClosure` reasoning.

This was a dramatically simpler repair than the coherence-invariant route:
define the invariant, prove preservation across all typing rules, enforce
in the spec constructors, thread through StepFR.  PR #133 implemented
this and landed on 2026-03-26.

**Initial expectation from the new invariant.**  The first hope was:

> if the matched carrier is forced to be poisoned by the invariant, then the
> condition itself should be poisoned, hence `branchPc = true`, hence the mode-3
> result should be poisoned with `pred = noPred`.

The owner-side reasoning behind that expectation was:

- **Variable owners.**  `matchGuard` matches a variable carrying a
  `guardClosure`.  By the new invariant, the variable is poisoned.  Since
  `matchGuard` also requires the predicate to use its argument (`usesArg`),
  the carrier seemed likely to force poison into the condition.
- **Reference owners.**  `matchGuard` can also match through `!r`, where the
  merged predicate comes from the referenced memory cells.  Those cells are
  non-reference `int` entries in `memEnv`, so under the new invariant they are
  poisoned whenever they carry predicates, and typing `!r` joins that poison
  into the dereference result.

This expectation motivated the bridge-theorem attempt later discarded in
§4.1.

**Limitation discovered later.**  The invariant ensures the carrier is
poisoned, but a poisoned carrier does not always force the *condition
expression* to be poisoned (see §4.1 — `usesArg` is syntactic, not
semantic).  The final proof strategy avoids this gap entirely by
case-splitting on the condition's poison rather than asserting it is always
true.  In other words, the global bridge theorem is false, but the local
clean/poisoned split remains viable.

### 4.6. Removal of `regime.bound`

After the condition-poison case split was adopted, the next blocker was the
artificial `k < bound` / `k >= bound` split in mode-3 branch contexts.  An
earlier line of work removed `regime.bound` from `Regime`, making `Regime.lookup?`
an unconditional map lookup.

This does **not** revive the dead ends in §4.4:

- it is not a new bounded-tags invariant (ruled out by §4.4.1);
- it is not a local "bump the bound in mode 3" patch (ruled out by §4.4.2).

Instead, it removes the mechanism entirely.  In the FR setting considered here, the
original reason for the bound — protecting the full-IO proof from fresh runtime
tags — is not relevant.

The immediate practical effect is that the old *hidden insert* branch-context
split disappears: mode-3 regime inserts are always visible.

**What we later learned.**  This removed the old *invisible insert* problem, but
it did **not** make same-branch mode-3 transport ordinary.  Visibility is
exactly what activates the fresh `consistentWithRegime` and `agreeOnClean`
obligations for `k`-tagged carriers.  So the old branch-context inconsistency
changed shape rather than disappearing; see §4.7.

### 4.7. Blocker after the no-bound change

**Date:** 2026-03-27, while executing an earlier proof plan for mode 3.

**What we tried.**  We attempted the first same-branch `sorry` in
`stepFR_ite_mode3` under the post-`regime.bound` proof plan, expecting it to be
mode-4-analogous transport.  The only code change made in the file was to
rename underscore-prefixed IH outputs (`_hwfTm1`, `_hcwr₀1`, `_hcwr₁1`, etc.)
so the branch proof could refer to them directly.

**What failed.**  The ordinary two-run IH on the branch context does **not**
apply directly.  Two preconditions become unprovable at
`ctxᵢ.regime.insert k true` / `ctxᵢ.regime.insert k false`:

1. `consistentWithRegime`.
   Activating `k` adds fresh obligations for every `k`-tagged location or
   variable in the context.  The incoming `hcwr₀1` / `hcwr₁1` never established
   those facts, because before the insert the regime still had `k ↦ none`.
   For `guardClosure k` entries this specifically needs new realization and
   predicate-consistency evidence; `guardOnly k` entries avoid that sub-obligation
   but are still newly activated regime entries.

2. `agreeOnClean`.
   `qtypCleanUnder.guard` makes non-function `k`-tagged entries clean as soon as
   the branch inserts `k = true`.  Under the invariant package introduced in
   §4.5 those carriers are
   typically poisoned non-reference values, and the current guarded agreement
   constructor `withPred_true_eq` then asks for literal equality of dirty
   values across runs.  That is exactly the case mode 3 was supposed to leave
   unconstrained.  This hits both `guardClosure k` and `guardOnly k` entries.

This blocks all four same-branch `sorry`s:

- true/true in the poisoned-condition branch;
- false/false in the poisoned-condition branch;
- true/true in the clean-condition branch;
- false/false in the clean-condition branch.

**What this means for the proof strategy.**

- The outer clean/poisoned split is still correct and should stay.
- The single-run masked theorem remains relevant for mixed poisoned cases.
- The same-branch cases need a new relational interface; they are not routine
  mode-4 transport.

**Assessment of candidate resolutions.**

- **Historical Route 1: unary masked reasoning for all mode-3 cases.**
  Useful for mixed poisoned cases, but insufficient by itself for same-branch
  cases because unary results do not reconstruct the missing cross-run branch
  agreement for newly produced outputs.

- **Historical Route 2: add a vacuous guarded-poisoned agreement
  constructor.**
  This would attack only the `agreeOnClean` half of the blocker, leaving
  `consistentWithRegime` untouched.  It would also weaken the meaning of
  guard-based clean agreement in the ordinary modes.

- **Historical Route 3: weaken `qtypCleanUnder.guard` to require
  `poison = false`.**
  This also attacks only the `agreeOnClean` half and would globally change the
  meaning of guard-based de-poisoning, collapsing legitimate mode-1 / mode-2
  clean agreement on linked carriers.

- **Historical Route 4: add masked two-run branch-local infrastructure.**
  Mask `k` while proving the branch-local relational theorem, then transport the
  resulting obligations through the final join, where `k` disappears again
  because the true and false branch regimes disagree on it.  This aligns with
  the existing masked single-run machinery and avoids changing the language- or
  theorem-level semantics.

  The cost is real: no masked two-run theorem currently exists.  The existing
  masked infrastructure is single-run only, so this route requires a new
  theorem-level relational interface rather than just one more transport lemma.

### 4.8. Higher-Precision Alternatives Not Chosen

Before choosing strong Idea A, we also considered several repairs that tried to
preserve some unknown-regime branch-local benefit.

These are not the direction for the current branch, but they may still be
useful later if the precision loss of strong Idea A turns out to matter.

1. **Weak then-only Idea A.**
   Drop only the `then`-side branch-local updates.  This is incomplete because
   it leaves the false-side `guardClosure` regime obligations untouched.

2. **Branch-local checked-carrier environment.**
   Introduce a temporary structure recording that one specific carrier was
   successfully checked.  This is semantically plausible but architecturally
   heavy.

3. **Shadow-tag or local tag-renumbering.**
   Split the checked carrier away from the rest of its tag-class only inside
   the `then` branch.  This keeps the rule tag-driven but looks delicate and
   high-risk.

4. **Deep de-poisoned view of the checked carrier.**
   Interpret the unknown-regime `then` branch semantically as trusting the
   checked carrier itself, not the whole tag class.  This is the cleanest
   higher-precision semantic idea, but it still needs a concrete operational
   story and still needs a false-side account.
