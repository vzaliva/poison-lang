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

The regime inserts are always visible because `Regime.lookup?` is an
unconditional map lookup.

### 1.1. Scope Assumption

This document assumes the current `.ioFree` fault-robustness theorem setting
throughout.  In particular, the discussion below is about the proof environment
in which no fresh guard tags are generated during execution.

### 1.2. The Two Remaining Mode-3 Sorries

- `stepFRSingleRun_ite_mode3_maskedReg` — single-run variant.  What remains
  is proving the masked-regime result for the taken branch.
- `stepFR_ite_mode3` — two-run variant.  At the theorem level this is still
  one remaining lemma, but the current script has been refined into six local
  branch-case holes after the condition-poison split.

Both are in `StepFRIte.lean`, after the IH has been applied to `e1`.

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

The FR precision impact is that guard-based de-poisoning only works for tags
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

### 1.5. Departures from `main` Branch

Relative to `main`, this work assumes two substantive proof-environment
changes:

These are intended as non-controversial proof-engineering changes: they are
fully proved here and are meant to make explicit facts that
were already implicitly relied on in `main`, rather than to change the intended
fault-robustness story.

1. **New invariant added and proved.**
   The development now includes the `predOnlyOnPoisonedNonRefCtx` /
   `predOnlyOnPoisonedNonRefResult` invariant and its preservation lemmas, and
   the relevant `StepFR` interfaces have been updated to thread it through the
   recursive proof.  This just exposes, in a proved form, the discipline that
   clean non-reference predicate-carrying values were not supposed to arise in
   the first place.

2. **`R.bound` removed.**
   `Regime` no longer carries a `bound` field.  `Regime.lookup?` is now an
   unconditional map lookup, so mode-3 branch inserts are always visible.  This
   does not add new semantic power; it removes an artificial bookkeeping device
   that was not part of the intended FR reasoning model.

---

## 2. Current Proof State

### 2.1. Current Proof Environment

The mode-3 proof still runs inside the current `StepFR` environment with the
new invariant package in place.  So the present question is no longer whether
we have enough proof infrastructure to reason about poisoned predicate-carrying
non-reference values.  We do.

The active local proof shape for `stepFR_ite_mode3` is still a split on the
condition poison `res1.qualType.poison`, and that split remains useful.

**Poisoned-condition branch.**  If `res1.qualType.poison = true`, then
`branchPc = true`, the final result poison is true, and the final clean-output
agreement obligation is vacuous because the result has `pred = noPred`.
This part of the story is understood, but the case is not fully proved.

**Clean-condition branch.**  If `res1.qualType.poison = false`, then the current
invariant forces the condition predicate to be `noPred`, so the condition is
genuinely clean.  The two runs must therefore agree on the boolean result of
the condition, which rules out the mixed-branch executions.  This also is only
partially proved: the same-branch cases remain open.

So the poison split is still the right outer organisation, but it is no longer
the centre of the design question.

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

The root problem is now best understood semantically rather than as a missing
transport lemma.

As currently written, this is a **tag-wide** branch-local effect.  Once the
rule commits to one of those premises, every carrier with that tag is treated
as affected inside the branch, not just the carrier whose successful
`match_guard` justified entering the `if_depoison_*` family in the first place.

This is exactly where the remaining fault-robustness problem comes from.

At the point where mode 3 arises, the outer regime explicitly says that the tag
is unknown.  So linked values with that tag are still allowed to differ across
the two runs.  But the current unknown-regime rules can still give
branch-local consequences to all same-tag carriers.

This needs to be split carefully by branch and by predicate form.

**`Then` branch.**  This is still where the `agreeOnClean` problem is most
visible.  Under the current unknown-regime rules, a successful guard check can
de-poison all carriers with the matched tag in the `then` premise.  That is
too strong for fault robustness when the outer regime still says the tag is
unknown: the proof is then asked to show agreement for arbitrary linked
same-tag values, even though only the checked carrier was actually justified by
the guard test.

**`Else` branch.**  The false side is less problematic for `agreeOnClean`, but
it is not obligation-free.  For `guardOnly k` entries, the false side is
indeed comparatively benign: `guardOnly_ok` imposes no regime-consistency
obligation.  But for `guardClosure k` entries, `R[k := false]` still activates
tag-wide `consistentWithRegime` obligations: every same-tag carrier must now
justify the negative predicate direction, and a single successful guard check
on one carrier does not provide that evidence for arbitrary other same-tag
closures.

In simple terms:

- `guardOnly k` entries are genuinely asymmetric: the main blocker is the
  `then`-side clean-agreement obligation;
- `guardClosure k` entries are blocked on both sides: `then` by
  `agreeOnClean` plus regime consistency, `else` by regime consistency alone;
- the common structural mistake is the same in both cases: a per-carrier check
  is being turned into tag-wide branch facts.

So the present blocker should be read as a design mismatch:

- the current unknown-regime Ott rules are symmetric and tag-wide;
- the proof obligations are only partly asymmetric: `guardOnly` is mostly a
  `then`-side problem, but `guardClosure` creates blockers on both sides.

### 2.4. Current Direction

Introducing a masked two-run branch interface is not the primary direction
here.  It may still be usable as a proof device, but it does not address the
semantic tension exposed by mode 3.

The analysis separates two questions:

1. **Then-side de-poisoning strategy.**  What special benefit, if any, should a
   successful unknown-regime check give to the checked carrier?
2. **Else-side regime strategy.**  What false-side facts, if any, may be
   asserted tag-wide for `guardClosure` entries?

The then-side diagnosis is stable: tag-wide de-poisoning is too strong, so any
live repair must stop using a successful check on one carrier as justification
for de-poisoning arbitrary other same-tag carriers.

The false side needs a more explicit statement than before.  What may still be
preservable is the conservative *effect* of making data less trusted in the
`else` branch, but that does not automatically justify the current tag-wide
`R[k := false]` story for arbitrary `guardClosure` entries.  So a then-only
repair is incomplete unless it also says what happens to the false-side regime
obligations.

This is a semantics question first and a proof question second.  The current
proof failure is useful because it pinpoints that the unknown-regime rule needs
an explicit story for both sides of the branch, not just for the then-side
de-poisoning behaviour.

### 2.5. Owner-Sensitive `Then`-Branch De-Poisoning

This subsection lays out the current design space.

One clarification matters up front.  The dead end in §4.4.10 rejected
**global** per-owner de-poisoning, because that would destroy the main
tag-linked de-poisoning mechanism of the language.  The present question is
narrower: whether the unknown-regime `then` premise alone should become
owner-sensitive, while ordinary modes 1/2 remain tag-wide and the false side
still needs some explicit conservative story of its own.

Any live idea must say something about both branches.  The then-side de-poisoning question and the false-side regime
question are separable.  A candidate that changes only the `then` side still
needs a separate explanation of what happens to the `guardClosure` obligations
created by `R[k := false]` in the `else` branch.

#### Idea A. Remove the `then`-branch `R`/`L` updates entirely

The most direct weakening would be to stop updating `R` and `L` in the
unknown-regime `then` premise at all, and simply type the `then` branch under
the original branch context.

Taken by itself, this is incomplete rather than merely "too weak":
changing only the `then` side leaves the false-side `guardClosure`
`consistentWithRegime` blocker untouched.

The stronger variant is to drop branch-local regime participation in mode 3
altogether, pushing mode 3 much closer to mode 4.  Concretely, this means
dropping both the branch-local `tagEnv` updates and the branch-local `R`
updates in the unknown-regime case, so that once `R(k) = none` is discovered,
the typing rule falls through to ordinary conservative `if` typing rather than
carrying any remembered branch-local tag fact.  That would sacrifice even the
checked-carrier benefit and any remembered local fact for nested checks, but it
would also avoid both the then-side clean-agreement problem and the false-side
`guardClosure` regime problem with minimal proof-engineering cost.

**Provisional judgement:** weak then-only form is incomplete; strong "collapse
toward mode 4" form is a live pragmatic baseline.

#### Idea B. Introduce a branch-local checked-carrier environment

A more targeted option is to add a temporary branch-scoped structure recording
that a specific carrier was successfully checked on the `then` side.  Lookup
rules would consult this structure before the ordinary tag-wide `R`/`L`
machinery, so the checked carrier could receive special treatment without
activating all same-tag carriers.

This is the most direct owner-sensitive implementation idea.  It keeps the
branch-local fact reusable inside the branch, which matters for later reads and
for nested mode-3 cases.  A nested mode-3 check could simply extend the
temporary structure in stack discipline, and the whole structure would be
dropped again at the branch join.

The cost is architectural and presentational.  A new temporary structure must
be threaded through the Ott rules, the Lean typechecker, and the FR proof
interfaces.  That would likely force new invariants and broad proof changes
throughout the FR development.  We would also need a precise representation of
the "checked carrier" that works not only for variables but also for
dereference-based and function-based matches.

This makes the rule harder to present and explain as part of the language
itself.  So although it is concrete, it currently looks like an unattractive
way to realise the intended semantics.

It also still needs a separate false-side regime story for `guardClosure`
entries.  By itself, it only addresses the then-side precision problem.

**Provisional judgement:** technically possible, but least preferable.

#### Idea C. Shadow-tag or local tag-renumbering

Another possibility is to preserve the existing tag-based machinery, but split
the checked carrier away from the rest of its tag-class only inside the
`then` branch.  Conceptually, the branch would allocate a fresh shadow tag
`k_then` for the checked carrier, set that shadow tag to true, and leave the
other original `k`-tagged carriers untouched.

This is appealing because it keeps the implementation tag-driven.  It also has
a plausible story for nested mode-3 cases: each nested successful check could
introduce another fresh shadow tag.

But the semantic and engineering costs look high.  We would need a coherent
branch-local re-tagging operation, a precise rule for what gets re-tagged, and
a proof that joins discard the shadow tags in the right way.  Alias-sensitive
cases, captured closures, and repeated checks on the "same" carrier all look
delicate here.  It also feels conceptually odd to repair an owner-sensitive
problem by changing tag identity.

It also does not yet answer the false-side `guardClosure` question.  Even if a
shadow-tag story solved the then-side identity problem, it would still need a
companion account of what the `else` branch is allowed to assert regime-wise.

**Provisional judgement:** plausible backup idea, but high risk.

#### Idea D. Deep de-poisoned view of the checked carrier

Instead of mutating branch environments at the tag level, we could define the
unknown-regime `then` premise semantically in terms of a de-poisoned **view**
of the checked carrier itself.  The branch would then benefit only from facts
that flow from that checked carrier, not from mere tag equality with unrelated
carriers.

In intuitive terms: after a successful mode-3 check, the `then` branch should
act as if "the thing I just checked is trustworthy here", not as if "every
other thing with the same tag is now trustworthy too".  So the branch-local
special treatment follows the checked carrier itself, rather than the whole tag.

This has the right flavour semantically: trust what was actually checked, not
the whole same-tag population.  It may also describe more accurately what we
want the language rule to mean than any particular environment trick.

The difficulty is making "deep" precise.  For a variable owner, the checked
carrier is fairly concrete.  For dereference-based matches, aliased locations,
or function values with captured state, the identity of the checked carrier is
less obvious.  There is also a design choice about how much downstream data
derived from the checked carrier should inherit the benefit.

So this may be the right **semantic** formulation, but not yet a concrete
implementation plan.  If adopted, it would still need a lighter operational
realisation; Idea B is one obvious possibility, but not a preferred one.

It also only explains the then-side trust story.  It still needs a separate
false-side regime strategy for `guardClosure` entries.

**Provisional judgement:** promising semantic direction; implementation still
open.

#### Current short-list

Two options deserve explicit attention for different reasons:

- the strong form of Idea A is the clearest low-engineering complete repair;
- Idea D is the cleanest higher-precision semantic target, but only if it is
  paired with an explicit false-side regime strategy;
- Idea C remains a speculative tag-based fallback;
- Idea B remains a last-resort engineering fallback.

### 2.6. Semantic Impact On De-Poisoning Precision

All live repairs agree on the broad direction, but they do not all lose
exactly the same precision.

On the `else` side, the semantic goal is still conservative: mode 3 should not
gain any new false-side trust that is not justified.  The open design question
is whether the current user-facing poisoning effect can be preserved without
keeping the present tag-wide `R[k := false]` obligations for `guardClosure`
entries.

On the `then` side, higher-precision variants keep some special benefit for the
checked carrier while removing tag-wide de-poisoning of arbitrary linked
same-tag carriers.  The stronger conservative variant instead collapses mode 3
much closer to mode 4 and loses even that checked-carrier benefit.

The practical precision loss is therefore narrow.  It matters only when one of
the routes in §1.3 puts a tag into mode 3 and, inside the `then` branch, the
program wants to rely not just on the checked carrier, but on other linked
same-tag carriers as well.

For spec tags in the theorem setting considered here, this means: the tag was
initially known in the regime, later became unknown by invalidation or join
loss, and a later mode-3 branch wants branch-local benefits that go beyond
what the checked carrier itself can justify.

That is the point where the revised mode-3 rule gives up precision.
Outside those cases, the ordinary modes still provide the original tag-wide
de-poisoning behaviour.

---

## 3. Plan

_To be filled._

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
in mode 3.  This led directly to the current proof strategy: case-split
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
artificial `k < bound` / `k >= bound` split in mode-3 branch contexts.  The
current line of work removed `regime.bound` from `Regime`, making `Regime.lookup?`
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

### 4.7. Current blocker after the no-bound change

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
