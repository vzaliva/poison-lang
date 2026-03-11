# Proposal for Issue #128

GitHub issue: https://github.com/vzaliva/poison-lang/issues/128

## 1. Scope

This document is about the remaining `if` proof work on top of the
rebased branch and the current split proof layout on `main`, with mode
3 as the primary blocker and mode 4 as the lower-risk follow-on.

`while` is out of scope for this iteration.  Any `while` lemmas or
proof branches may remain `sorry` while the `if` mode-3 path is
completed.

This is intentionally a shorter design note.  Long code/spec diffs and
completed rebase work are omitted unless they still matter for an open
design decision.

## 2. Motivation and Core Problem

In `typecheckIf` mode 3, the typechecker learns a fresh branch-local
fact about the guard tag `k`:

- true branch: `k |-> true`
- false branch: `k |-> false`

Historically, that fact was inserted into `L` (`tagEnv`) but not into
`R` (`regime`).  That breaks the key invariant
`tagEnvConsistentWithRegime` whenever the branch inserts a true entry
for a tag that is absent from the outer regime.  Informally, every
`true` entry in `tagEnv` must be mirrored by `some true` in the
regime lookup for the same tag.

So the core issue is:

- mode 3 branch contexts learn more in `L` than they learn in `R`
- the strong invariant then fails
- `stepFR_ite_mode3` cannot apply its IH under that branch context

The proposed semantic fix remains:

- type the true branch under `R[k |-> true]`
- type the false branch under `R[k |-> false]`
- leave `R.bound` unchanged

This keeps the strong invariant instead of weakening it.

The important semantic point is that these branch regimes are
intermediate.  They exist only while typing the branches.  The final
result of the `if` still joins the two branch regimes, and
`joinRegimes` drops the disagreeing entry for `k`, so the output
regime does not retain the mode-3 branch tag.

That said, the rebase exposed an important clarification:

- "the join drops `k`" is only a statement about the final output
- shared recursive proof lemmas still see the intermediate
  `R[k |-> true]` / `R[k |-> false]`

That distinction is now central to the proof work.

### Why keep the strong invariant

An older direction tried to weaken `tagEnvConsistentWithRegime` so it
only constrained tags `k < R.bound`.  That did not simplify the proof
story in practice:

- it pushed `k < R.bound` premises into many existing uses of the
  invariant
- those call sites still needed a bounded-tags invariant
- once that boundedness proof became unavoidable, it was cleaner to
  keep the original invariant and fix the branch regime instead

So the document continues to assume the strong invariant is the right
target.

## 3. Current Design Position

### Preferred branch-update design

The preferred design is still to update both branches:

- true branch under `R[k |-> true]`
- false branch under `R[k |-> false]`

Why this is still the default:

- it is the faithful semantic reading of the branch assumptions
- it preserves typing precision for nested `if`s in the false branch
- it matches the intended mode-3 story in the spec and typechecker

But this point is still provisional.  If tag reuse makes
`R[k |-> false]` semantically wrong or too expensive to prove, the
fallback is an asymmetric design:

- true branch gets `R[k |-> true]`
- false branch keeps the outer `R`

### Working assumptions on the rebased branch

The following are the working assumptions for this proposal:

- mode-3 `if` branches are modeled with branch-local `R.map` updates
- `R.bound` is not changed by those inserts
- the final output regime still drops the branch-local `k`
- the active proof surface is the split `StepFR*` layout, not the old
  monolithic `FaultRobustnessProofs.lean`

## 4. Current State After Completed Work

The completed work on this branch establishes the following starting
point for the remaining design and proof work:

- the typechecking-side repair is in place: the clean-lookup redesign,
  the `R.bound` bridge, and the recursive masked preservation theorem
  `typecheckExpr_preserves_regimeConsistentWithCtxMasked_main` are all
  complete
- the single-run proof infrastructure is in place: the paired
  `CtxCons` / `ValCons` framework, the shared masked runtime/value
  consistency layer, the masked-regime recursive interface, and the
  per-constructor masked / masked-regime wrappers are all landed
- the top-level one-run theorem in
  `FaultRobustnessProofs.lean` is already refactored onto the masked
  recursive family, and mode 1 / mode 2 of the concrete masked `ite`
  proof compile
- the broad generic regime-growth path for
  `consistentWithRegime_insert_regime_*` remains deferred; the active
  direction is still the local masked path plus a targeted repair for
  the active-tag subcase

## 5. Remaining Open Issues

### 5.1 Active-tag mode-3 branch growth

The remaining live blocker is the **in-bound `none`** mode-3 case.
`typecheckIf` can enter mode 3 with `ctx.regime.lookup? k = none` even
when `k < ctx.regime.bound`.

In that subcase, inserting `k ↦ true` / `k ↦ false` makes `k` active
rather than masked, so the approved local masked path no longer avoids
the semantic regime-growth obligation.

This is a branch-local issue, not evidence that the post-`if` regime is
failing to reset.  The Ott `if_depoison_*_R_unknown` rules explicitly
type the two branches under `R[k |-> true]` and `R[k |-> false]`, then
rejoin them with `JoinR` in the conclusion.  The problem is that when
`k < R.bound`, those branch-local inserts become visible to `lookup?`
and therefore activate regime-consistency obligations during the branch
proofs.

### 5.2 Why one owner witness is not enough

This is not a single-owner corner case.  Because same-tag predicates
survive through `joinPredicates`, both-sided memory joins can retain
them, `ctxAfter` leaves `varEnv` unchanged, and `joinRegimes` can drop
the map entry while keeping `k < regime.bound`, a post-join context can
still contain many var / mem / closure-reachable entries referring to
`k` while `regime.lookup? k = none`.

The multi-entry coherence gap is therefore:

- closures, because `closureCapturedVarsRegime` ranges over captured
  values in `ρcap`, not the current runtime `ρ`
- current-memory entries that are **orphaned** from any current
  reference root and therefore do not fit the owner-witness premise of
  `PredSatLaws.match_iff`

So the concrete masked single-run theorem cannot be completed from the
current assumptions alone.  The remaining question is how to supply
multi-entry coherence for the active-tag case without changing the
stable boundaries in Section 7.2.

### 5.3 Mode 4 is separate and lower risk

`stepFR_ite_mode4` is real remaining work, but it is not part of the
issue-128 regime-sync blocker.  Mode 4 is the `matchGuard`-failure
path, so it does not insert `k` into the regime and does not trigger the
active-tag growth problem above.

Mode 4 should therefore be treated as a lower-risk follow-on after mode
3.  It should share:

- the conservative join back-half
- any reusable clean-back / join transport lemmas
- parts of the already-working mode-1 / mode-2 front-half where the
  proof shape truly matches

If some of those reusable lemmas are currently trapped in
`StepFRApp.lean`, they should be moved to `StepFR.lean` rather than
duplicated locally.

## 6. Proposed Solution and Plan

This is an intended order of attack, not a rigid waterfall.  In
particular, the clean-lookup redesign and the regime-growth transfer
story may partially collapse into the same implementation step.

The active plan now focuses only on the remaining mode-3/mode-4 proof
work.

### 6.1 Why the current proof-only path stops

The current `PredSatLaws.match_iff` bridge is inherently
owner-witness-specific: it connects one successful `matchGuard` check
to the particular runtime value that was actually checked.

That is enough for:

- current variables that themselves witness the match, and
- current memory entries reachable through the reference-rooted
  owner-witness shape.

It is not enough for the full active-tag mode-3 branch obligation,
because the branch-local regime insertion for `k` must justify
regime-consistency for all same-tag entries now made active, including:

- closure-captured values, and
- current-memory entries that are orphaned from any current reference
  root.

Since predicate satisfaction is value-sensitive, one owner witness
cannot in general justify all of those other entries.  So the remaining
step-6 gap is not just missing proof plumbing; it is a design-level
problem about how tags are allowed to survive and be re-used.

### 6.2 Viable solution families

At this point the remaining plausible directions are structural, not
proof-axiomatic.

\textbf{A. Repair the tag lifecycle in the typechecker/spec.}

The goal here is to prevent tags whose regime entry has been dropped
from remaining re-matchable later as active in-bound tags.  Candidate
mechanisms include:

- scrubbing dropped tags from joined predicates and related proof
  surfaces,
- or retagging surviving predicates with fresh out-of-bound tags after
  joins, so later re-checks do not reactivate an old in-bound hole.

Any such design has to account for all places tags can survive:

- current `varEnv` entries,
- joined `memEnv` entries,
- and closure-carried typing data.

This is not an implementation bug relative to the current Ott rules.
The existing `if_depoison_*_R_unknown` rules already type the branches
under `R[k |-> true]` / `R[k |-> false]` and rejoin with `JoinR`; the
question is whether the surrounding type/tag lifecycle needs a spec
change so dropped tags do not remain reusable in the wrong shape.

\textbf{B. Redesign tag ownership.}

The deeper alternative is to make a tag name one live predicate
instance (or one coherent owner family), rather than an arbitrary set
of values carrying the same predicate descriptor.  In that world a
single `matchGuard` owner witness could plausibly justify the active-tag
branch insertion.

This would preserve value-sensitive predicates, but it is a much larger
design shift.  It likely touches:

- tag generation / freshness,
- copying and transport of predicates across bindings and memory,
- and the way joins preserve or merge predicate tags.

### 6.3 Recommended next design step

The recommended next step is a bounded design investigation of solution
family A before any more proof work:

(a) catalogue exactly where a dropped tag can survive and later be
    re-matched (`varEnv`, joined `memEnv`, closure typing data, etc.),
(b) determine whether scrub or retag is enough, or whether the current
    `varEnv` treatment forces a larger judgment/interface change,
(c) compare the candidate repair against the Ott rules and write down
    the minimal spec/typechecker change that removes in-bound-`none`
    re-use,
(d) only after that, return to the step-6 proof plan for mode 3, with
    mode 4 remaining the lower-risk follow-on.

Mode 4 should still be planned as simpler than mode 3: it shares the
conservative join back-half, but it avoids the active-tag regime-growth
issue because `matchGuard` failed.  Reuse mode-1 / mode-2 front-half
proof structure where it actually fits, and if reusable join /
clean-back lemmas are currently trapped in `StepFRApp.lean`, move them
into `StepFR.lean` rather than duplicating them in the `ite` proof.

### 6.4 Current active `sorry` surface

As of the current branch, the active code `sorry` surface in
`LeanProofs/` is small and falls into three buckets:

\textbf{(1) `kwhile`-related and out of scope for issue 128.}

- `StepFRKWhile.lean`: `stepFR_kwhile`
- `StepFR.lean`: the `kwhile` branches inside
  `typecheckExpr_preserves_regimeConsistentWithCtxMasked_main` and
  `typecheckExpr_preserves_wfTagMeaningCtx_main`
- `StepFR.lean`: `typecheckExpr_lookup_origin_of_pc_true_split_kwhile`
- `FaultRobustnessProofs.lean`: the `kwhile` case in
  `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree`

\textbf{(2) `if`-related and inside the remaining issue-128 scope.}

- `StepFRIte.lean`: `stepFR_ite_mode3`
  This is blocked by the live mode-3 active-tag / in-bound-`none`
  problem described in Section 5.1.
- `FaultRobustnessProofs.lean`: the remaining mode-3 branch inside
  `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree`
  This is the single-run manifestation of the same blocker.
- `StepFRIte.lean`: `stepFR_ite_mode4`
  This is not blocked by the mode-3 active-tag issue, but it is still
  part of the remaining `if` proof scope and should be treated as the
  lower-risk follow-on after mode 3.

So the remaining proof surface relevant to finishing the `if` work is
exactly:

- two mode-3 holes sharing the same design blocker, and
- one mode-4 hole that should remain after mode 3 as the simpler
  follow-on.

## 7. Implementation Constraints

The following rules apply to every implementation step in the plan above.

### 7.1 Build discipline

After each plan step (and at every intermediate checkpoint), the code must
build with `lake build` and produce no warnings other than `sorry`-related
ones.  A step that introduces new non-`sorry` warnings is not considered
complete.

### 7.2 Stable boundary definitions

The following definitions and predicates sit at the boundary between the
per-case proofs and the top-level theorem.  Changes to them propagate
widely and are expensive to absorb:

- `StepFR` (StepFR.lean:490)
- `StepFR_IH` (StepFR.lean:4209)
- `StepFRSingleRunFinalCleanPcTrue` (StepFR.lean:1042)
- `StepFRSingleRunFinalCleanPcTrue_IH` (StepFR.lean:4214)
- `FaultRobustnessSpec` (FaultRobustness.lean:707)
- `TypeSystemEnforcesFaultRobustness_IOFree` (FaultRobustnessProofs.lean:740)

and the predicates they directly depend on:

- `consistentWithRegime`, `agreeOnClean`, `valueConsistentWithRegime`,
  `resultAgreesIfClean` (RegimeConsistency.lean / FaultRobustness.lean)
- `regimeConsistentWithCtx`, `regimeBounded` (StepFR.lean)
- `runtimeInstantiatesCtx`, `wfTagMeaningCtx`, `wfTypeContext`
  (TypeSafety.lean / StepFR.lean)

Changes to any of these definitions or their signatures require explicit
approval before implementation begins.  If the clean-lookup redesign or
regime-growth work appears to require such a change, that is a stopping
point (see 7.3).

### 7.3 Stopping points

Implementation should pause and report back for design review whenever:

- a plan step appears to require changing a stable boundary definition
  (Section 7.2)
- a concrete counterexample or type-level obstruction is found that
  invalidates the current theorem target or design assumption
- the proof work uncovers a dependency not anticipated in the plan that
  would change the order or scope of later steps
- the symmetric/asymmetric branch-update design decision is forced by
  evidence discovered during implementation

At each stopping point, the implementer should document the finding
concisely and wait for approval before proceeding.  The goal is to
catch design-level surprises early rather than sinking effort into a
path that will need to be unwound.

## 8. History

This section keeps older material that is no longer part of the active
plan but may still matter for future design decisions.

### 8.1 Rejected direction: weaken the invariant

The earlier "bound-guarded invariant" idea changed
`tagEnvConsistentWithRegime` so it only constrained tags within
`R.bound`.

That direction was rejected because it:

- spread `k < R.bound` obligations through many existing proofs
- did not remove the need for a bounded-tags invariant
- complicated the framework more than synchronizing `R.map` did

### 8.2 Old-branch proof work is still useful as design input

The old pre-refactor branch developed parts of the story around:

- `matchGuard_ok_tag_from_ctx`
- `matchGuard_tag_in_bound`
- `consistentWithRegime_insert_regime_true`

That work should still inform the design, but it should not be treated
as current split-layout infrastructure until it is re-homed there.

### 8.3 Historical status of the symmetric design

The symmetric `R[k |-> true]` / `R[k |-> false]` design was chosen to
match the intended semantics and preserve nested-`if` precision.

That reasoning is still valid as a default, but after the rebase it is
no longer sufficient by itself.  The clean-lookup blocker and the
tag-reuse / closure-growth questions now determine whether symmetry is
worth keeping.

### 8.4 Summary of completed steps 1--5

The completed early steps established the current starting point for the
remaining design work:

- the clean-lookup theorem was split and repaired
- the bounded-tag / `R.bound` bridge was restored
- the local masked preservation layer for
  `regimeConsistentWithCtx` landed
- the broad generic `consistentWithRegime_insert_regime_*` direction was
  deferred in favour of the local masked path for step 6
