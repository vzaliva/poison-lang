# Proposal for Issue #128

GitHub issue: https://github.com/vzaliva/poison-lang/issues/128

## 1. Scope

This document is about `if` mode 3 only, on top of the rebased branch
and the current split proof layout on `main`.

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

## 4. What the Rebase Changed for the Proofs

The rebase onto current `main` did more than move code around.  It
changed which proof obligations are now primary.

### 4.1 Shared clean-lookup blocker

The most important new blocker is the shared theorem
`typecheckExpr_clean_lookup_origin_of_pc_true` in `StepFR.lean`.

Before the regime-sync change, that theorem could recurse into branch
proofs and return a clean source under the outer regime.  After the
change, the recursive call naturally returns a clean source under the
branch-local regime instead:

- `R[k |-> true]` in the true branch
- `R[k |-> false]` in the false branch

That is exactly where the two new post-merge `sorry`s appeared.

At first glance the false-branch case looks easier than the true
branch, because `qtypCleanUnder.guard` needs `lookup? = some true` and
inserting `k |-> false` cannot itself create such a witness.

However, the review correctly highlights a deeper risk: the current
transport goal may simply be false as stated.  The theorem currently
tries to transport

- `qtypCleanUnder { ctx.regime with map := ctx.regime.map.insert k b } qt_in`

back to

- `qtypCleanUnder ctx.regime qt_in`

for some `qt_in` looked up in the pre-branch `ctx.memEnv`.

That transport is trivial only in the `.clean` case.  In the `.guard`
case it requires the base regime to already satisfy the same lookup.
If the guard witness uses the freshly inserted tag `k`, transport back
to the base regime fails immediately, because mode 3 is entered
precisely when `ctx.regime.lookup? k = none`.

The document therefore should not assume that the clean-lookup task is
"just" a branch-local transport lemma.  On the current branch,
pre-branch entries can already carry guard tag `k` while `R(k) = none`:

- `consistentWithRegime` only constrains entries when the regime
  already interprets their tag
- `matchGuard` discovers tags from existing predicates in
  `memEnv` / `varEnv`; it does not obtain them from the regime
- `advanceNextTagForPred` advances the fresh-tag supply past tags
  already present in predicates, but it does not force those tags into
  the regime

So the transport target in
`typecheckExpr_clean_lookup_origin_of_pc_true` is false as currently
stated in the `.guard` case.  The theorem must be redesigned, or a
stronger invariant must be added that changes which pre-branch entries
are even possible.

### 4.2 Current main proof style

Inspection of `StepFRApp.lean` and `StepFRIte.lean` suggests a clear
direction for the fix.

Current `main` tends to preserve provenance and transport explicit
member evidence, rather than erase it early and try to recover it with
one generic theorem.  The reusable pieces already present in the split
layout include:

- `joinTypeResults_lookup_member_clean_compat`
- `joinTypeResults_lookup_member_guardTag_compat`
- `joinTypeResults_lookup_member_regime_compat`
- `memberVarsRegimeEvidence_transport_lookup_back`
- `memberCvcrEvidence_transport_lookup_back`
- `agreeValueUnder_clean_transport_by_cleanBack`

That makes the likely repair path:

- strengthen `typecheckExpr_clean_lookup_origin_of_pc_true`, or add a
  companion theorem, so it preserves more witness provenance
- keep the current existential theorem as a corollary, because it is
  used broadly by `StepFRApp`, `StepFRAssign`, `StepFROp`,
  `StepFRSeq`, and `StepFRVlet`

These helpers are most obviously relevant after the branch join, where
facts are transported backward through `joinTypeResults` and
disagreeing regime entries are dropped again.  They do not by
themselves solve the earlier branch-entry problem, where the regime has
grown from `R` to `R[k |-> b]`.

### 4.3 Other issue-128 proof obligations that are on the path

The clean-lookup theorem is not the only affected proof site.  The
current issue-128 proof surface on this branch includes:

- two post-merge `sorry`s in
  `StepFR.lean:typecheckExpr_clean_lookup_origin_of_pc_true`
- one mode-3 preservation `sorry` in
  `StepFR.lean:typecheckExpr_preserves_regimeConsistentWithCtx_main`
- one `ite`-case `sorry` in
  `FaultRobustnessProofs.lean:TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree`
- the final target `sorry` in `StepFRIte.lean:stepFR_ite_mode3`

So the current document should treat the issue as more than "two new
post-merge sorrys".  There are several distinct blocked obligations,
some lower-level and some downstream.  On the current branch, that
amounts to four issue-128-related `sorry`s before the final mode-3
proof is complete.

For clarity: `stepFR_ite_mode4` is not part of the issue-128 regime
sync story.  Mode 4 is the `matchGuard`-failure path, which does not
insert `k` into the regime.  Its remaining `sorry` is real, but it is
not evidence against the `R.map` synchronization design.

The dependency from
`TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree`
is indirect rather than immediate.  The `ite` case there has not yet
been split into a helper, but when it is, it should follow the same
pattern as the already proved cases and depend on both the
clean-lookup theorem and `regimeConsistentWithCtx` preservation.

## 5. Remaining Proof Problems

### 5.1 The clean-lookup theorem must be redesigned

If pre-branch `memEnv` entries may already carry guard tag `k` while
`R(k) = none`, then the current theorem target is false in the
`.guard` case with witness tag `k`.

For the current branch, that feasibility question is now considered
closed: such entries can occur under the visible invariants, because
the regime does not constrain uninterpreted tags, while `matchGuard`
discovers tags from existing predicates in `memEnv` / `varEnv`.

So the open question is no longer whether the current theorem can be
proved as written.  It cannot, at least not from the currently exposed
invariants.  The open question is what the replacement theorem should
say:

- return more structured cleanliness evidence
- restrict to a subset of clean sources
- or add a stronger invariant that rules out the problematic `.guard k`
  case in pre-branch memory

This question also affects the design decision about symmetric versus
asymmetric branch updates, so it belongs at the front of the plan.

### 5.2 The `R.bound` bridge is still missing

The proposal still needs an active split-layout path from successful
`matchGuard` to `k < ctx.regime.bound`.

The expected ingredients are still:

- `matchGuard_ok_tag_from_ctx`
- `matchGuard_tag_in_bound`
- a bounded-tags invariant such as `predTagsBoundedInCtx`

Why this remains plausible:

- ioFree typechecking does not create fresh predicate tags
- predicates are preserved or dropped, not invented
- initial spec tags are already bounded by `wfRegime`

So the problem is not the semantic idea.  The problem is that the old
branch work around this has not yet been re-homed into the active
split proof layout.

### 5.3 `regimeConsistentWithCtx` preservation looks locally fixable

There is also a distinct mode-3 preservation gap in
`StepFR.lean:typecheckExpr_preserves_regimeConsistentWithCtx_main`.

This obligation is different from the clean-lookup theorem, but it
looks much easier:

- `regimeConsistentWithCtx` is just
  `tagEnvConsistentWithRegime ∧ regime.bound ≤ nextTag`
- the bound conjunct should survive because `R.bound` is unchanged
- the tagEnv conjunct should be reachable using the existing insert
  lemmas plus simple lookup facts for the simultaneously updated regime

So this should still be tracked, but not as a fundamental design
blocker on the same level as the clean-lookup theorem.  It is more
likely a local preservation proof that needs a small regime-insert
lookup bridge.

### 5.4 `consistentWithRegime` under regime growth is still unresolved

Once the regime grows from `R` to `R[k |-> b]`, obligations open that
were previously gated off.

For the top-level `locsRegime` / `varsRegime` conjuncts, the main risk
is tag reuse:

- `PredSatLaws.match_iff` gives predicate satisfaction only for the
  owning runtime value matched by the guard
- if multiple entries share the same guard tag `k`, that does not
  automatically justify all entries with tag `k`

For the closure side, the situation is even harder:

- `closureCapturedVarsRegime_monotone` only handles regime shrinkage
- mode-3 branch reasoning needs regime growth
- previously closed gates inside closures can open when `k` is added

So there are really two related but distinct questions:

1. can the shared clean-lookup theorem be repaired under regime growth?
2. can `consistentWithRegime` itself be transferred under regime
   growth, especially in the presence of tag reuse and closure
   evidence?

Those should not be conflated, but they also may not separate cleanly
in implementation.  The theorem shape chosen for the clean-lookup
redesign will likely constrain which `consistentWithRegime` transfer
lemmas are needed later.

### 5.5 The symmetric false-branch design is still a decision point

The proposal still prefers symmetric branch updates, but that choice
should be revisited very early, not only after later proof repair.

If false-branch insertion turns out to be:

- semantically wrong under reused tags, or
- much more expensive than its value justifies

then the document should switch to the asymmetric design rather than
continue investing proof effort in `R[k |-> false]`.

## 6. Concrete Plan

This is an intended order of attack, not a rigid waterfall.  In
particular, the clean-lookup redesign and the regime-growth transfer
story may partially collapse into the same implementation step.

Current implementation status on this branch:

- Step 1 is complete.
- Step 2 has been reviewed early and does not currently force a design
  change; the implementation is continuing with the symmetric
  branch-update design.
- A supporting regime-insert lookup bridge now exists in
  `StepFR.lean` as `regime_lookup_insert_ne`.
- The shared clean-lookup redesign now exists as a split proof:
  `typecheckExpr_lookup_poison_origin_of_pc_true`,
  `typecheckExpr_lookup_guard_origin_of_pc_true`, and
  `typecheckExpr_clean_lookup_origin_of_pc_true` rebuilt as a
  corollary.
- A checkpoint `lake build` succeeds after the step-1 refactor with only existing
  `sorry`-related warnings.
- The step-4 closure-sensitive regime-growth blocker has now resurfaced
  concretely inside step 6: the mode-3 single-run `ite` proof needs to
  start a branch IH under `ctxTrue` / `ctxFalse'` after interpreting the
  fresh guard tag `k`, but the existing transport helpers only preserve
  `consistentWithRegime` for the old regime.  This is the same blocker in
  a more local proof context, not a new design category.

1. **Redesign the shared clean-lookup theorem.**
   The current transport target in
   `typecheckExpr_clean_lookup_origin_of_pc_true` is false under the
   currently visible invariants, so the theorem must change.  Work in
   the current `main` style: preserve lookup/provenance information and
   keep the existing existential theorem only as a corollary for its
   current callers.
   Status: complete.  The theorem has been refactored into the split
   lemmas `typecheckExpr_lookup_poison_origin_of_pc_true` and
   `typecheckExpr_lookup_guard_origin_of_pc_true`, with
   `typecheckExpr_clean_lookup_origin_of_pc_true` rebuilt as the
   existential corollary for existing callers.  The key proof sites
   for that refactor were discharged in `ite` mode 3, `ite` mode 4,
   `app`, and the `assign` invalidation case.  `while` remains out of
   scope for this iteration and its existing `sorry` remains isolated.

2. **Make the regime-growth design decision early.**
   Re-evaluate symmetric versus asymmetric branch updates while the
   clean-lookup redesign is still in flight.  Do not assume the
   false-branch insertion is worth keeping until the tag-reuse and
   guard-tag analysis say it is.
   Status: complete for the current iteration.  The step-1 refactor
   did not uncover a concrete obstruction or counterexample forcing
   the asymmetric fallback, so the implementation continues with the
   symmetric branch-update design until later evidence says otherwise.

3. **Re-introduce the `R.bound` bridge in the split layout.**
   Re-home or redesign `matchGuard_ok_tag_from_ctx`,
   `matchGuard_tag_in_bound`, and the bounded-tags invariant they need.
   The output of this phase should be an active path from successful
   `matchGuard` to `k < ctx.regime.bound`.
   Status: complete.  The split layout now has a shared bounded-tags
   invariant `predTagsBoundedInCtx` in `StepFR.lean`, together with
   `matchGuard_ok_tag_from_ctx` and `matchGuard_tag_in_bound` in
   `StepFRIte.lean`.  The ref-side extraction was strengthened to carry
   nonempty locset evidence, so successful `matchGuard` now yields a
   concrete var/mem witness for the returned tag and a direct bridge to
   `k < ctx.regime.bound` once `predTagsBoundedInCtx` is available.

4. **Implement the regime-growth transfer lemmas for the chosen
   design.**
   This includes the split-layout versions of
   `tagEnvConsistentWithRegime_insert_*_with_regime` and
   `consistentWithRegime_insert_regime_{true,false}` as needed, with
   `PredSatLaws.match_iff` wired into the actual proof sites.
   Status: partially complete under the narrowed path.  The local
   simultaneous-insert helpers
   `tagEnvConsistentWithRegime_insert_true_with_regime` and
   `tagEnvConsistentWithRegime_insert_false_with_regime` are now in
   `StepFR.lean`, and `lake build` succeeds after adding them.  The
   broader generic `consistentWithRegime_insert_regime_{true,false}`
   work remains blocked pending review: the top-level mem/var transfer
   shape still looks implementable, but the generic closure-sensitive
   story breaks at the closure conjunct of `consistentWithRegime`.
   Under regime growth, previously inactive captured-variable
   obligations for the newly interpreted tag `k` can become active
   inside closures, and the current premises do not provide the runtime
   evidence needed to discharge them.  That remains deferred.

5. **Close the local mode-3 preservation gap for
   `regimeConsistentWithCtx`.**
   Repair
   `typecheckExpr_preserves_regimeConsistentWithCtx_main` using the
   existing tagEnv insert lemmas together with the step-3 bound bridge
   and the minimal simultaneous-insert lemmas from step 4.  Treat this
   as a local repair to land after the higher-risk blockers above.
   Status: complete.  The local repair now uses a recursive masked
   preservation theorem
   `typecheckExpr_preserves_regimeConsistentWithCtxMasked_main` in
   `StepFR.lean`, together with the new masked TagEnv/Regime helper
   layer (`tagEnvConsistentWithRegimeMasked_weaken`,
   `tagEnvConsistentWithRegimeMasked_join_drop`,
   `invalidateRegimeDeps_preserves_true_masked`, and related insert /
   invalidate lemmas).  The original
   `typecheckExpr_preserves_regimeConsistentWithCtx_main` has been
   rebuilt as the `masked := False` wrapper, and the old mode-3 `sorry`
   is gone.  A checkpoint `lake build` succeeds after this repair with
   only the existing `sorry`-related warnings, including the still
   deferred `kwhile` work.

6. **Propagate the fix through downstream `ite` obligations, in
   risk-first order.**
   Do not spend time first polishing the mechanically easier `ite`
   subcases.  The next proof effort should attack the highest-risk
   remaining point directly: mode 3 of
   `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree`
   in `FaultRobustnessProofs.lean`.
   Status: paused at a confirmed Section 7.3 stopping point.  Modes 1,
   2, and 4 of the single-run `ite` proof still look routine under the
   current helper layer.  The active blocker remains mode 3, where
   starting the branch IH under `ctxTrue` or `ctxFalse'` requires
   `consistentWithRegime` for a regime that has just grown by
   interpreting the fresh tag `k`.  That reuses the same
   closure-sensitive obstruction already discovered in step 4: the
   mem/var conjuncts still look transportable, but the closure conjunct
   can activate new captured-variable obligations for `k`, and the
   current premises do not generically discharge them.

   Reviewer feedback confirms the current path ranking:

   - **Preferred in principle:** a masked single-run approach for the
     conservative-join case
   - **Not recommended as primary path:** reviving the broad generic
     `consistentWithRegime_insert_regime_{true,false}` effort, because
     the closure-sensitive regime-growth story appears to require a new
     cross-entry coherence invariant that is not currently present and
     would likely put pressure on the Section 7.2 stable boundaries
   - **Unlikely to help:** a matchGuard-specific "no closures mention
     this tag" lemma, because the tag lifecycle permits dropped regime
     tags to remain referenced in closure predicates

   The implementation finding is now stronger than before: the masked
   single-run idea does **not** stay a one-off outer wrapper.  Because
   the branch body may contain arbitrary subexpressions and the existing
   single-run induction interface in `StepFR.lean`
   (`StepFRSingleRunFinalCleanPcTrue_IH`) is unmasked, the masked path
   would need its own recursive masked IH / theorem family.

   The design choice now is between:

   - **A1: parametric refactor.**  Refactor the per-case single-run
     proofs so they are parametric in the relevant consistency
     predicate, then instantiate that framework with the masked and
     unmasked versions.  This has higher upfront cost but avoids
     maintaining two parallel proof families.
   - **A2: parallel masked proofs.**  Add a second masked single-run
     proof family alongside the current unmasked one.  This avoids the
     refactor but increases duplication and long-term maintenance cost.

   Current recommendation: prefer **A1** if step 6 proceeds, since it
   preserves the Section 7.2 boundaries while avoiding a duplicated
   proof stack.

   Scoping work completed so far:

   - `seq` established the basic theorem-shape fact: a local
     `StepFRSingleRunFinalCleanPcTrueWithCtxCons` can rederive the
     existing unmasked single-run theorem without touching the Section
     7.2 stable boundaries.
   - `vlet`, `app`, and `assign` established the recursive transport
     fact: the context-consistency part of the single-run proof can stay
     behind private hooks rather than forcing the top-level theorem to
     expose the loc / var / closure conjuncts of
     `consistentWithRegime`.  The current picture is:
     `vlet` needs a body-start hook plus a finish hook; `app` needs a
     small family of branch-local hooks; `assign` admits a single
     post-transport hook.

   Those spikes are enough to confirm that the recursive *context*
   transport / reconstruction direction of **A1** is viable.  The
   remaining question is the leaf side of the single-run theorem: how to
   abstract the construction of the final `valueConsistentWithRegime`
   witness while still supporting the masked mode-3 `ite` branch
   instantiation.

   Reviewer follow-up narrows that issue more precisely than the earlier
   "leaf hooks" framing:

   - `var` is the hardest leaf.  Its proof builds final value
     consistency from the **input** `consistentWithRegime` premise,
     using both the `varsRegime` and `closureCapturedVarsRegime`
     conjuncts.
   - `deref` is medium.  Its final value consistency is built from the
     **IH output** consistency, specifically the `locsRegime` side.
   - `newRef` does **not** need context consistency to build its final
     value consistency.  Its result is `noPred`, so the value witness is
     a direct `noTag` proof; the decomposition there is only for
     rebuilding the final context consistency.

   The important structural point is that the single-run recursion needs
   both directions:

   - **context → value:** derive a result-value consistency witness from
     the current context-consistency premise (most sharply in `var`, and
     in a different way in `deref`)
   - **value → context:** use intermediate value consistency to start or
     re-enter downstream contexts (`vlet`, `app`, and related recursive
     cases)

   So the recommended A1 shape is now a **richer bundled interface**,
   not a `CtxCons`-only parameter plus ad hoc per-leaf hooks.  Concretely:

   - Add a second abstract parameter `ValCons` alongside `CtxCons` in
     the parametric single-run framework.
   - Keep the already-discovered value-to-context hooks for recursive
     cases (`vlet`, `app`, and the assign-style post-transport
     situation), but express them in terms of `ValCons` rather than the
     concrete `valueConsistentWithRegime`.
   - Add the missing context-to-value hooks that let leaf / near-leaf
     cases derive `ValCons` from `CtxCons` plus lookup/typing evidence.
   - Define `valueConsistentWithRegimeMasked` as the masked companion to
     `consistentWithRegimeMasked`, mirroring the earlier masked
     `regimeConsistentWithCtx` pattern.
     The completed `var` spike confirms one important detail: the
     masking must not stop at the outer guard-tag case split.  It also
     has to propagate through the closure side of value consistency,
     i.e. through the `closureCapturedVarsRegime` obligations for
     closure values.  The `var` proof uses the closure conjunct of
     `consistentWithRegime` heavily, and closure-captured variables may
     themselves mention the masked branch-local tag `k`.  So the masked
     value companion has to treat those captured-variable obligations in
     a mask-aware way as well; otherwise the `var` leaf would still
     re-open the same closure-sensitive obstruction inside the masked
     branch.

   For the intended masked mode-3 `ite` instantiation:

   - When a value's guard tag is the masked branch-local tag `k`,
     `valueConsistentWithRegimeMasked` can treat that case as
     intentionally masked inside the branch.
   - After the conservative join drops `k` from the output regime,
     recover the ordinary unmasked `valueConsistentWithRegime` directly:
     use `notInRegime` for values guarded by the dropped tag `k`, and
     ordinary transport for all other tags.

   This still stays within Section 7.2: `ValCons` and
   `valueConsistentWithRegimeMasked` are new companion definitions, not
   changes to the existing stable boundary predicates.  But it enlarges
   the confirmed A1 scope from "parametrize by a context-consistency
   predicate" to "parametrize by a paired context/value consistency
   interface".  Treat that enlargement as the active Section 7.3 review
   checkpoint for step 6.

   Bundled-interface spike status:

   - `var`: complete.  `StepFRVar` now contains a local bundled shell
     `StepFRSingleRunFinalCleanPcTrueWithCtxValCons`, the paired hook
     type `VarCtxToValCons`, local masked companions
     `consistentWithRegimeMasked` / `valueConsistentWithRegimeMasked`,
     the masked leaf witness
     `var_valueConsistentWithRegimeMasked_of_typecheck`, and a private
     parametric theorem
     `stepFRSingleRunFinalCleanPcTrue_var_parametric`; the public
     `stepFRSingleRunFinalCleanPcTrue_var` is rederived as the concrete
     unmasked instantiation.  This validated the harder input-side
     context-to-value leaf and confirmed that the masking must extend
     through closure-captured-variable obligations.

   - `deref`: complete.  `StepFRDeref` now uses the same bundled
     `CtxCons` / `ValCons` shape, with a single deref-local post-IH
     hook `DerefCtxToValCons` and a concrete witness
     `deref_valueConsistentWithRegime_of_typecheck`.  The public
     `stepFRSingleRunFinalCleanPcTrue_deref` is rederived from the
     private parametric theorem
     `stepFRSingleRunFinalCleanPcTrue_deref_parametric`.  This
     validates the other context-to-value direction as well: the final
     value witness can be reconstructed from the IH output consistency
     through one bundled hook, without exposing the concrete
     `locsRegime` conjunct at the theorem boundary.

   - `newRef`: complete.  `StepFRNewRef` now follows the same bundled
     shape with a post-write context hook `NewRefCtxConsFinish`, a
     trivial-result value hook `NewRefResultValCons`, and concrete
     witnesses `consistentWithRegime_newRef_finish` and
     `newRef_valueConsistentWithRegime_result`.  The public
     `stepFRSingleRunFinalCleanPcTrue_newRef` is rederived from the
     private parametric theorem
     `stepFRSingleRunFinalCleanPcTrue_newRef_parametric`.  This keeps
     the work on plan: `newRef` did not force a new design review, but
     it did confirm one additional interface detail worth carrying
     forward into the mode-3 rollout.  The bundled path needs both
     kinds of local hooks:
     post-IH `CtxCons` reconstruction hooks for context updates, and
     lightweight `ValCons` constructors for result shapes whose value
     consistency is trivial in the concrete regime semantics.

   Recommended next implementation step: return to step 6 proper and
   push the bundled `CtxCons` / `ValCons` interface back into the
   single-run mode-3 `ite` proof in `FaultRobustnessProofs.lean`.  The
   leaf spikes now cover the three relevant shapes (`var`, `deref`,
   `newRef`), so the next risk-first question is whether the bundled
   interface composes cleanly through the mode-3 branch setup and join.

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
- the symmetric/asymmetric design decision (Section 5.5) is forced by
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
