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

- Steps 1 through 5 are complete.
- The symmetric branch-update design remains in use for this iteration.
- `lake build` is green at the current checkpoint, with only the
  expected `sorry` warnings.
- The broad generic regime-growth story for
  `consistentWithRegime_insert_regime_{true,false}` remains deferred:
  the closure-sensitive obstruction identified in step 4 is real, and
  step 6 continues on the approved masked/local path instead.

1. **Redesign the shared clean-lookup theorem.**
   The current transport target in
   `typecheckExpr_clean_lookup_origin_of_pc_true` is false under the
   currently visible invariants, so the theorem must change.  Work in
   the current `main` style: preserve lookup/provenance information and
   keep the existing existential theorem only as a corollary for its
   current callers.
   Status: complete.  `typecheckExpr_clean_lookup_origin_of_pc_true`
   now sits on the split lemmas
   `typecheckExpr_lookup_poison_origin_of_pc_true` and
   `typecheckExpr_lookup_guard_origin_of_pc_true`, with the old
   existential statement retained as a corollary for current callers.

2. **Make the regime-growth design decision early.**
   Re-evaluate symmetric versus asymmetric branch updates while the
   clean-lookup redesign is still in flight.  Do not assume the
   false-branch insertion is worth keeping until the tag-reuse and
   guard-tag analysis say it is.
   Status: complete for the current iteration.  No concrete obstruction
   has forced the asymmetric fallback, so the implementation continues
   with the symmetric branch-update design unless later proof evidence
   changes that call.

3. **Re-introduce the `R.bound` bridge in the split layout.**
   Re-home or redesign `matchGuard_ok_tag_from_ctx`,
   `matchGuard_tag_in_bound`, and the bounded-tags invariant they need.
   The output of this phase should be an active path from successful
   `matchGuard` to `k < ctx.regime.bound`.
   Status: complete.  The shared bounded-tags invariant
   `predTagsBoundedInCtx` and the split-layout bridge lemmas
   `matchGuard_ok_tag_from_ctx` / `matchGuard_tag_in_bound` are in
   place and now give an active path from successful `matchGuard` to
   `k < ctx.regime.bound`.

4. **Implement the regime-growth transfer lemmas for the chosen
   design.**
   This includes the split-layout versions of
   `tagEnvConsistentWithRegime_insert_*_with_regime` and
   `consistentWithRegime_insert_regime_{true,false}` as needed, with
   `PredSatLaws.match_iff` wired into the actual proof sites.
   Status: partially complete under the narrowed path.  The local
   simultaneous-insert helpers landed, but the broad generic
   `consistentWithRegime_insert_regime_{true,false}` work stays
   deferred because the closure conjunct can activate new
   captured-variable obligations for the newly interpreted tag `k`.

5. **Close the local mode-3 preservation gap for
   `regimeConsistentWithCtx`.**
   Repair
   `typecheckExpr_preserves_regimeConsistentWithCtx_main` using the
   existing tagEnv insert lemmas together with the step-3 bound bridge
   and the minimal simultaneous-insert lemmas from step 4.  Treat this
   as a local repair to land after the higher-risk blockers above.
   Status: complete.  The local repair now uses the recursive masked
   preservation theorem
   `typecheckExpr_preserves_regimeConsistentWithCtxMasked_main`, and
   the original unmasked theorem is rebuilt as the `masked := False`
   wrapper.

6. **Propagate the fix through downstream `ite` obligations, in
   risk-first order.**
   Do not spend time first polishing the mechanically easier `ite`
   subcases.  The next proof effort should attack the highest-risk
   remaining point directly: mode 3 of
   `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree`
   in `FaultRobustnessProofs.lean`.
   Status: active.  The closure-sensitive obstruction from step 4 means
   the remaining `ite` mode-3 work is proceeding on the approved local
   masked path, not by reviving the broad generic regime-growth lemmas.

   Current design choice:

   - Use **A1**: a parametric single-run framework over a paired
     context/value consistency interface (`CtxCons` / `ValCons`)
   - Keep the theorem concrete at the top level over
     `consistentWithRegimeMasked` /
     `valueConsistentWithRegimeMasked`
   - Do **not** pursue the broad generic
     `consistentWithRegime_insert_regime_{true,false}` path unless a
     later review explicitly changes direction

   Relevant completed infrastructure for step 6:

   - The recursive single-run combinator surface is already lifted to
     the paired `CtxCons` / `ValCons` interface.
   - The shared paired single-run predicate and public parametric case
     wrappers live in `StepFR.lean` and the `StepFR*` files.
   - `valueConsistentWithRegimeMasked` and the matching masked
     runtime-consistency layer now live in shared scope.
   - The shared masked transport layer is in place for lookup-back,
     monotonicity, memory / `θ`, and predicate / `etyp` transport over
     the masked closure/value predicates.
   - The cheap masked hook-export batch is complete:
     `stepFRVar_ctxToValCons_masked`,
     `stepFRDeref_ctxToValCons_masked`,
     `stepFRNewRef_ctxConsFinish_masked`,
     `stepFRNewRef_resultValCons_masked`, and
     `stepFRAssign_resultValCons_masked`.
   - The masked `vlet` / `assign` hook layer is also complete:
     `stepFRVlet_ctxConsBodyStart_masked`,
     `stepFRVlet_ctxConsFinish_masked`,
     `stepFRVlet_valConsFinish_masked`, and
     `stepFRAssign_ctxConsPostTransport_masked`.
   - The masked `app` hook layer is complete:
     `stepFRApp_closureBodyStart_masked`,
     `stepFRApp_pClosureBodyStart_masked`,
     `stepFRApp_memberCtxCons_masked`,
     `stepFRApp_joinCtxConsFromMember_masked`,
     `stepFRApp_bodyResultValCons_masked`, and
     `stepFRApp_joinValConsFromMember_masked`.
   - The first same-state support piece for the concrete masked theorem
     is complete:
     `singleRunFinalCleanWitness_of_same_state_param` in `StepFR.lean`
     and `stepFRSingleRunFinalCleanPcTrue_literal_masked` in
     `StepFRLiteral.lean`.
   - The remaining simple concrete masked support cases are complete:
     `stepFRSingleRunFinalCleanPcTrue_unaryop_masked`,
     `stepFRSingleRunFinalCleanPcTrue_op_masked`,
     `stepFRSingleRunFinalCleanPcTrue_fn_masked`, and
     `stepFRSingleRunFinalCleanPcTrue_pfn_masked`.
   - The shared masked-to-unmasked conversion layer is in place for the
     post-join phase:
     `consistentWithRegimeMasked_unmask` and
     `valueConsistentWithRegimeMasked_unmask`.
   - The masked `ite` transport layer is now in place in
     `StepFRIte.lean` for the remaining single-run theorem work:
     `consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true`,
     `consistentWithRegimeMasked_join_from_left`, and
     `consistentWithRegimeMasked_join_from_right`.
   - The top-level single-run proof is now refactored onto the
     concrete masked recursive family in
     `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree`,
     with the existing public theorem rebuilt as the `masked := False`
     wrapper.

   Remaining work, in current risk-first order:

   1. use the masked recursive family to close the concrete single-run
      mode-3 `ite` theorem in `FaultRobustnessProofs.lean`.

   Step 6 should still pause for review if this masked/local path turns
   out to require changing the stable boundary definitions in Section
   7.2, or if the concrete masked mode-3 theorem exposes a new
   obstruction beyond proof-engineering scope.

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
