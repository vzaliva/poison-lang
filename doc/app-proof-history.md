# `stepFR_app` Design History

This file preserves the full design history for the `stepFR_app` proof work: approaches tried
and rejected, detailed issue analysis, implementation milestones, and the chronological evolution
of the closure-invariant design.  The active planning document is `doc/app-proof-plan.md`.

## Root Cause Analysis: Selector Transport Across Merged Closure Lists

`resultAgreesIfClean` unfolds to `qtypCleanUnder R qt -> agreeValueUnder ...`.
For function-typed results:
- Dirty internal poison after join: `dirty_internal_arrow` only needs `valueHasETyp`
  (already proved).  No problem.
- Clean internal poison after join: `clean_internal_arrow` needs
  `ArrowMemberCvcrSelector predSat st1 st2 p tcls ...`, parameterized on `(p, tcls)`.
  This was the blocker.

We have a selector for `(p_src, tcls_src)`.  We need one for `(p_joined, tcls_joined)` where
`tcls_src ⊆ tcls_joined` (via `mergeFnTClosures`).

**Why the selector cannot be transported from narrow to wide closure list:**

The selector takes `closureCapturedVarsRegime predSat R qtFun μ v` (where
`qtFun.etyp = ETyp.arrow st1 st2 p tcls`) as input and extracts `varsRegime` /
`closureCapturedVarsRegime` for the specific `σcap`.  To use the old selector with the wider
type, we would need to *narrow* `closureCapturedVarsRegime` from `tcls_joined` to `tcls_src` --
the opposite direction from `closureCapturedVarsRegime_weaken_fnTClosures`.

Narrowing fails because `deepValueQTypProperty.closure` uses existential quantification over the
matching closure alternative (`FnTClosure.regular x body σcap ∈ tcls`).  When `tcls` is the
wider list, the existential can pick a `σcap'` from `tcls_joined \ tcls_src` that does not exist
in `tcls_src`.  We cannot then feed this evidence to the old selector which expects
`qtFun.etyp = ETyp.arrow st1 st2 p_src tcls_src`.

The `arrowMemberCvcrSelector_singleton` construction works precisely because the singleton list
`[FnTClosure.regular x body σcap]` forces `σcap' = σcap` (only one member to match).  Once the
closure list grows past a singleton (via any join), this reasoning breaks.

## Approaches Tried and Rejected

### 1. Predicate-driven `closureCapturedVarsRegime` (commit `87878ef`, Feb 19)

First version, gated on `qt.pred = guardClosure k ...`.  Added to every
`valueConsistentWithRegime` constructor.  Problem: in `ioFree` mode, closures have
`qt.pred = noPred`, so the predicate gate never fires and closures are invisible to the
invariant.  Replaced by the etyp-driven redesign.

### 2. Selectors parameterized on `(p, tcls)` (commits `8d23a9d`, `1f626f0`, Feb 23)

`ArrowMemberCvcrSelector` / `PArrowMemberCvcrSelector` on `agreeValueUnder.clean_internal_arrow`
/ `.clean_internal_parrow`.  Selectors parameterized on `(st1, st2, p, tcls)` and universally
quantified over `(R, μ)`.  Constructed via `arrowMemberCvcrSelector_singleton` at lambda sites
(singleton closure list forces `σcap' = σcap`).

Solved the sigma mismatch at the app extraction point but could not survive `joinETyps`
widening because the selector methods take `closureCapturedVarsRegime` at the current
`(p, tcls)` as input, and closure-list narrowing fails due to the existential in
`deepValueQTypProperty`.

### 3. Naive closure-list-polymorphic selector (post `e8faf62`, Feb 24)

Drop `tcls`/`p` from selector parameters, add membership argument.  Fails at construction
time: the resulting selector needs to answer queries for arbitrary closure lists, which
re-introduces the existential witness problem at `arrowMemberCvcrSelector_singleton`.

### 4. Alternative selector input signature (Feb 25)

Selectors taking `capturedVarsRegimeProperty` for the specific `σcap` as input.  Shifts the
sigma mismatch to the caller (who must extract `capturedVarsRegimeProperty` from the
function-level CVCR, hitting the same existential).

### 5. Hybrid existential+universal `deepValueQTypProperty` (analysed Feb 25)

Keep existential (for widening) and add universal (for narrowing).  Analysis revealed a
critical caveat: since `closureCapturedVarsRegime` wraps both conjuncts as a unit, the
universal conjunct faces the same widening problem as the full universal.  The member-to-joined
transport has evidence for only one member, so the universal part gets lost during widening.
Path A reduces to Path C for the hard part.

### 6. Full universal `deepValueQTypProperty` (analysed at `118ad35`, Feb 23)

Replace existential with universal.  Cleanest invariant shape but largest blast radius.  Likely
precision killer: forces proving regime facts for typing artifacts in merged closure lists that
are not the intended witness for the runtime closure.  The `118ad35` analysis noted that "a pure
universal-over-all-matching-members invariant may be too strong semantically" because joined
closure lists contain typing artifacts.  Deferred.

### 7. App-specific transport (Path B, considered Feb 25)

Inline the transport into `stepFR_app` directly.  Avoids touching `deepValueQTypProperty` or
selectors, but the clean-internal function case likely still requires selector-style reasoning
internally.  Does not fix `stepFR_ite` modes 3/4.  High risk as a dead-end: the same gap
blocks other join points, and you pay the redesign cost later plus duplicated reasoning.

## Path D: The Implemented Solution

### Design

Replace the selector payloads on `agreeValueUnder.clean_internal_arrow` /
`.clean_internal_parrow` with the member-aligned FACTS themselves: the `varsRegime` and
`closureCapturedVarsRegime` conclusions for the specific synchronized `(σcap, ρcap)`, at the
current `R` and `μ`.

Concretely, replace:
```
hcvcrSel₁ : ArrowMemberCvcrSelector predSat st1 st2 p tcls x body σcap ρcap₁
hcvcrSel₂ : ArrowMemberCvcrSelector predSat st1 st2 p tcls x body σcap ρcap₂
```
with payloads like:
```
hCapVR₁ : ∀ y qt_y k_y v_y,
  (VarTypeEnv.ofCaptured σcap).lookup y = some qt_y →
  ρcap₁.lookup y = some v_y →
  qtypGuardTag qt_y = some k_y → R.lookup? k_y ≠ none →
  varsRegime predSat R μ₁ ρcap₁ (y, qt_y)
hCapCVCR₁ : ∀ y qt_y v_y,
  (VarTypeEnv.ofCaptured σcap).lookup y = some qt_y →
  ρcap₁.lookup y = some v_y →
  closureCapturedVarsRegime predSat R qt_y μ₁ v_y
```
(and mirrored for run 2).

### Why this works

- These facts do NOT mention `tcls`.  When `joinETyps` widens the closure list, the only field
  that changes is `hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls`; the member evidence passes
  through unchanged because it is about the specific captured vars, not the surrounding type.
- Construction at the lambda production site is straightforward: the closure list is a singleton,
  so `σcap` is unique, and the facts are extracted directly from `consistentWithRegime` of the
  enclosing context.  No sigma mismatch.
- Transport across regime/memory changes uses existing monotonicity lemmas
  (`closureCapturedVarsRegime_monotone`, `closureCapturedVarsRegime_transport_μ`, and analogous
  `varsRegime` transport).
- At the app use site, the stored facts are read directly from `agreeValueUnder` -- no inversion
  of `closureCapturedVarsRegime` for the function value, so no sigma mismatch.

Semantically, this matches FR better than universal invariants: once the proof has synchronized
on a concrete member `(x, body, σcap)`, the member evidence is durable ghost state.  Widening
the type's closure set does not invalidate facts about the chosen member.

### Implementation steps (completed)

1. Removed `ArrowMemberCvcrSelector` / `PArrowMemberCvcrSelector` definitions.
2. Replaced selector fields on `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow`
   with direct member-evidence payloads (`MemberVarsRegimeEvidence` / `MemberCvcrEvidence`).
3. Updated lambda production sites (`stepFR_fn` / `stepFR_pfn`) to construct the direct facts
   from `consistentWithRegime`.
4. Migrated all `agreeValueUnder_clean_extends` callers to explicit wrapper APIs
   (`_transport_mem`, same-memory wrappers) before the swap, making the constructor change
   wrapper-internal.
5. Repaired `agreeValueUnder` regime/memory transport wrappers using explicit member-evidence
   transport helpers (monotone / memory transport / lookup-back).
6. Proved `joinTypeResults_transport_resultAgreesIfClean_from_member` -- the function-typed
   clean-internal case is now straightforward since the member evidence is `tcls`-free.

### Key insights from the proof

- Function `...guard` branches are structurally impossible and can be discharged by function-shape
  contradiction.
- Non-function branches and ref branches transport with existing shape / membership infrastructure.
- Dirty-internal function branches transport with `valueHasETyp` + internal-poison/shape transport.
- The clean-internal arrow/parrow branches use direct member-evidence lookup-back transport plus
  closure-member fold decomposition helpers.

## Implementation Milestones

### Pre-Path-D status snapshot

The strong mem-join change fixed the earlier app/papp mem-env design mismatch.  The next blocker
was qtype-widening transport across `joinTypeResults` for FR agreement/consistency predicates.

Investigation results at this point:
- Making selectors closure-list-polymorphic was attempted and rejected (existential-root witness
  problem re-appears at selector construction time).
- `joinTypeResults_transport_valueConsistentWithRegime_from_member` was still a sorry stub.
- `joinTypeResults_transport_resultAgreesIfClean_from_member` was still a sorry stub.

### Path D prep work

- Direct member-evidence payload types (`MemberVarsRegimeEvidence`, `MemberCvcrEvidence`)
- Lambda-site construction helpers from `consistentWithRegime`
- Lambda production-site feasibility checks in `stepFR_fn` / `stepFR_pfn`
- Member-evidence transport helpers: `memberVarsRegimeEvidence_monotone`,
  `memberVarsRegimeEvidence_transport_μ`, `memberCvcrEvidence_monotone`,
  `memberCvcrEvidence_transport_μ`

### Transport wrapper migration

All `agreeValueUnder_clean_extends` callers (6 sites) and `agreeValueUnder_clean_transport_by_cleanBack`
callers (2 sites) were migrated to explicit wrapper APIs before the Path D swap:
- `agreeValueUnder_clean_extends_transport_mem`
- `agreeValueUnder_clean_transport_by_lookupTrueBack`
- Corresponding `agreeCapturedEnv` variants

This made the constructor swap wrapper-internal rather than a cascade across all call sites.

### Path D constructor swap

Swap completed; `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow` now carry
`MemberVarsRegimeEvidence` / `MemberCvcrEvidence`.  Transport wrappers repaired using
member-evidence transport helpers.  `stepFR_app` arrow clean-sync plumbing updated.

### Join transport proof completion

Both transport theorems proved:
- `joinTypeResults_transport_valueConsistentWithRegime_from_member`
- `joinTypeResults_transport_resultAgreesIfClean_from_member`

Post-merge cleanup: pre-Path-D selector code removed, transitional naming cleaned up,
shared predicate-join helpers consolidated in `TypeSafety.lean`.

## Chronological Design Evolution

1. Predicate-driven `closureCapturedVarsRegime` (`87878ef`, Feb 19)
2. Etyp-driven redesign (`4884a6b`, Feb 20)
3. Sigma mismatch identified (`cbaf119`, Feb 21)
4. Universal vs existential analysis (`118ad35`, Feb 23)
5. Member-coupled selectors introduced (`8d23a9d`, `3406ce4`, Feb 23)
6. Selectors expanded with `varsRegime` conjunct (`1f626f0`, Feb 23)
7. Naive closure-list-polymorphic selector attempted (post `e8faf62`, Feb 24)
8. Alternative selector input signature explored (Feb 25)
9. Hybrid existential+universal analysis (Feb 25)
10. Path D direct member-evidence implemented (Feb 25)
11. Wrapper-first transport migration + Path D swap (Feb 25)
12. Path D join-transport proof completion (Feb 25)

## Issue H History: `StepFR_single_run` and "Don't Derive Static Facts From StepFR"

This file mostly records the Path D redesign needed to make the clean-internal function
result transportable across closure-list joins.

After Path D, the remaining `stepFR_app` blocker shifted to **fallback branches** where the
two runs can execute **different** closure bodies (notably when function outer poison
`p1 = true`).  In those branches the body `StepFR` IH cannot be applied directly because
`StepFR` requires both runs to evaluate the **same expression**.

### What was tried

- Commit `dba4db3` (Feb 26) introduced a helper lemma `StepFR_single_run` in
  `FaultRobustnessProofs.lean`.  The idea was to instantiate `StepFR` with both runs equal
  (`μ₀ = μ₁`, `cf₀ = cf₁`, `o₀ = o₁`) and discharge the precondition using same-config
  `agreeOnClean` (at the time via an `agreeOnClean_self`/same-config lemma).
- This is **logically sound** as a packaging lemma *when a `terminatesTo` witness exists* for
  the expression being stepped.

### Why it was removed / what went wrong at the time

- Commit `ec05def` (Feb 27) removed `StepFR_single_run` during a checkpoint refactor.
  The helper was not the core blocker, and at that point the surrounding same-config
  infrastructure was still in flux (mutual recursion between `agreeValueUnder_same` and
  captured-env agreement; and later `closure_same_config_tenv_env`/`peClosure_same_config_tenv_env`
  were discovered to be false and removed after the member-matching redesign).
- Separately, the project tried to route **purely static** obligations through StepFR
  (notably `StepFR_implies_wfTypeResult` for `applyFnTClosure_ok_wfTypeResult`), but this has
  no viable proof path because StepFR fundamentally requires runtime evidence (`terminatesTo`)
  and runtime context instantiation premises.  This was recognized explicitly and the lemma
  was deleted in commit `02e7fcb`, replaced by a direct typechecker fuel-induction lemma
  `typecheckExpr_preserves_wfTypeResult` in `TypeSafety.lean`.

### Implication for the current proposal (avoid going in circles)

- Reintroducing a `StepFR_single_run` corollary is fine *only* for **executed** closure bodies
  where a per-run `terminatesTo` witness is available from runtime inversion of application.
  This is a legitimate way to obtain per-run packs (`valueHasETyp`, `runtimeInstantiatesCtx`,
  `consistentWithRegime`, etc.) needed in fallback branches.
- `StepFR_single_run` does **not** solve left-biased join/preservation lemmas for
  **non-executed** closure alternatives, because there is no `terminatesTo` witness for those.
  Those lemmas must remain static (typechecker-only) or be avoided by restructuring.

## Issue I History: App-result provenance gate widened

The narrow dirty-internal non-function app blocker was later removed by a typing change.
Non-function app rules now use `AppPred (join p1 p) P3` in Ott, and the implementation/proof
side matches this with `normalizeAppResultByProvenance (joinPoison p1 p)`.

Effect for future reference:

- when `p = true`, the final non-function app result drops the body predicate even if `p1 = false`
- this removes the retained-predicate path that previously forced cross-run agreement in the
  dirty-internal fallback branches
- the earlier standalone note `doc/app-typing.proposal` is obsolete after landing this change

## Issue J History: Different-body framing experiments (March 6)

After the app-typing change landed, the remaining app-specific blocker moved to the
different-body location obligations inside `stepFR_app`.

What was tried:

- First framing proposal: keep the fix app-local by proving that every clean post-body
  location is inherited from the pre-body memory typing environment, then combine that with
  unary preservation lemmas.
- This failed.  Under poisoned `pc`, `typecheckVar` can preserve a guard predicate,
  `typecheckNewRef` can store it on a fresh location, and `joinMemEnvsStrong` can preserve
  it on a two-sided fresh join entry.  So a fresh clean location can survive the final join.
- The local route was then restated as an inherited-vs-symmetric-fresh split: inherited
  locations handled by unary facts, symmetric-fresh locations handled in the final
  `some / some` branch.

What was learned:

- Final recombination is not the blocker.  `join_transport_agreeOnClean_from_member` already
  packages the joined clean-location proof once the branch can supply either a source-member
  witness or final `none / none`.
- The real blocker is the unary `θ` bridge for inherited clean locations: from pre-body
  `both_unrealized`, show the chosen post-body maps also leave the location unrealized.
- A later implementation attempt tightened this further: the missing object is best viewed as
  a shared unary theorem in `StepFR.lean` that constructs a canonical post-run realization map,
  rather than another local `stepFR_app` lemma built around an existential witness.
- The current local interface does not provide this:
  - `StepFR_single_run` only exposes an existential post-run `θ'`
  - `wfExtendsMap` preserves existing `some` bindings, not `none`
  - `runtimeInstantiatesCtx` permits realizing old typed locations
  - `freshLoc_not_realized` only applies to fresh `l >= nextLoc`
- The only obvious local `parrow` escape hatch also stalled: reusing the pre-body maps as
  final witnesses would require reverse/shrink transport for `valueHasETyp` and
  `valueConsistentWithRegime`, while the library only exposes extension transport.
- The same attempt did identify reusable fragments for the unary theorem:
  `theta_not_contains_if_not_in_memEnv`, the old-location transport in `stepFR_newRef`, the
  final-clean-implies-old-clean assignment argument in `StepFRAssign`, and the pure-body
  memory / regime bridges used by the `parrow` path.

Decision:

- stop the app-local framing route at that go/no-go gate
- move the active plan to broader unary proof infrastructure in `doc/app-proof-plan.md`
- keep the focused blocker write-up in `doc/app-framing-proposal.md`

## Issue K History: Former `app-problem2.md` snapshot

The deleted file `doc/app-problem2.md` recorded an intermediate checkpoint right after the
app-typing change landed.

Its main claim was:

- once the app-typing fix was in, and once a framing fix was chosen, no app-specific
  conceptual blocker should remain; the four app holes should reduce to ordinary proof
  integration

That snapshot is useful only as a record of what was believed at that stage.

What later invalidated it:

- the inheritance-only framing lemma turned out to be false
- the restated app-local framing route then stopped at the unary `θ` bridge
- so the remaining work did not collapse to local proof plumbing after all

During March 6 housekeeping, the file was merged into this history log and deleted so the
active planning surface stayed smaller.

## Issue L History: Single-run witness redesign attempts (March 7)

After the app-local location packaging was closed, the remaining blocker moved to the
single-run witness used in the different-body `arrow` / `parrow` fallback branches.

### Failed path 1: strengthen `StepFR_single_run` directly

What was tried:

- Replace the old input-clean property with an output-conditioned one:
  inherited location `l`, final lookup `res.memEnv'.lookup l = some qt_out`,
  final cleanness `qtypCleanUnder res.regime' qt_out`, then preserve the runtime cell.
- Rewire the app fallback sites to consume that narrower witness.

What was learned:

- This fixes the statement mismatch in the old
  `PreservesInheritedCleanLocsOneRun`, but it does **not** solve witness selection.
- `StepFR_single_run_core` still exposes only an existential post-run realization map `θ'`.
- The narrowed preservation fact must hold for the **same** `θ'` that the app proof later uses.
  It cannot be recovered after the fact from an arbitrary witness extracted from plain `StepFR`.

Decision:

- keep the output-conditioned statement shape
- stop trying to derive it as a thin wrapper over `StepFR_single_run_core`

### Failed path 2: widen `StepFR` itself

What was considered:

- Add the narrowed single-run witness property directly to the global `StepFR` contract, so
  every case proof would produce it uniformly.

Why it was rejected:

- `StepFR` is the shared two-run contract used by essentially every `stepFR_*` lemma.
- Widening it would force nontrivial proof work in many unrelated cases:
  `assign`, `ite`, `seq`, `vlet`, `op`, `newRef`, and eventually `kwhile`.
- The new property is only needed in app-body fallback reasoning, so this would pay a large
  global cost for a local consumer.

Decision:

- do **not** widen `StepFR`
- keep `StepFR` as the shared two-run theorem
- move the extra witness-producing fact to the induction side

### Current accepted direction

The accepted architecture is now:

- keep `StepFR_single_run_core` as the sound extraction wrapper over `StepFR`
- treat the current `StepFR_single_run` wrapper as historical / transitional only
- define a separate induction-side theorem
  `StepFRSingleRunFinalCleanPcTrue`
  for expressions typed under `pc = true`
- thread that theorem through the strong induction IH used by `stepFR_app`
- rewire the app fallback sites to consume that IH directly

Supporting work completed at this checkpoint:

- generic unary composition lemma:
  `PreservesInheritedCleanLocOneRun.trans`
- induction-side theorem surface:
  `StepFRSingleRunFinalCleanPcTrue`
- induction-side IH surface:
  `StepFRSingleRunFinalCleanPcTrue_IH`

## Historical Identifiers (removed from code)

- `ArrowMemberCvcrSelector`
- `PArrowMemberCvcrSelector`
- `arrowMemberCvcrSelector_singleton`
- `stepFR_app_arrow_member_varsRegime_extract`
- `stepFR_app_arrow_member_cvcr_extract`
