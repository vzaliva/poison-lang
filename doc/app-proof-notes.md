# `stepFR_app` Proof Handoff Notes

This document is a handoff summary for the remaining `stepFR_app` proof work.
It is written to support both:
- review of the current approach, and
- continued implementation by another contributor.

Notes:
- Avoid relying on line numbers in this file; they drift frequently.
- Use lemma names / TODO tags and `rg` to locate code.
- Current branch compiles with `sorry` warnings only.

## 1. Goal (`stepFR_app` proof)

Complete the remaining obligations in the `app` case of the fault-robustness step theorem (`stepFR_app`) in `LeanProofs/FaultRobustnessProofs.lean`.

Current focus:
- I/O-free `app` path first
- arrow clean/shared-closure branch first (highest complexity)
- parrow mirror second

What makes `stepFR_app` hard:
- runtime picks a specific closure alternative (member-oriented reasoning), while
- typing returns a joined result across closure alternatives (`joinTypeResults`), and
- FR proof obligations require transporting runtime/agreement/invariant facts from the selected member to the joined result.

## 2. Key Changes Made (important moving forward)

This section lists only changes that matter for the remaining proof work. Historical experiments and failed approaches are intentionally omitted.

### A. Captured-env invariants were redesigned and are now available where app needs them

Key changes:
- `valueConsistentWithRegime` now carries `closureCapturedVarsRegime` in every constructor.
- `closureCapturedVarsRegime` was redesigned to be `etyp`-driven (via deep closure traversal), not predicate-driven.
- `consistentWithRegime` now has a third conjunct: deep closure-captured-vars evidence for runtime variables.

Why this matters:
- This is the main invariant pipeline that makes closure-body reasoning possible in `stepFR_app`.
- It fixes the `ioFree` closure blind spot (`qt.pred = noPred` no longer hides closures from the invariant).

### B. Captured-env agreement was strengthened (typed runtime bindings)

`agreeCapturedEnv` now carries enough information to recover:
- runtime lookup witnesses for captured bindings, and
- `valueHasETyp` evidence for captured values.

Why this matters:
- It supports reconstruction of `runtimeInstantiatesCtx` for closure body contexts from synchronized closure agreement.

### C. Member-coupled selector payloads were added to `agreeValueUnder` (Phase 1 core fix)

New logical predicates (in `LeanProofs/FaultRobustness.lean`):
- `ArrowMemberCvcrSelector`
- `PArrowMemberCvcrSelector`

`agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow` now carry these selectors.

Why this matters:
- This solved the arrow-path `APP-SIGMA-WITNESS-MISMATCH` without changing the `StepFR` boundary.
- The selectors connect the synchronized closure member chosen by app reasoning to the deep captured-env closure evidence required for body entry.

Important design detail:
- The selectors are regime-polymorphic and memory-polymorphic so they survive existing FR transport lemmas.
  This is not only design intent; it has been validated in the current branch because the existing
  `agreeValueUnder` transport stack (including regime/memory transport used by the arrow Phase 1 fix)
  compiles and is used successfully with the selector payloads.
- They are inductive logical predicates (not executable defs), which fits project proof style and keeps the logical/executable boundary clear.

### D. Body-start helper interface is already correct

`consistentWithRegime_closure_body_start` already takes the right obligations:
- captured-member deep evidence (`h_cap_cvcr`)
- argument deep evidence (`h_arg_cvcr`)

Why this matters:
- The remaining app work is not a body-start helper redesign problem.
- The remaining problems are mainly transport and qtype-join proof infrastructure.

### E. `app`/`papp` closure-alternative joins now use strong mem join (FR-semantic fix)

`joinTypeResults` now uses `joinMemEnvsStrong` for closure-alternative joins (`app` / `papp`).

Effect:
- single-sided `memEnv` entries keep type/poison,
- single-sided predicates are dropped (`Predicate.noPred`).

Why this matters:
- It matches FR semantics: post-join predicate facts should be stable across hidden closure alternatives.
- It removes the earlier design mismatch where joined `memEnv` could contain predicate facts from unrealized alternatives.

Spec/documentation alignment:
- Ott app/papp multi-closure rules now use `JoinGStrong`.
- `while` join policy remains unchanged for now (deferred, explicitly commented in Lean + Ott).

### F. Phase 0 (invariant initialization) is closed at the top-level boundary

Two top-level policy changes were made:
- `InputSpec.vars` is restricted to first-order (non-function) values via `wfInputSpecVarsFirstOrder`.
- A new explicit top-level premise handles trusted initial closures:
  `trustedVarsClosureRegimeInit`.

The bridge theorem (`consistentRegimeSpec_implies_consistentWithRegime`) was strengthened accordingly.

Why this matters:
- Initialization soundness for the new deep invariant is no longer an app-local blocker.
- The hidden-state issue for trusted initial closures is now explicit at the FR boundary (where it belongs).

## 3. Current Status

### Completed / working

- Phase 0 soundness gate is closed (with explicit top-level trusted-initialization premise).
- Phase 1 arrow sigma mismatch is resolved using selector-based member-coupled evidence.
- `stepFR_app_arrow_member_cvcr_extract` is proved.
- `joinTypeResults` app/papp mem join policy has been switched to strong join, and spec docs were updated.
- Member-to-joined transport for `valueHasETyp` is now proved:
  - `joinTypeResults_transport_valueHasETyp_from_member`
- Member-to-joined transport for `valueConsistentWithRegime` is now proved:
  - `joinTypeResults_transport_valueConsistentWithRegime_from_member`

### Remaining proof work in `stepFR_app`

Open items (conceptual groups):
- Shared-member -> joined-result transport for:
  - `resultAgreesIfClean`
- `VARSREGIME_GAP`:
  shared-member final `consistentWithRegime` -> joined output `consistentWithRegime`
- Remaining app proof plumbing:
  - fallback `hOutMapChoice` branches
  - outer join/static obligations after `hOutMapChoice`
  - parrow mirror cleanup

### Important status update (current frontier)

The strong mem-join change fixed the earlier app/papp mem-env design mismatch.

The next blocker is different:
- qtype-widening transport across `joinTypeResults` (especially `joinETyps` + `joinPredicates`) for FR agreement/consistency predicates.

This is now the highest-impact issue blocking the remaining member->joined transport work
(in particular `resultAgreesIfClean` transport).

Latest investigation result:
- A straightforward version of Option 1 (making selectors closure-list/polymorphic and passing
  membership into the current closure list as an explicit selector-method argument) was attempted
  and rejected.
- It makes the selector too strong to construct from existing evidence (the existential-root witness
  problem reappears at selector construction time, including singleton-selector construction).

### Latest implementation checkpoint (Path D swap complete; join transport theorem closed)

The codebase has now advanced beyond the status described above.

What is now done:
- Path D prep work is implemented and compiles:
  - direct member-evidence payload types (`MemberVarsRegimeEvidence`, `MemberCvcrEvidence`)
  - lambda-site construction helpers from `consistentWithRegime`
  - lambda production-site feasibility checks in `stepFR_fn` / `stepFR_pfn`
- `joinTypeResults_transport_valueConsistentWithRegime_from_member` is proved (no longer a stub).
- All `agreeValueUnder_clean_extends` callers were migrated through explicit wrapper APIs before the
  swap (`..._transport_mem`, same-memory wrappers), so the Path D change became wrapper-internal.
- Path D constructor refactor is now implemented:
  - `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow` carry direct member evidence
    (`MemberVarsRegimeEvidence` / `MemberCvcrEvidence`) instead of selector payloads.
  - `stepFR_app` arrow clean-sync plumbing now carries direct member evidence through the shared
    synchronized member witness (no selector extraction on the main arrow clean path).
- The `agreeValueUnder` regime/memory transport wrapper path has been repaired on the Path D
  baseline using explicit member-evidence transport hypotheses (lookup-back and memory-compat
  wrappers).
- `joinTypeResults_transport_resultAgreesIfClean_from_member` is now proved on the Path D
  baseline (including the two former clean-internal arrow/parrow blocker branches).
- The final proof uses a small reusable helper cluster:
  - `agreeCapturedEnv_transport_by_lookupTrueBack`
  - `joinTypeResults_qualType_arrow_member_from_member`
  - `joinTypeResults_qualType_parrow_member_from_member`

Key proof-state result (milestone):
- The member->joined qtype transport pair is now fully proved:
  - `joinTypeResults_transport_valueConsistentWithRegime_from_member`
  - `joinTypeResults_transport_resultAgreesIfClean_from_member`
- This closes the Path D proof-completion target that previously remained after the constructor swap.

What was confirmed during the theorem split:
- Function `...guard` branches are structurally impossible and can be discharged by function-shape
  contradiction.
- Non-function branches and ref branches transport with existing shape / membership infrastructure.
- Dirty-internal function branches transport with `valueHasETyp` + internal-poison/shape transport.

Build / proof-check status at this checkpoint:
- `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeds.
- `lake build` succeeds.
- `sorry` count in `LeanProofs/FaultRobustnessProofs.lean` is reduced relative to `HEAD`
  (`45` vs `47`), and no new `sorry` lines were introduced in the Path D swap/refactor/proof diff.

## 4. Key Issues (with analysis)

### Issue A: `APP-SIGMA-WITNESS-MISMATCH` (resolved for arrow path)

Summary:
- The app proof had a synchronized closure member witness (`σcap`) from clean agreement.
- Deep closure evidence was available only through an existential witness, which could choose a different captured env (`σcap'`).
- Attempting to prove `σcap' = σcap` is invalid in general because joined closure lists can contain multiple same-body alternatives with different captured typings.

Resolution used in this branch:
- Strengthen clean-internal function agreement to carry member-aligned ghost evidence for the
  synchronized closure member.
- Current Path D baseline stores the member-specific `varsRegime` / `closureCapturedVarsRegime`
  facts directly on `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow` (instead of
  selector methods), avoiding witness realignment.

Why this is the right kind of strengthening:
- It is internal (no `StepFR` boundary change).
- It matches FR semantics for clean application: once a particular synchronized member is selected, the proof should have the deep evidence for that member.

### Issue B: app/papp closure-alternative mem-join policy (resolved)

Summary:
- Weak mem joins preserved single-sided predicates from unrealized closure alternatives.
- FR uses post-join facts as robust guarantees, so this was semantically too optimistic.

Resolution used in this branch:
- `joinTypeResults` now uses strong mem joins for app/papp (`joinMemEnvsStrong`).
- Ott app/papp rules were updated to `JoinGStrong`.

Result:
- The old mem-env unrealized-alternative blocker is removed.
- Remaining blockers should be treated as proof-infrastructure issues, not mem-join semantics issues.

### Issue C: Top-level initialization of the deep invariant (resolved with explicit premise)

Summary:
- The new third conjunct of `consistentWithRegime` requires deep closure evidence for runtime vars.
- Flat `InputSpec` assumptions alone do not describe hidden captured envs of trusted initial closures.

Resolution used in this branch:
- Restrict `InputSpec.vars` to first-order values.
- Add `trustedVarsClosureRegimeInit` for trusted initial closures.

Result:
- Phase 0 is closed.
- This is no longer part of the `stepFR_app` risk frontier.

### Issue D: Member->joined `resultAgreesIfClean` qtype transport (resolved for `joinTypeResults`)

This was the key proof-infrastructure blocker on the Path D baseline.

Status update:
- Path D constructor refactor on `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow`
  is implemented and compiles.
- The transport lemma cascade was repaired enough to restore a green build on the Path D baseline
  (wrapper-internal changes + explicit member-evidence transport hooks).
- `joinTypeResults_transport_valueConsistentWithRegime_from_member` is now proved.
- `joinTypeResults_transport_resultAgreesIfClean_from_member` is now proved (including the two
  former Path D blocker branches: clean-internal arrow/parrow under `qtypCleanUnder.clean`).

### What was blocked (now closed for this theorem)

Previously blocked theorem:
- `joinTypeResults_transport_resultAgreesIfClean_from_member`

Current follow-on work:
- Reuse the same helper pattern at other join points (`stepFR_ite` modes 3/4).
- Continue downstream plumbing (`VARSREGIME_GAP`, app fallback branches) now that the qtype
  transport layer is complete for the `joinTypeResults` member->joined path.

### The two transports have very different difficulty (key finding)

**`valueConsistentWithRegime` transport was provable with existing infrastructure (now done).**
For function-typed results, `joinTypeResults` forces `res.qualType.pred = noPred` (the `finalPred`
match in `joinTypeResults`).  This means `qtypGuardTag res.qualType = none`, so the `noTag`
constructor of `valueConsistentWithRegime` applies.  The only obligation is
`closureCapturedVarsRegime`, which the existing `closureCapturedVarsRegime_joinETyps_step` +
`closureCapturedVarsRegime_weaken_fnTClosures'` already handle (existential widening).
For non-function types, CVCR is trivially `nonClosure`.

**`resultAgreesIfClean` transport was blocked by a structural problem in the selector design.**
Path D removes that design blocker by storing direct member evidence on `agreeValueUnder`, and the
post-swap theorem is now proved for the `joinTypeResults` member->joined transport path.

### Why the existing transport lemmas are insufficient

`joinTypeResults` can widen the result qtype relative to a selected member:
- `res.qualType.etyp` may be `joinETyps ...`, not literally equal to `src.qualType.etyp`
- `res.qualType.pred` may be weakened by `joinPredicates`

Existing helper gap:
- `agreeValueUnder_transport_clean` handles clean transport when `qt.etyp = qt2.etyp`
- This is too weak for member->joined transport where `etyp` is widened

Helpful consequence of the strong app/papp mem-join change:
- Since app/papp joins now drop single-sided predicates from `memEnv`, joined predicate obligations are
  generally weaker on the conclusion side.
- This should make parts of the qtype-widening transport easier (especially predicate-side conclusion
  obligations), even though it does not by itself solve the `agreeValueUnder` qtype-widening gap.

### Why this matters for FR logic (not just proof mechanics)

FR agreement/consistency obligations are phrased over the joined output qtype.
For app/papp closure joins, the joined qtype is intentionally a conservative summary of alternatives.

Therefore, the proof infrastructure needs a principled way to say:
- if a value/result is FR-consistent for a member qtype,
- then it remains FR-consistent for the joined qtype (under the join semantics)

This is a semantic transport obligation, not just a local tactic gap.

### Historical root cause (pre-Path D): selector transport across merged closure lists

`resultAgreesIfClean` unfolds to `qtypCleanUnder R qt -> agreeValueUnder ...`.
For function-typed results:
- Dirty internal poison after join: `dirty_internal_arrow` only needs `valueHasETyp`
  (already proved).  No problem.
- Clean internal poison after join: `clean_internal_arrow` needs
  `ArrowMemberCvcrSelector predSat st1 st2 p tcls ...`, parameterized on `(p, tcls)`.
  This is the blocker.

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

**Chronological design evolution (from branch history):**

1. *Predicate-driven `closureCapturedVarsRegime`* (commit `87878ef`, Feb 19): first version, gated
   on `qt.pred = guardClosure k ...`.  Added to every `valueConsistentWithRegime` constructor.
   Problem discovered: in `ioFree` mode, closures have `qt.pred = noPred`, so the predicate gate
   never fires and closures are invisible to the invariant.

2. *Etyp-driven redesign* (commit `4884a6b`, Feb 20): `closureCapturedVarsRegime` moved to
   `RegimeConsistency.lean` as `deepValueQTypProperty` + `capturedVarsRegimeProperty` +
   `closureCapturedVarsRegime`.  Driven by `qt.etyp` (arrow/parrow closure lists), not `qt.pred`.
   Fixes the `ioFree` blind spot.  `consistentWithRegime` extended with third conjunct.
   Documented at `cbaf119` (Feb 21) with detailed sorry inventory.

3. *Sigma mismatch identified* (commit `cbaf119`, Feb 21): `APP-SIGMA-WITNESS-MISMATCH` first
   documented.  Inverting the existential in `deepValueQTypProperty.closure` yields `σcap'` that
   may differ from the synchronized `σcap`.

4. *Universal vs existential analysis* (commit `118ad35`, Feb 23): thorough analysis of replacing
   existential with universal.  Conclusion: "a pure universal-over-all-matching-members invariant
   may be too strong semantically" because joined closure lists contain typing artifacts.  Breaks
   widening (`closureCapturedVarsRegime_weaken_fnTClosures`).  Recommended member-coupled evidence
   on a synchronized relation instead.  Selectors were temporarily REMOVED from code at this
   commit to explore alternatives.

5. *Member-coupled selectors introduced* (commit `8d23a9d`, Feb 23, then `3406ce4`): selectors
   re-added to `agreeValueUnder.clean_internal_arrow/parrow` with one CVCR conjunct.  Selectors
   parameterized on `(st1, st2, p, tcls)` and universally quantified over `(R, μ)`.  Constructed
   via `arrowMemberCvcrSelector_singleton` at lambda sites (singleton closure list forces
   `σcap' = σcap`).  Phase 0 resolved with `trustedVarsClosureRegimeInit`.

6. *Selectors expanded with `varsRegime` conjunct* (commit `1f626f0`, Feb 23): selectors now
   carry two methods (varsRegime extraction + recursive CVCR extraction).  Strong mem-join
   (`joinMemEnvsStrong`) introduced for app/papp closure-alternative joins.

7. *Naive closure-list-polymorphic selector attempted* (post `e8faf62`, Feb 24): attempted
   conceptually -- drop `tcls`/`p` from selector parameters, add membership argument.  Fails at
   construction time: the resulting selector needs to answer queries for arbitrary closure lists,
   which re-introduces the existential witness problem at `arrowMemberCvcrSelector_singleton`.

8. *Alternative input signature explored* (this session): making selectors take
   `capturedVarsRegimeProperty` for the specific `σcap` as input.  Shifts the sigma mismatch to
   the caller (who must extract `capturedVarsRegimeProperty` from the function-level CVCR,
   hitting the same existential).

9. *Hybrid existential+universal `deepValueQTypProperty`*: not yet attempted in code.  The idea
   is to keep the existential conjunct (for widening) and add a universal conjunct (for
   narrowing).  Analysis (this session) revealed a critical caveat: the universal conjunct
   faces the same widening problem as the pure universal (Path C), so the hybrid does not
   cleanly decouple widening from narrowing.

10. *Direct member-evidence on `agreeValueUnder`* (implemented on current branch): instead of
    storing selector methods (parameterized by `tcls`, consuming `closureCapturedVarsRegime` at the
    current type), the clean-internal arrow/parrow constructors now store the member-aligned FACTS
    themselves -- the `varsRegime` and `closureCapturedVarsRegime` conclusions for the specific
    `σcap`, at the current `R` and `μ`.  These facts do not mention `tcls`, so join widening is
    stable at the constructor payload level.

11. *Wrapper-first transport migration + Path D swap repair* (implemented): call sites were
    migrated to explicit memory/regime transport wrappers before the constructor swap, then the swap
    was completed and the wrapper internals were repaired using direct member-evidence transport
    helpers (monotone / memory transport / lookup-back).  The codebase builds on the Path D
    baseline.

12. *Path D join-transport proof completion* (current checkpoint): the two focused
    `joinTypeResults_transport_resultAgreesIfClean_from_member` clean-internal function branches
    were filled using direct member-evidence lookup-back transport plus closure-member fold
    decomposition helpers.  This closes the `joinTypeResults` member->joined qtype transport pair
    and reduces `LeanProofs/FaultRobustnessProofs.lean` `sorry` count by 2 (relative to `HEAD`).

### This is not app-specific -- it affects all join points

`stepFR_ite` modes 3 and 4 are both `sorry`.  They face the same structural issue: transporting
`agreeValueUnder` across a qtype widened by `joinETyps`.  The selector transport problem blocks
all join points (app, if, while) uniformly.  Any fix should target the root cause rather than
working around it in `stepFR_app` alone.

### Issue E: `VARSREGIME_GAP` remains open, but likely after the qtype transport layer

`VARSREGIME_GAP` is still open (shared-member final `consistentWithRegime` -> joined output `consistentWithRegime`).

Current assessment:
- After the app/papp strong-join change, this is no longer the earlier mem-env semantic mismatch.
- It is now the next proof-infrastructure target after the member->joined qtype transport pair was closed.

Recommendation:
- Treat it as the next target after propagating the now-proved transport pattern to the remaining
  join points (`stepFR_ite` modes 3/4).

## 5. High-Level Plan to Proceed (Risk-First)

Planning principles:
- Keep `StepFR` boundary unchanged unless all internal strengthening options fail.
- Any fix to the selector transport problem should apply to all join points (app, if, while), not just app.
- Address design-level transport gaps before resuming proof plumbing.

### Immediate action (completed): prove `valueConsistentWithRegime` transport

This stub is likely provable with existing infrastructure (see "two stubs have very different
difficulty" above).  Proving it first unblocks downstream work and validates the fold decomposition
pattern for the harder stub.

Status:
- Completed.  `joinTypeResults_transport_valueConsistentWithRegime_from_member` is now proved.
- Subsequent milestones on this branch also completed the Path D constructor refactor and proved
  `joinTypeResults_transport_resultAgreesIfClean_from_member`.
- See "Recommended next steps" below for the post-transport-gap plan.

### Candidate approaches for `resultAgreesIfClean` transport

Four approaches have been considered.  Path D is recommended; the others are retained for
reference with their known issues.

Note on reachability: the clean-internal function result case IS reachable -- it occurs whenever
`ite` returns a closure under `pc = false` (`joinETyps` merges closure sets and keeps internal
poison `false` when both branches are clean).  This cannot be side-stepped.

**Path D (recommended): Direct member-evidence on `agreeValueUnder`, independent of `tcls`**

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

Why this works:
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

Key advantage: fixes all join points (app, if, while) without changing `deepValueQTypProperty`
or any CVCR widening/transport infrastructure.  Lower blast radius than Path A/C.

Key cost: all existing `agreeValueUnder` transport lemmas that case-split on the arrow/parrow
constructors need to handle the new fields.  For lemmas that do not change `R` or `μ`, the
fields pass through unchanged.  For lemmas that change `R` or `μ`, an additional monotonicity
call is needed per field.  This is mechanical but touches a number of lemmas.

Implementation plan:
1. Remove `ArrowMemberCvcrSelector` / `PArrowMemberCvcrSelector` definitions.
2. Replace selector fields on `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow`
   with direct member-evidence payloads.
3. Update `arrowMemberCvcrSelector_singleton` call sites (lambda production sites in
   `stepFR_fn` / `stepFR_pfn`) to construct the direct facts from `consistentWithRegime`.
4. Update `agreeValueUnder` transport lemmas to carry the new fields (regime/memory transport
   via monotonicity where needed).
5. Update `stepFR_app_arrow_member_cvcr_extract` (or inline it) to read the stored facts
   directly from `agreeValueUnder` instead of invoking a selector method.
6. Prove `joinTypeResults_transport_resultAgreesIfClean_from_member` -- the function-typed
   clean-internal case should now be straightforward since the member evidence is `tcls`-free.

**Path A: Hybrid existential+universal `deepValueQTypProperty`**

Add a universal conjunct to `deepValueQTypProperty.closure` alongside the existing existential.

Critical caveat: since `closureCapturedVarsRegime` wraps both conjuncts as a unit, the universal
conjunct faces the same widening problem as Path C.  The member-to-joined transport only has
evidence for one member, so the universal part gets lost during widening.  Path A reduces to
Path C for the hard part.

**Path B: App-specific transport (avoid generic selector widening)**

Inline the transport into `stepFR_app` directly.  Avoids touching `deepValueQTypProperty` or
selectors, but the clean-internal function case likely still requires selector-style reasoning
internally.  Does not fix `stepFR_ite` modes 3/4.  High risk as a dead-end: the same gap
blocks other join points, and you pay the redesign cost later plus duplicated reasoning.

**Path C: Full universal `deepValueQTypProperty`**

Replace existential with universal.  Cleanest invariant shape but largest blast radius and
likely precision killer: it forces proving regime facts for typing artifacts in merged closure
lists that are not the intended witness for the runtime closure (see `118ad35` analysis).

### Recommended next steps

Path D constructor refactor, wrapper-internal transport cascade repair, and the `joinTypeResults`
member->joined qtype transport pair are now complete.  The remaining work is propagation and
downstream proof plumbing on this baseline.

1. Reuse the same member->joined transport pattern at other join points (especially
   `stepFR_ite` modes 3/4), using the new helper cluster
   (`agreeCapturedEnv_transport_by_lookupTrueBack`,
   `joinTypeResults_qualType_arrow_member_from_member`,
   `joinTypeResults_qualType_parrow_member_from_member`) as the template.

2. Close `VARSREGIME_GAP` (shared-member final `consistentWithRegime` -> joined output
   `consistentWithRegime`) now that the qtype transport layer is no longer the blocker.

3. Finish remaining app proof plumbing (`hOutMapChoice` fallback branches and outer join/static
   obligations) on top of the completed Path D transport baseline.

4. Factor any theorem-local join helpers back into a more shared transport layer only if reuse
   pressure appears at the next join-point proof (avoid premature generalization).

Notes on ordering:
- `joinTypeResults_transport_valueConsistentWithRegime_from_member` and
  `joinTypeResults_transport_resultAgreesIfClean_from_member` are both proved and stable.
- Immediate risk has shifted from theorem design to proof reuse / propagation at the remaining join
  points.
- `stepFR_ite` modes 3/4 remain the best validation target for whether the Path D helper pattern
  generalizes cleanly beyond the app join path.

### Subsequent phases (now active)

**Phase 2: close `VARSREGIME_GAP`**

Once the transport layer is in place:
- prove shared-member final `consistentWithRegime` -> joined output `consistentWithRegime`
- use the strong mem-join helper layer for memory-side cases
- use the new member->joined qtype transport lemmas for value-level obligations as needed

**Phase 3: finish remaining app proof plumbing**

- close fallback `hOutMapChoice` branches
- finish outer join/static obligations after `hOutMapChoice`
- complete arrow path end-to-end
- then mirror the final fixes into parrow path

### Stop / reassess conditions (important for risk management)

Stop and discuss before continuing if any of the following happens:
- Reusing the new Path D join-transport helper pattern at `stepFR_ite` modes 3/4 requires a
  materially different theorem interface (not just local specialization of the current helper
  cluster).
- Closing `VARSREGIME_GAP` requires strengthening `StepFR`-level statements or changing the proof
  boundary (instead of using the now-complete qtype transport layer as-is).
- Helper generalization starts causing churn across many callers/theorems before a second concrete
  reuse site is closed (signal to defer abstraction and finish the next proof first).

## Appendix A: Key identifiers to search (no line numbers)

Search these names/tags to navigate the code quickly.

### Core invariants and FR definitions
- `closureCapturedVarsRegime`
- `deepValueQTypProperty`
- `capturedVarsRegimeProperty`
- `consistentWithRegime`
- `valueConsistentWithRegime`
- `agreeCapturedEnv`
- `agreeValueUnder`
- `MemberVarsRegimeEvidence`
- `MemberCvcrEvidence`
- `ArrowMemberCvcrSelector` (legacy / transition helper)
- `PArrowMemberCvcrSelector` (legacy / transition helper)
- `trustedVarsClosureRegimeInit`
- `wfInputSpecVarsFirstOrder`

### Initialization / top-level bridge
- `consistentRegimeSpec_implies_consistentWithRegime`
- `FaultRobustnessSpec`
- `FaultRobustnessSpec_ioFree`

### App proof helpers (arrow path)
- `stepFR_app_arrow_sync_from_clean`
- `stepFR_app_arrow_member_varsRegime_extract` (legacy helper)
- `stepFR_app_arrow_member_cvcr_extract` (legacy helper)
- `arrowMemberCvcrSelector_singleton` (legacy helper)
- `memberVarsRegimeEvidence_of_toCaptured`
- `memberCvcrEvidence_of_toCaptured`
- `consistentWithRegime_closure_body_start`
- `stepFR_app`

### Join / transport infrastructure
- `qtypPredHolds_mem_compat_of_predSatLaws`
- `agreeValueUnder_clean_extends_sameMem`
- `agreeValueUnder_clean_extends_transport_mem`
- `agreeCapturedEnv_clean_extends_sameMem`
- `agreeCapturedEnv_clean_extends_transport_mem`
- `agreeValueUnder_clean_transport_by_lookupTrueBack`
- `agreeCapturedEnv_transport_by_lookupTrueBack`
- `memberVarsRegimeEvidence_monotone`
- `memberVarsRegimeEvidence_transport_μ`
- `memberCvcrEvidence_monotone`
- `memberCvcrEvidence_transport_μ`
- `memberVarsRegimeEvidence_transport_lookup_back`
- `memberCvcrEvidence_transport_lookup_back`
- `joinTypeResults`
- `joinETyps`
- `joinPredicates`
- `joinMemEnvsStrong`
- `mergeFnTClosures`
- `closureCapturedVarsRegime_weaken_fnTClosures`
- `closureCapturedVarsRegime_joinETyps_step`
- `joinTypeResults_closure_cvcr_transport`
- `join_transport_valueConsistentWithRegime_resQual`
- `join_transport_agreeOnClean_from_member`
- `joinTypeResults_transport_valueHasETyp_from_member`
- `joinTypeResults_transport_valueConsistentWithRegime_from_member`
- `joinTypeResults_qualType_arrow_member_from_member`
- `joinTypeResults_qualType_parrow_member_from_member`
- `joinTypeResults_transport_resultAgreesIfClean_from_member`

### Related join points (same structural issue)
- `stepFR_ite_mode3`
- `stepFR_ite_mode4`

### Active issue tags in comments / notes
- `APP-SIGMA-WITNESS-MISMATCH` (resolved in arrow path)
- `VARSREGIME_GAP` (active)
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)

## Appendix B: Reviewer checklist (approach review)

If reviewing the current direction rather than implementing immediately, the main review questions are:

1. Does the Path D member-evidence design (direct facts on `agreeValueUnder`, independent of
   `tcls`) correctly model the FR semantics of synchronized closure members as durable ghost
   state?
2. Are the existing monotonicity lemmas (`closureCapturedVarsRegime_monotone`,
   `closureCapturedVarsRegime_transport_μ`) sufficient to transport the new member-evidence
   fields through all `agreeValueUnder` transport lemmas, or are new transport helpers needed?
3. At the lambda production site (`stepFR_fn`, `stepFR_pfn`), are captured-var `varsRegime` and
   `closureCapturedVarsRegime` facts directly available from `consistentWithRegime` of the
   enclosing context, or is additional extraction infrastructure needed?
4. Is the strong mem-join policy for app/papp (`joinMemEnvsStrong`) the right FR-semantic choice
   (with while deferred)?
5. Does Path D unblock `stepFR_ite` modes 3/4 as expected (same structural fix applies to all
   join points)?
