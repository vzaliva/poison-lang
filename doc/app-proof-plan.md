# `stepFR_app` Proof Notes

Notes:
- Avoid relying on line numbers; they drift frequently.  Use lemma names / TODO tags and `rg`.
- Current branch compiles with `sorry` warnings only (`rg -n -w sorry LeanProofs/` to count).
- Design history (approaches tried, detailed root cause analysis, chronological evolution) is in
  `doc/app-proof-history.md`.

## 1. Problem Statement

Complete the remaining obligations in the `app` case of the fault-robustness step theorem
(`stepFR_app`) in `LeanProofs/StepFRApp.lean`, and all lemmas it depends upon.

**Out of scope** (separate concerns):
- `stepFR_ite_*`, `stepFR_kwhile` — they stay `sorry` for this track; we are not spending
  time proving them here
- `memEnv_lookup_etyp_int` — axiom / issue #70; treated as a given primitive

**Scope guard**:
- App-proof work should not intentionally expand the proof surface so that
  `stepFR_ite_*` / `stepFR_kwhile` become mandatory subtasks.
- If progress on `stepFR_app` appears to require proving those lemmas, stop and reassess the
  proof architecture instead of absorbing them into this plan.

What makes `stepFR_app` hard:
- runtime picks a specific closure alternative (member-oriented reasoning), while
- typing returns a joined result across closure alternatives (`joinTypeResults`), and
- FR proof obligations require transporting runtime/agreement/invariant facts from the selected
  member to the joined result.

## 2. Issues and Blockers

### A. `APP-SIGMA-WITNESS-MISMATCH` (resolved)

The app proof needs deep closure evidence for the synchronized closure member `σcap`, but
inverting the existential in `deepValueQTypProperty.closure` yields a `σcap'` that may differ.
Proving `σcap' = σcap` is invalid in general because joined closure lists can contain multiple
same-body alternatives with different captured typings.

Resolution: `agreeValueUnder.clean_internal_arrow` / `.clean_internal_parrow` now carry direct
member-evidence payloads (`MemberVarsRegimeEvidence` / `MemberCvcrEvidence`) for the synchronized
`(σcap, ρcap)`.  These facts do not mention `tcls`, so they survive `joinETyps` widening.

### B. Closure-alternative mem-join policy (resolved)

Weak mem joins preserved single-sided predicates from unrealized closure alternatives, which is
semantically too optimistic for FR.  `joinTypeResults` now uses `joinMemEnvsStrong` for app/papp.
Ott rules updated to `JoinGStrong`.

### C. Top-level initialization of the deep invariant (resolved)

The third conjunct of `consistentWithRegime` requires deep closure evidence for runtime vars.
Resolved by restricting `InputSpec.vars` to first-order values (`wfInputSpecVarsFirstOrder`) and
adding `trustedVarsClosureRegimeInit` for trusted initial closures.

### D. Member-to-joined qtype transport (resolved for `joinTypeResults`)

The `joinTypeResults` fold can widen the result qtype relative to a selected member (via
`joinETyps` / `joinPredicates`).  The existing `agreeValueUnder_transport_clean` requires
`qt.etyp = qt2.etyp`, which is too weak for member-to-joined transport.

Resolution: Path D direct member-evidence on `agreeValueUnder` (independent of `tcls`) makes
the clean-internal function result case transportable.  Both transport theorems are now proved:
- `joinTypeResults_transport_valueConsistentWithRegime_from_member`
- `joinTypeResults_transport_resultAgreesIfClean_from_member`

### E. Shared-member → joined `consistentWithRegime` (resolved)

Resolved by `joinTypeResults_transport_consistentWithRegime_from_member` and
`joinTypeResults_lookup_member_guardClosure_lookup_compat`.

### F. `wfTypeResult` for all closure alternatives (resolved — decision made)

**Problem**: `join_transport_wfTypeContext` needs `wfTypeResult r` for ALL `r ∈ results` (not
just the runtime-selected shared closure), because `joinMemEnvsStrong` keeps locations from ALL
members and `nextLoc' = max(...)`.  StepFR requires `terminatesTo` witnesses to extract
`wfTypeResult`, but non-shared closures are never executed — no such witnesses exist.

This was the stop/reassess condition in the original plan: "wfTypeResult is needed for ALL
closure results and passing witnesses for non-shared closures is infeasible."

**Root cause**: `wfTypeResult` (`∀ l, res.memEnv'.contains l → l < res.nextLoc'`) is purely
about location bookkeeping in the typechecker output.  It has no semantic/runtime content.
Routing it through StepFR (which requires runtime witnesses) was a category error — StepFR is
the wrong tool for a purely static property.

**Decision**: Prove `typecheckExpr_preserves_wfTypeResult` as a targeted typechecker lemma.
This is a fuel induction matching `typecheckExpr`'s recursion structure, but it is simple:
it only tracks two fields (`memEnv'` keys and `nextLoc'`).  The typechecker was explicitly
designed to maintain this invariant (see `Typecheck.lean` assignment case: "Bump nextLoc'
past all locations in ls to ensure wfTypeResult holds").  This is fundamentally different from
heavy semantic preservation lemmas — it is pure location arithmetic with no runtime semantics.

**Consequences**:
- `StepFR_implies_wfTypeResult` → **delete** (no longer needed).
- `applyFnTClosure_regular_body_wfTypeResult` → **rewrite** to call
  `typecheckExpr_preserves_wfTypeResult` instead of going through StepFR.
- `applyFnTClosure_ok_wfTypeResult` and `mapM_applyFnTClosure_forall_wfTypeResult` → may
  simplify but structural flow stays the same.

### G. Closure member-matching in same-config agreement (resolved)

The false lemmas `closure_same_config_tenv_env` and `peClosure_same_config_tenv_env` were
**deleted** — they assumed `σcap = toCaptured ctx.varEnv` and `env = ρ`, which fails for
closures created in earlier scopes or after joins with multiple alternatives.

Resolution: strengthened `closureCapturedVarsRegime` to carry **both** regime and typing
evidence for the **same** `σcap` member (see `capturedVarsTypingProperty` in
RegimeConsistency.lean).  This eliminates the member-matching problem entirely:
- `agreeValueUnder_same` now takes `closureCapturedVarsRegime` as input and does structural
  induction on the `deepValueQTypProperty` evidence tree
- `agreeCapturedEnv_same_toCaptured` (was sorry'd mutual recursion) deleted — subsumed by
  inline construction within `agreeValueUnder_same`
- All definitions gained a `θ : RealizationMap` parameter: `closureCapturedVarsRegime`,
  `consistentWithRegime`, `valueConsistentWithRegime`, `MemberCvcrEvidence`,
  `trustedVarsClosureRegimeInit`, `FaultRobustnessSpec`
- Transport lemmas extended: `closureCapturedVarsRegime_transport_μ_θ`,
  `memberCvcrEvidence_transport_μ_θ` (new)
- `deepValueQTypProperty.peClosure` gained `Expr.toPExpr? body = some pbody` field

Design details formerly in `doc/app-problem1.md` (deleted after implementation).

## 3. Current Status and Plan

### Checkpoint: 2026-03-06 — Body-IH strategy validated; 4 direct app-local sorry sites remain

Build: **clean** (no errors; sorry-only warnings).

**Current app-local blockers in `stepFR_app`**:
- Arrow dirty-internal fallback
- Arrow `agreeOnClean` locations conjunct in the `¬ qtypCleanUnder` branch
- Parrow dirty-internal fallback
- Parrow `agreeOnClean` locations conjunct in the `¬ qtypCleanUnder` branch

See `doc/app-problem2.md` for the current blocker inventory and rationale.

### What landed since the earlier plan

- `StepFR_single_run` proved via `agreeOnClean_same_config`.
- Clean shared-member path proved for both arrow and parrow.
- `¬ qtypCleanUnder` per-run scaffolding is in place for both arrow and parrow.
- The `agreeOnClean` **variables conjunct** is proved in those `¬ qtypCleanUnder` branches.
- `applyFnTClosure_ok_regimeConsistentWithCtx` and
  `applyPFnTClosure_ok_regimeConsistentWithCtx` are proved.
- `typecheckExpr_preserves_wfTagMeaningCtx_main` now already returns
  `wfTagMeaningCtx ∧ QTypRespectsTagMeaning`; the combined-induction refactor has happened.

### Scope discipline for the current track

- We are **not** trying to clear all transitive `sorry`s in generic declarations.
- In particular, `stepFR_ite_*` and `stepFR_kwhile` stay out of scope and remain `sorry`.
- If app-local work starts pulling those lemmas into the critical path as proof obligations
  we must discharge now, that is a **reassess signal**, not the next task.

### Proof-style rule

- Prefer proving invariant facts **inline inside `stepFR_*` proofs or app-specific closure
  helper lemmas**, where the main induction and runtime evidence already exist.
- Avoid introducing or expanding whole-syntax lemmas of the form
  `typecheckExpr_preserves_<invariant>` unless there is a strong reason they cannot be avoided.
- Reason: those lemmas duplicate syntax induction, force unrelated case analysis, and discard
  runtime information that the `stepFR` proof already has available.
- Keep the `StepFR` statement fixed whenever possible; do not add new invariant-preserving
  premises or conclusions just to support these helper proofs.
- Current justified exception: `typecheckExpr_preserves_wfTypeResult`, because `wfTypeResult`
  must hold for **all** closure alternatives, including non-executed ones, so runtime `StepFR`
  evidence is not enough.

### Status of the supporting lemmas

- `regimeConsistentWithCtx` support is good enough for the current app-local work:
  the app-specific closure helpers are proved, even though the generic theorem still has
  unrelated `ite` mode 3 / `kwhile` holes.
- `wfTagMeaningCtx` / `QTypRespectsTagMeaning` support is partially built:
  the combined theorem exists, but we should only fill further preservation cases if they are
  directly forced by the app-local helpers.  Proving the whole generic theorem, especially its
  `ite` / `kwhile` cases, is not a goal of this track.

### Suspect generic preservation lemmas

These are technically relevant to the broader file state, but they are **not** part of the
intended `doc/app-problem2.md` blocker path and should be treated as deferred unless a narrow
app-local fragment is truly forced:

- `typecheckExpr_preserves_regimeConsistentWithCtx_main`
- `typecheckExpr_preserves_wfTagMeaningCtx_main`
- `typecheckExpr_preserves_QTypRespectsTagMeaning`

Working stance:
- Do **not** make completion of `doc/app-problem2.md` depend on finishing these generic lemmas.
- If one of the app-local holes needs support in this area, prefer:
  - an inline argument inside the relevant `stepFR_app` branch, or
  - a narrow app-specific helper about closure body contexts,
  rather than proving the full whole-syntax theorem.
- Revisit the generic lemmas later, after the blocker in `doc/app-problem2.md` is closed, if
  they still matter for the broader `app` proof cleanup.

### Active plan (risk-first)

1. **Finish arrow dirty-internal fallback**
   - Replace the placeholder pack in the `¬ internalPoisonClean` branch with the same
     per-run `StepFR_single_run` pattern already used in the `¬ qtypCleanUnder` branch.
   - Key difference from dirty-outer: `resultAgreesIfClean` is not vacuous when `p1 = false`.

2. **Finish parrow dirty-internal fallback**
   - Mirror the arrow dirty-internal solution.
   - Reuse as much of the existing `¬ qtypCleanUnder` parrow scaffolding as possible.

3. **Finish the two `agreeOnClean` locations conjuncts**
   - Arrow `¬ qtypCleanUnder` locations conjunct
   - Parrow `¬ qtypCleanUnder` locations conjunct
   - The variables conjunct is already done, so the remaining cross-run work is now strictly
     about locations.

4. **Only add preservation support that directly unblocks app helpers**
   - If `applyFnTClosure_ok_*` / `applyPFnTClosure_ok_*` need more preservation support, fill
     the narrowest cases needed for app progress.
   - Do **not** widen this into a full cleanup of generic `typecheckExpr_preserves_*` theorems.

### Explicit non-goals for this plan

- Proving `stepFR_ite_mode3`
- Proving `stepFR_ite_mode4`
- Proving `stepFR_kwhile`
- Proving every remaining case in generic preservation theorems just because they are present

### Stop / reassess conditions

- If the shortest route to `stepFR_app` starts requiring proofs of `stepFR_ite_*` or
  `stepFR_kwhile`, stop and reassess rather than absorbing those lemmas into this track.
- If a proposed app-proof refactor would increase reliance on generic body theorems with open
  `ite` / `kwhile` cases, reject that refactor or replace it with a narrower app-specific
  helper.
- If the `agreeOnClean` locations conjuncts appear to need a new global invariant about
  poisoned-PC guard cleanliness, pause and reassess before widening the theory surface.

## 4. Design History

See `doc/app-proof-history.md` for full design history: approaches tried and rejected (7
alternatives to Path D), detailed root cause analysis, implementation milestones, and
chronological evolution with commit references.

## Appendix A: Key identifiers

### Core invariants and FR definitions
- `closureCapturedVarsRegime`, `deepValueQTypProperty`, `capturedVarsRegimeProperty`
- `consistentWithRegime`, `valueConsistentWithRegime`
- `agreeCapturedEnv`, `agreeValueUnder`
- `MemberVarsRegimeEvidence`, `MemberCvcrEvidence`
- `trustedVarsClosureRegimeInit`, `wfInputSpecVarsFirstOrder`

### Initialization / top-level bridge
- `consistentRegimeSpec_implies_consistentWithRegime`
- `FaultRobustnessSpec`, `FaultRobustnessSpec_ioFree`

### App proof helpers
- `stepFR_app_arrow_sync_from_clean`
- `memberVarsRegimeEvidence_of_toCaptured`, `memberCvcrEvidence_of_toCaptured`
- `consistentWithRegime_closure_body_start`
- `stepFR_app`
- `applyFnTClosure_ok_wfTypeResult`, `mapM_applyFnTClosure_forall_wfTypeResult`,
  `applyFnTClosure_regular_body_wfTypeResult`
- `applyPFnTClosure_ok_wfTypeResult`, `mapM_applyPFnTClosure_forall_wfTypeResult'`,
  `applyPFnTClosure_regular_body_wfTypeResult` (new — parrow mirrors)
- `applyPFnTClosure_ioFree_extern_fails` (new — parrow extern contradiction)
- `mapM_applyPFnTClosure_forall_wfTagMeaningCtx`,
  `mapM_applyPFnTClosure_forall_regimeConsistentWithCtx`,
  `mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning` (new — parrow mapM lifters)
- `typecheckExpr_preserves_wfTypeResult` (Step 1)
- `typecheckApp_wfTypeResult` (Step 1 residual, now proved)
- `wfTagMeaningCtx_closure_body` (body context wfTagMeaning)

### Same-config agreement
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`, `agreeValueUnder_same`
- `agreeValueUnder_same_aux` (structural induction on `deepValueQTypProperty` tree)
- `valueHasETyp_loc_inv` (avoids dependent elimination in `agreeValueUnder_same` loc cases)
- `valueHasETyp_closure_etyp_arrow`, `valueHasETyp_peClosure_etyp_parrow`
- `capturedVarsTypingProperty` (new — typing evidence for captured vars)
- `deepValueQTypProperty_mono` (moved from FaultRobustnessProofs.lean to RegimeConsistency.lean)

### Member-evidence transport
- `memberVarsRegimeEvidence_monotone`, `memberVarsRegimeEvidence_transport_μ`
- `memberCvcrEvidence_monotone`, `memberCvcrEvidence_transport_μ`
- `memberVarsRegimeEvidence_transport_lookup_back`, `memberCvcrEvidence_transport_lookup_back`
- `closureCapturedVarsRegime_transport_μ_θ`, `memberCvcrEvidence_transport_μ_θ` (new — combined μ+θ transport)

### Agreement transport
- `qtypPredHolds_mem_compat_of_predSatLaws`
- `agreeValueUnder_clean_extends_sameMem`, `agreeValueUnder_clean_extends_transport_mem`
- `agreeCapturedEnv_clean_extends_sameMem`, `agreeCapturedEnv_clean_extends_transport_mem`
- `agreeValueUnder_clean_transport_by_lookupTrueBack`
- `agreeCapturedEnv_transport_by_lookupTrueBack`

### Join / fold transport
- `joinTypeResults`, `joinETyps`, `joinPredicates`, `joinMemEnvsStrong`, `mergeFnTClosures`
- `closureCapturedVarsRegime_weaken_fnTClosures`, `closureCapturedVarsRegime_joinETyps_step`
- `joinTypeResults_closure_cvcr_transport`
- `join_transport_valueConsistentWithRegime_resQual`
- `join_transport_agreeOnClean_from_member`
- `joinTypeResults_transport_valueHasETyp_from_member`
- `joinTypeResults_transport_valueConsistentWithRegime_from_member`
- `joinTypeResults_transport_consistentWithRegime_from_member`
- `joinTypeResults_qualType_arrow_member_from_member`
- `joinTypeResults_qualType_parrow_member_from_member`
- `joinTypeResults_transport_resultAgreesIfClean_from_member`
- `joinTypeResults_QTypRespectsTagMeaning` (proved)
- `joinTypeResults_poison_pred_of_head_true_noPred` (p1=true → joined result poisoned/noPred)
- `resultAgreesIfClean_of_poison_noPred` (vacuous when poison=true ∧ pred=noPred)
- `applyFnTClosure_ok_poison_pred_of_p1_true`, `applyPFnTClosure_ok_poison_pred_of_p1_true`
- `joinPredicates_eq_guardClosure`, `fold_joinPred_guardClosure_init` (in `TypeSafety.lean`)
- `join_transport_wfTagMeaningCtx`, `join_transport_wfTypeContext`,
  `join_transport_regimeConsistentWithCtx` (join transport for context invariants)

### Issue H infrastructure (resolved)
- ~~`agreeOnClean_self`~~ — **not needed**; used existing `agreeOnClean_same_config`
- `StepFR_single_run` — **PROVED** (single-run corollary of StepFR via `agreeOnClean_same_config`)
- `typecheckExpr_preserves_regimeConsistentWithCtx_main` app case — **PROVED** (inline IH)

### Issue tags
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
- `APP-BODY-IH-BLOCKER` (Issue H — body StepFR IH requires same expression for both runs)
