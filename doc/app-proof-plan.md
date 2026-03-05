# `stepFR_app` Proof Notes

Notes:
- Avoid relying on line numbers; they drift frequently.  Use lemma names / TODO tags and `rg`.
- Current branch compiles with `sorry` warnings only (`rg -n -w sorry LeanProofs/` to count).
- Design history (approaches tried, detailed root cause analysis, chronological evolution) is in
  `doc/app-proof-history.md`.

## 1. Problem Statement

Complete the remaining obligations in the `app` case of the fault-robustness step theorem
(`stepFR_app`) in `LeanProofs/FaultRobustnessProofs.lean`, and all lemmas it depends upon.

**Out of scope** (separate concerns):
- `stepFR_ite_mode3`, `stepFR_ite_mode4` — branch case analysis, different proof
- `stepFR_kwhile` — while-loop fixpoint reasoning, deferred
- `memEnv_lookup_etyp_int` — axiom / issue #70; treated as a given primitive
- `valueHasETyp_det` — not called anywhere in the `stepFR_app` chain

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

### Checkpoint: 2026-03-05 — Body IH partially resolved, 8 sorry keywords remain in chain

Build: **clean** (no errors; sorry-only warnings).

**Sorry count**: 10 sorry statements total in FaultRobustnessProofs.lean (down from 20 at
last commit).  Of these, **8 sorry keywords** are in the stepFR_app dependency chain.

Steps completed since last checkpoint:
- **Issue H (partial)**: `StepFR_single_run` proved via `agreeOnClean_same_config` ✓
- **Step 5/6 (partial)**: Arrow clean path fully proved.  Parrow clean path fully proved.
  Parrow ¬qtypCleanUnder full 15-element StepFR tuple proved.
- **Step 4 (partial)**: `regimeConsistentWithCtx` preservation RESOLVED:
  - `applyFnTClosure_ok_regimeConsistentWithCtx` proved (was sorry)
  - `applyPFnTClosure_ok_regimeConsistentWithCtx` proved (was sorry)
  - `typecheckExpr_preserves_regimeConsistentWithCtx_main` app case proved
    (circular dependency resolved by inlining with `IH'` from strong induction)
- **Investigation**: Confirmed dirty-internal (¬internalPoisonClean) is NOT contradictory
  with qtypCleanUnder for function types (p ≠ p1); genuinely needs per-run body IH.

#### In-scope sorrys (stepFR_app dependency chain)

**`FaultRobustnessProofs.lean`** — 8 sorry keywords in chain:

| Group | Lemma(s) | Keywords | Risk | Step |
|---|---|---|---|---|
| Preservation (FnT) | `applyFnTClosure_ok_wfTagMeaningCtx` | 1 | Needs static induction | 4 |
| Preservation (FnT) | `applyFnTClosure_ok_QTypRespectsTagMeaning` | 1 | Needs static induction | 4 |
| Preservation (PFnT) | `applyPFnTClosure_ok_wfTagMeaningCtx` | 1 | Needs static induction | 4 |
| Preservation (PFnT) | `applyPFnTClosure_ok_QTypRespectsTagMeaning` | 1 | Needs static induction | 4 |
| Arrow dirty-internal + agreeOnClean | sorry pack at line ~25428 | 1 | Blocked on Step 5 | 5 |
| Arrow agreeOnClean | `by sorry` at line ~26098 | 1 | Blocked on Step 5 | 5 |
| Parrow dirty-internal | sorry at line ~27932 | 1 | Blocked on Step 5 | 6 |
| Parrow agreeOnClean | `by sorry` at line ~28643 | 1 | Blocked on Step 5 | 6 |

**Resolved since last checkpoint** (no longer sorry):
- `applyFnTClosure_ok_regimeConsistentWithCtx` ✓
- `applyPFnTClosure_ok_regimeConsistentWithCtx` ✓
- `typecheckExpr_preserves_regimeConsistentWithCtx_main` app case ✓
- All arrow clean path sorrys ✓
- All parrow clean path sorrys ✓
- Parrow ¬qtypCleanUnder per-run obligations (except agreeOnClean) ✓

**`TypeSafety.lean`** — 0 sorrys in stepFR_app chain.

#### Out-of-scope sorrys (not targeted here)

| Lemma | File | Keywords | Reason |
|---|---|---|---|
| `stepFR_ite_mode3` | FaultRobustnessProofs | 1 | Different concern |
| `stepFR_ite_mode4` | FaultRobustnessProofs | 1 | Different concern |
| `stepFR_kwhile` | FaultRobustnessProofs | 1 | Deferred; while-loop fixpoint |
| `valueHasETyp_det` | TypeSafety | 1 | Likely false; unused |

### Checkpoint: 2026-03-04 — Steps 1–3 complete, build clean

Build: **clean** (no errors; sorry-only warnings).

Steps completed:
- **Step 1**: `typecheckExpr_preserves_wfTypeResult` proved; `StepFR_implies_wfTypeResult` deleted;
  `applyFnTClosure_regular_body_wfTypeResult` rewritten; signatures simplified.
  One planned sorry remains in `typecheckApp_wfTypeResult`.
- **Step 2 + 3 (Issue G)**: Resolved via closure member-matching fix.
  `closure_same_config_tenv_env` and `peClosure_same_config_tenv_env` deleted (false).
  `agreeCapturedEnv_same_toCaptured` deleted (subsumed).
  `agreeValueUnder_same` rewritten with structural induction on `deepValueQTypProperty` tree.
  All θ-transport sorry's in `stepFR_app` arrow clean path resolved.

#### Out-of-scope sorrys (not targeted here)

| Lemma | File | Reason |
|---|---|---|
| `stepFR_ite_mode3`, `stepFR_ite_mode4` | FaultRobustnessProofs | Different concern |
| `stepFR_kwhile` | FaultRobustnessProofs | Deferred; while-loop fixpoint |
| `memEnv_lookup_etyp_int` | TypeSafety | Axiom / issue #70 |
| `valueHasETyp_det` | TypeSafety | Not used in stepFR_app chain |

### What was done (prior sessions)

- `stepFR_deref`: proved.
- `joinTypeResults_QTypRespectsTagMeaning` + `QTypRespectsTagMeaning_joinStep`: proved.
- `hTm_ctx''` in `applyFnTClosure_ok_wfTypeResult`: proved.
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`: proved.
- Phase 0 (invariant initialization), Path D / APP-SIGMA-WITNESS-MISMATCH, strong mem-join,
  member-to-joined transport cascade: all proved.
- **Step 1 (Issue F)**: `typecheckExpr_preserves_wfTypeResult` proved (TypeSafety.lean);
  `StepFR_implies_wfTypeResult` deleted; `applyFnTClosure_regular_body_wfTypeResult` rewritten;
  `applyFnTClosure_ok_wfTypeResult` / `mapM_applyFnTClosure_forall_wfTypeResult` signatures
  simplified (dropped StepFR/PredSat/TagMeaning parameters).
- **Steps 2+3 (Issue G)**: Closure member-matching fix implemented.  Key changes:
  - `closureCapturedVarsRegime` strengthened: `P = capturedVarsRegimeProperty ∧ capturedVarsTypingProperty`
  - `θ` parameter added to `closureCapturedVarsRegime`, `consistentWithRegime`,
    `valueConsistentWithRegime`, `MemberCvcrEvidence`, `trustedVarsClosureRegimeInit`,
    `FaultRobustnessSpec`
  - `deepValueQTypProperty.peClosure` gained `Expr.toPExpr? body = some pbody` field
  - `agreeValueUnder_same` rewritten: takes `closureCapturedVarsRegime` as input, structural
    induction on `deepValueQTypProperty` tree (no mutual recursion needed)
  - Deleted: `closure_same_config_tenv_env`, `peClosure_same_config_tenv_env` (false),
    `agreeCapturedEnv_same_toCaptured` (subsumed)
  - New transport lemmas: `closureCapturedVarsRegime_transport_μ_θ`, `memberCvcrEvidence_transport_μ_θ`
  - All θ-transport sorry's in arrow clean path resolved via chained transport:
    `closureCapturedVarsRegime_transport_etyp` → `_monotone` → `_transport_μ_θ`

### Plan (risk-first)

**Step 1: Prove `typecheckExpr_preserves_wfTypeResult` — Issue F** ✓ DONE

Proved `typecheckExpr_preserves_wfTypeResult` in TypeSafety.lean (~800 lines, fuel induction).
All sub-tasks completed:
1. ✓ `applyFnTClosure_regular_body_wfTypeResult` rewritten to use the new lemma directly.
2. ✓ `StepFR_implies_wfTypeResult` deleted.
3. ✓ Signatures of `applyFnTClosure_ok_wfTypeResult` / `mapM_applyFnTClosure_forall_wfTypeResult`
   simplified (dropped StepFR IH, PredSat, TagMeaning parameters).
4. ✓ `typecheckApp_wfTypeResult` proved (Phase 4).

**Step 2+3: Close same-config agreement — Issue G** ✓ DONE

Resolved by the closure member-matching fix (strengthened `closureCapturedVarsRegime`).
- False lemmas `closure_same_config_tenv_env` / `peClosure_same_config_tenv_env` deleted.
- `agreeCapturedEnv_same_toCaptured` deleted (mutual recursion eliminated).
- `agreeValueUnder_same` rewritten with structural induction on `deepValueQTypProperty` tree.
- θ-transport sorry's in arrow clean path resolved.
- All definitions gained `θ` parameter; ~105 call sites updated across FaultRobustnessProofs.lean.

**Step 4: Preservation lemmas** — PARTIALLY RESOLVED

Originally six lemmas with sorry (3 FnTClosure + 3 PFnTClosure).
Two resolved, four remain:

- ✓ `applyFnTClosure_ok_regimeConsistentWithCtx` — PROVED (circular dependency resolved)
- ✓ `applyPFnTClosure_ok_regimeConsistentWithCtx` — PROVED (mirror)
- `applyFnTClosure_ok_wfTagMeaningCtx` — sorry (needs `typecheckExpr_preserves_wfTagMeaningCtx`)
- `applyFnTClosure_ok_QTypRespectsTagMeaning` — sorry (needs `typecheckExpr_preserves_QTypRespectsTagMeaning`)
- `applyPFnTClosure_ok_wfTagMeaningCtx` — sorry (mirror)
- `applyPFnTClosure_ok_QTypRespectsTagMeaning` — sorry (mirror)

**Resolution for `regimeConsistentWithCtx`**: The circular dependency (main induction → helpers
→ wrapper → main) was broken by inlining the helper logic in the app case using `IH'` from
strong induction.  Both FnTClosure and PFnTClosure cases handled in lines 17497-17649.

**Remaining**: `wfTagMeaningCtx` and `QTypRespectsTagMeaning` need similar
`typecheckExpr_preserves_*` theorems (~500 lines each).  The same inline-IH approach can
resolve the circular dependency.  However, the `wfTagMeaningCtx` proof also depends on how
mode 3 `ite` creates new tags (same blocker as out-of-scope `stepFR_ite_mode3`).

**Step 5: Arrow fallback branches** — BLOCKED on body IH infrastructure

Two sub-branches:

**5a: ¬ `internalPoisonClean`** (1 sorry at line ~24544):
`qtypCleanUnder` holds (p1 = false), so the existing shared-body sync logic applies.  The
only difference from the clean path is `resultAgreesIfClean`, which uses `dirty_internal_arrow`
(needs only `valueHasETyp`).  Most of the pack should come from the shared body IH.

**5b: ¬ `qtypCleanUnder`** (9 sorrys at lines ~24578–24586):
p1 = true, res.poison = true, res.pred = noPred.  Runs may pick different closures.  Need
per-run body evidence via `StepFR_single_run` + join transport.  Cross-run `agreeOnClean`
needs a pc-based argument (no new clean entries under poisoned PC).  `resultAgreesIfClean`
already proved vacuously.

**Step 6: Parrow mirror** — PARTIALLY DONE

Infrastructure created (10 helpers).  4 of 13 refine block sorrys filled (join transport for
QTypRespectsTagMeaning, wfTagMeaningCtx, wfTypeContext, regimeConsistentWithCtx).

Remaining: 9 sorrys in refine block (same structure as arrow fallback) + 2 sorrys at
clean/dirty split (shared-body IH + `dirty_internal_parrow`).

### Issue H: Body StepFR IH evidence for fallback paths — PARTIALLY RESOLVED

See **`doc/app-problem2.md`** for detailed analysis (revised 2026-03-05).

**Resolved**:
- ✓ `StepFR_single_run` proved via `agreeOnClean_same_config`.
- ✓ Per-run body IH + membership transport for single-run obligations (all transport lemmas
  proved: valueHasETyp, consistentWithRegime, valueConsistentWithRegime,
  runtimeInstantiatesCtx, wfConfig).
- ✓ Clean path (arrow + parrow): fully proved.
- ✓ Parrow ¬qtypCleanUnder per-run obligations: fully proved (except agreeOnClean).

**Remaining concentrated blocker**: Cross-run `agreeOnClean` — 4 sorry sites.
- **High-risk item**: precise characterization of guard-clean entries under poisoned PC;
  `qtypCleanUnder.guard` can make entries clean even when `qt.poison = true` (for non-function
  types with active guard tags), so the naive "no new clean entries" claim is too strong.
  Investigation needed (§4 in app-problem2.md).
- Preservation lemmas (#1-4 in chain) need `typecheckExpr_preserves_wfTagMeaningCtx` /
  `_QTypRespectsTagMeaning` — static fuel induction, independent of cross-run agreement.

### Dependency order (updated 2026-03-05)

```
Step 1 (typecheckExpr_preserves_wfTypeResult) ✓ DONE
Step 2+3 (closure member-matching fix) ✓ DONE
Issue H infrastructure (StepFR_single_run) ✓ DONE
Step 5/6 clean paths ✓ DONE
Step 4 partial (regimeConsistentWithCtx preservation) ✓ DONE

NEXT: Investigate guard-clean entries under poisoned PC  ← CRITICAL PATH
  └─ determines if 4 agreeOnClean sorrys are trivial or need substantial work
  └─ if vacuous: sorrys #5-8 collapse immediately
  └─ if not: need agreeOnClean_poisonedPC_from_precall (High risk)

Step 4 remainder (wfTagMeaningCtx / QTypRespectsTagMeaning preservation)
  └─ independent of Issue H; needs static fuel induction (~500 lines each)
  └─ can proceed in parallel with agreeOnClean investigation

Step 5a (arrow ¬internalPoisonClean): depends on agreeOnClean (shared body, low risk)
Step 5b (arrow ¬qtypCleanUnder agreeOnClean): depends on poisoned-PC investigation
Step 6 (parrow mirror): structurally mirrors arrow paths
```

### Stop / reassess conditions

- ~~If `closure_same_config_tenv_env` turns out to be false~~ — **confirmed false; resolved via
  closure member-matching fix (Issue G).**
- ~~If the `mutual` block for `agreeCapturedEnv_same_toCaptured`~~ — **resolved; mutual recursion
  eliminated by structural induction on evidence tree.**
- ~~If `agreeOnClean_self` turns out to be hard~~ — **moot; using existing
  `agreeOnClean_same_config` instead.**
- If guard-clean entries survive the join under poisoned PC (investigation item 3 in §7
  Step 4) AND neither static analysis nor pre-call agreement transport can handle them —
  consider: (a) strengthening `joinMemEnvsStrong` to drop guards when both sides have
  `poison = true`, or (b) adding a regime-level invariant that guard tags under poisoned PC
  are always `R[k] = false`.
- If preservation lemmas are not provable statically and cannot be derived from
  `StepFR_single_run` (no `terminatesTo` witness for non-executed closures) — consider
  restructuring the refine blocks to only use first-member evidence obtained via the
  mapM wrapper + a direct first-member `terminatesTo` witness.

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
