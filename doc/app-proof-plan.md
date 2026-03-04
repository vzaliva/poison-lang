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

### Checkpoint: 2026-03-04 (2) — Parrow infrastructure + Phase 4 done

Build: **clean** (no errors; sorry-only warnings).

Steps completed since last checkpoint:
- **Phase 4 (Step 1 residual)**: `typecheckApp_wfTypeResult` proved in TypeSafety.lean
  (arrow/parrow mapM + joinTypeResults inline unfolding).
- **Parrow infrastructure (Step 6 partial)**:
  - Created 10 parrow helper lemmas (mirroring FnTClosure versions):
    `applyPFnTClosure_ioFree_extern_fails`,
    `applyPFnTClosure_regular_body_wfTypeResult`,
    `applyPFnTClosure_ok_wfTypeResult` (no sorry),
    `applyPFnTClosure_ok_wfTagMeaningCtx` (sorry),
    `applyPFnTClosure_ok_regimeConsistentWithCtx` (sorry),
    `applyPFnTClosure_ok_QTypRespectsTagMeaning` (sorry),
    `mapM_applyPFnTClosure_forall_wfTypeResult'`,
    `mapM_applyPFnTClosure_forall_wfTagMeaningCtx`,
    `mapM_applyPFnTClosure_forall_regimeConsistentWithCtx`,
    `mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning`
  - Added ~80-line derivation chain before parrow refine block (join transport setup)
  - Filled 4 of 13 parrow refine block sorrys:
    `QTypRespectsTagMeaning` (via `joinTypeResults_QTypRespectsTagMeaning`),
    `wfTagMeaningCtx` (via `join_transport_wfTagMeaningCtx`),
    `wfTypeContext` (via `join_transport_wfTypeContext`),
    `regimeConsistentWithCtx` (via `join_transport_regimeConsistentWithCtx`)
- **Discovered**: `applyFnTClosure_ok_wfTagMeaningCtx` is NOT provable as a purely static lemma
  (mode 3 `ite` creates new tags, so `wfTagMeaningCtx` depends on runtime semantics). All 6
  preservation lemmas (3 FnTClosure + 3 PFnTClosure) are blocked on this.
- **Discovered**: `valueHasETyp_det` (TypeSafety.lean) is likely FALSE (`Value.loc` can type
  as `ETyp.ref ls` for different `ls`). It is unused — not in the stepFR_app chain.

#### New blocker identified: Body StepFR IH evidence

All remaining sorrys in `stepFR_app` (both arrow fallback and parrow body-dependent paths)
require per-run post-body evidence (valueHasETyp, runtimeInstantiatesCtx, consistentWithRegime,
etc.), but `StepFR` IH requires TWO runs evaluating the SAME expression.  Fallback paths handle
cases where the two outer runs may pick different closure alternatives.

Detailed analysis and proposed resolution: **`doc/app-problem2.md`**.

#### In-scope sorrys (stepFR_app dependency chain)

**`FaultRobustnessProofs.lean`** — 10 declarations with sorry, 30 sorry keywords:

| Group | Lemma(s) | Keywords | Risk | Step |
|---|---|---|---|---|
| Preservation (FnT) | `applyFnTClosure_ok_wfTagMeaningCtx` | 1 | Blocked — not purely static | 4 |
| Preservation (FnT) | `applyFnTClosure_ok_regimeConsistentWithCtx` | 1 | Blocked — not purely static | 4 |
| Preservation (FnT) | `applyFnTClosure_ok_QTypRespectsTagMeaning` | 1 | Blocked — not purely static | 4 |
| Preservation (PFnT) | `applyPFnTClosure_ok_wfTagMeaningCtx` | 1 | Blocked — mirrors FnT | 4 |
| Preservation (PFnT) | `applyPFnTClosure_ok_regimeConsistentWithCtx` | 1 | Blocked — mirrors FnT | 4 |
| Preservation (PFnT) | `applyPFnTClosure_ok_QTypRespectsTagMeaning` | 1 | Blocked — mirrors FnT | 4 |
| Arrow ¬intPoisonClean | sorry in `stepFR_app` ¬ `internalPoisonClean` branch | 1 | Medium — needs body IH | 5 |
| Arrow ¬qtypClean | sorrys in `stepFR_app` ¬ `qtypCleanUnder` branch | 9 | Medium — needs body IH | 5 |
| Parrow refine block | sorrys in `stepFR_app` parrow refine | 9 | Medium — needs body IH | 6 |
| Parrow body IH | sorrys at parrow clean/dirty split | 2 | Medium — needs body IH | 6 |

**`TypeSafety.lean`** — 0 sorrys in stepFR_app chain (down from 1).

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

**Step 4: Preservation lemmas** — BLOCKED

Six lemmas with sorry (3 FnTClosure + 3 PFnTClosure):
- `applyFnTClosure_ok_wfTagMeaningCtx`, `applyFnTClosure_ok_regimeConsistentWithCtx`,
  `applyFnTClosure_ok_QTypRespectsTagMeaning`
- `applyPFnTClosure_ok_wfTagMeaningCtx`, `applyPFnTClosure_ok_regimeConsistentWithCtx`,
  `applyPFnTClosure_ok_QTypRespectsTagMeaning` (new — created as mirrors)

**Status**: Discovered these are NOT purely static — `wfTagMeaningCtx` depends on runtime
semantics (mode 3 `ite` creates new tags).  Cannot be proved by typechecker-level fuel
induction alone.  The right approach is to derive them from the StepFR IH (body evaluation
evidence), making them part of the body IH plumbing rather than independent lemmas.

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

### Issue H: Body StepFR IH evidence for fallback paths

See **`doc/app-problem2.md`** for detailed analysis.

**Summary**: StepFR IH requires same expression for both runs.  Fallback paths have different
bodies.  Recommended approach: prove `agreeOnClean_self` (config agrees with itself) and
`StepFR_single_run` (corollary of StepFR via self-agree), then use per-run body IH + join
transport for single-run obligations, and pc-based argument for cross-run `agreeOnClean`.

### Dependency order

```
Step 1 (typecheckExpr_preserves_wfTypeResult) ✓ DONE

Step 2+3 (closure member-matching fix) ✓ DONE

Step 4 (preservation lemmas) — BLOCKED (not purely static; fold into body IH)

Issue H infrastructure (agreeOnClean_self, StepFR_single_run)
  └─ prerequisite for Steps 5, 6

Step 5 (arrow fallback)
  └─ depends on Issue H infrastructure

Step 6 (parrow mirror)
  └─ depends on Step 4 (same as Step 5)
Step 6 (parrow mirror)
  └─ depends on Issue H infrastructure
  └─ structurally mirrors arrow paths
```

### Stop / reassess conditions

- ~~If `closure_same_config_tenv_env` turns out to be false~~ — **confirmed false; resolved via
  closure member-matching fix (Issue G).**
- ~~If the `mutual` block for `agreeCapturedEnv_same_toCaptured`~~ — **resolved; mutual recursion
  eliminated by structural induction on evidence tree.**
- If `agreeOnClean_self` turns out to be hard (e.g., `agreeValueUnder_same` has missing
  preconditions for the reflexive case) — reassess Approach D in `doc/app-problem2.md`.
- If pc-based `agreeOnClean` transport (Approach B) is blocked by `joinTypeResults` semantics —
  consider alternative: prove a direct `agreeOnClean_poisonedPC_transport` from pre-body to
  post-body when pc = true.

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

### Planned (Issue H)
- `agreeOnClean_self` (to be created — config agrees with itself on clean entries)
- `StepFR_single_run` (to be created — single-run corollary of StepFR via self-agree)

### Issue tags
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
- `APP-BODY-IH-BLOCKER` (Issue H — body StepFR IH requires same expression for both runs)
