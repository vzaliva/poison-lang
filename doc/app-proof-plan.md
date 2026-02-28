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

### G. `closure_same_config_tenv_env` / `peClosure_same_config_tenv_env` (open)

These TypeSafety.lean lemmas are needed by `agreeValueUnder_same` (closure branches), which is
needed for `agreeOnClean_same_config` → `stepFR_app`.  They assert that when a closure value
is typed at an arrow/parrow type and the realization map instantiates the context, the closure's
captured env is `ctx.varEnv.toCaptured` and its runtime env is `ρ`.

The proof requires inverting `runtimeInstantiatesCtx` and `valueHasETyp` at the closure.
Care needed: if a closure can be typed at multiple arrow types (different `tcls` members),
we need to ensure the specific member `FnTClosure.regular x body σcap ∈ tcls` pins `σcap`
to `ctx.varEnv.toCaptured`.

## 3. Current Status and Plan

### Checkpoint: 2026-02-27b — Step 1 complete, build clean, 33 in-scope sorrys

Build: **clean** (no errors; sorry-only warnings).

Step 1 completed:
- `typecheckExpr_preserves_wfTypeResult` proved in TypeSafety.lean (fuel induction, ~800 lines).
- `StepFR_implies_wfTypeResult` deleted from FaultRobustnessProofs.lean.
- `applyFnTClosure_regular_body_wfTypeResult` rewritten to call
  `typecheckExpr_preserves_wfTypeResult` directly (no longer needs StepFR IH).
- `applyFnTClosure_ok_wfTypeResult` and `mapM_applyFnTClosure_forall_wfTypeResult` simplified:
  dropped `predSat`, `tm`, `fuel_app`, `h_fuel`, `IH`, `hpred`, `hTm1`, `tcls`, `hetyp1`,
  `hresTm1`, `hmem_tcl`/`hargTm` parameters (no longer needed for purely static wfTypeResult).
- One planned sorry remains in `typecheckApp_wfTypeResult` (arrow/parrow mapM + joinTypeResults
  inline unfolding — mechanical but tedious).

#### In-scope sorrys (stepFR_app dependency chain)

**`FaultRobustnessProofs.lean`** — 30 sorrys:

| Group | Lemma(s) | Count | Risk | Step |
|---|---|---|---|---|
| Mutual recursion | `agreeCapturedEnv_same_toCaptured` | 1 | Low — logic sound, need `mutual`/`termination_by` | 3 |
| Preservation | `applyFnTClosure_ok_wfTagMeaningCtx` | 1 | Low — standard preservation | 4 |
| Preservation | `applyFnTClosure_ok_regimeConsistentWithCtx` | 1 | Low — standard preservation | 4 |
| Preservation | `applyFnTClosure_ok_QTypRespectsTagMeaning` | 1 | Low — standard preservation | 4 |
| Arrow fallback | 11 sorrys in `stepFR_app` `¬ qtypCleanUnder` branch | 11 | Low — `poison=true`, `pred=noPred` | 5 |
| Parrow branch | 15 sorrys in `stepFR_app` parrow path | 15 | Low — mechanical mirror of arrow | 6 |

**`TypeSafety.lean`** — 3 sorrys:

| Lemma | Risk | Step |
|---|---|---|
| `closure_same_config_tenv_env` | Medium — see Issue G | 2 |
| `peClosure_same_config_tenv_env` | Medium — mirror of above | 2 |
| `typecheckApp_wfTypeResult` | Low — mechanical mapM/joinTypeResults unfolding | 1 (residual) |

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
- `agreeValueUnder_same` closure/peClosure branches: closed in FaultRobustnessProofs (now call
  `closure_same_config_tenv_env` / `peClosure_same_config_tenv_env` from TypeSafety).
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`: proved.
- Phase 0 (invariant initialization), Path D / APP-SIGMA-WITNESS-MISMATCH, strong mem-join,
  member-to-joined transport cascade: all proved.
- **Step 1 (Issue F)**: `typecheckExpr_preserves_wfTypeResult` proved (TypeSafety.lean);
  `StepFR_implies_wfTypeResult` deleted; `applyFnTClosure_regular_body_wfTypeResult` rewritten;
  `applyFnTClosure_ok_wfTypeResult` / `mapM_applyFnTClosure_forall_wfTypeResult` signatures
  simplified (dropped StepFR/PredSat/TagMeaning parameters).

### Plan (risk-first)

**Step 1: Prove `typecheckExpr_preserves_wfTypeResult` — Issue F** ✓ DONE

Proved `typecheckExpr_preserves_wfTypeResult` in TypeSafety.lean (~800 lines, fuel induction).
All sub-tasks completed:
1. ✓ `applyFnTClosure_regular_body_wfTypeResult` rewritten to use the new lemma directly.
2. ✓ `StepFR_implies_wfTypeResult` deleted.
3. ✓ Signatures of `applyFnTClosure_ok_wfTypeResult` / `mapM_applyFnTClosure_forall_wfTypeResult`
   simplified (dropped StepFR IH, PredSat, TagMeaning parameters).
One planned sorry remains: `typecheckApp_wfTypeResult` (arrow/parrow mapM + joinTypeResults
inline unfolding — the same pattern as `typecheckExpr` app case but fully inlined).

**Step 2: Close same-config agreement — Issue G**

Prove `closure_same_config_tenv_env` and `peClosure_same_config_tenv_env` in TypeSafety.lean
by inverting `runtimeInstantiatesCtx` and `valueHasETyp` at the closure value.  Once done, the
`agreeValueUnder_same` closure cases have no sorry dependence beyond the `memEnv_lookup_etyp_int`
axiom (which is intentionally out of scope).

**Step 3: Resolve mutual recursion — `agreeCapturedEnv_same_toCaptured`**

Either introduce a `mutual` block with `agreeValueUnder_same`, or give `agreeValueUnder_same` a
`termination_by Value.size v` measure.  Once done, the `agreeCapturedEnv_same_toCaptured` sorry
is replaced with a proper structural induction.

**Step 4: Preservation lemmas**

Fill `applyFnTClosure_ok_wfTagMeaningCtx`, `applyFnTClosure_ok_regimeConsistentWithCtx`,
`applyFnTClosure_ok_QTypRespectsTagMeaning`.  These are standard preservation properties
(context well-formedness invariants survive function body typechecking) and are independent of
the runtime proof.  Each follows the same pattern: case-split on `FnTClosure` constructor
(regular vs fallback), unfold `applyFnTClosure`, and use typechecker-level preservation
or the corresponding `mapM_applyFnTClosure_forall_*` sibling lemma patterns.

**Step 5: Arrow fallback branch (¬ qtypCleanUnder)**

Close the `hOutMapChoice` fallback branch in `stepFR_app` (11 sorrys).  Key facts available:
- `res.qualType.poison = true` and `res.qualType.pred = noPred` (from
  `joinTypeResults_poison_pred_of_head_true_noPred`)
- `p1 = true` (from `hpoison1_true`)

Obligations and approach:
- `valueHasETyp θ₀ o₀ res.qualType.etyp` / `θ₁ o₁`: use body StepFR IH for one run
  (single-run variant), then `joinTypeResults_transport_valueHasETyp_from_member`.
- `runtimeInstantiatesCtx (ctxAfter ctxᵢ res)`: use
  `joinTypeResults_transport_runtimeInstantiatesCtx_from_member` (or prove it; transport
  `runtimeInstantiatesCtx` from the shared member to the joined context).
- `consistentWithRegime`: use
  `joinTypeResults_transport_consistentWithRegime_from_member`.
- `agreeOnClean`: use `join_transport_agreeOnClean_from_member`.
- `valueConsistentWithRegime`: `poison = true` makes this trivial (poisoned values are
  vacuously consistent).
- `resultAgreesIfClean`: `poison = true ∧ pred = noPred` → `.clean` case is impossible
  (by `qtypCleanUnder` definition); `.guard` case is impossible (`pred = noPred` has no
  `guardClosure` tag).

**Step 6: Parrow mirror**

Mirror the completed arrow path into the parrow branch (15 sorrys).  The parrow branch has
the same structure as the arrow clean path but with `PExpr`/`PFnTClosure`/`parrow` types.
The obligations are identical in structure:
- `QTypRespectsTagMeaning`: use `joinTypeResults_QTypRespectsTagMeaning`.
- `valueHasETyp`: body IH + `joinTypeResults_transport_valueHasETyp_from_member`.
- `wfTagMeaningCtx`, `wfTypeContext`: join transport lemmas (same as arrow path).
- `runtimeInstantiatesCtx`, `consistentWithRegime`, `agreeOnClean`: member-to-joined transport.
- `valueConsistentWithRegime`, `resultAgreesIfClean`: member-to-joined transport.
- Parrow-specific: two remaining sorrys at end are the `hclean1_e1` clean/dirty split
  (same structure as arrow but with `PFnTClosure`).

### Dependency order

```
Step 1 (typecheckExpr_preserves_wfTypeResult)
  └─ no dependencies on other steps; enables Steps 5, 6

Step 2 (closure_same_config_tenv_env)
  └─ no dependencies; enables Step 3

Step 3 (agreeCapturedEnv_same_toCaptured)
  └─ depends on Step 2

Step 4 (preservation lemmas)
  └─ independent; parallel with Steps 1-3

Step 5 (arrow fallback)
  └─ depends on Step 1 (for join_transport_wfTypeContext)
  └─ depends on Step 4 (for wfTagMeaningCtx, regimeConsistentWithCtx transport)

Step 6 (parrow mirror)
  └─ depends on Steps 1, 4 (same as Step 5)
  └─ structurally mirrors arrow clean path + Step 5
```

### Stop / reassess conditions

- If `typecheckExpr_preserves_wfTypeResult` induction turns out to require many case-specific
  sub-lemmas about `joinMemEnvs`, `joinMemEnvsStrong`, `updateMemEnv`, `updateLocsetWeak` etc.,
  stop and assess whether these sub-lemmas should be proved first as standalone helpers.
- If `closure_same_config_tenv_env` turns out to be false (e.g. σcap can differ from
  `ctx.varEnv.toCaptured` for multi-alternative closures at different capture points), the
  `agreeValueUnder_same` closure proof strategy needs revision — stop and discuss.
- If the `mutual` block for `agreeCapturedEnv_same_toCaptured` / `agreeValueUnder_same`
  requires a different recursion structure, stop and discuss before large refactors.

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
- `typecheckExpr_preserves_wfTypeResult` (new — Step 1)
- `wfTagMeaningCtx_closure_body` (body context wfTagMeaning)

### Same-config agreement
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`, `agreeCapturedEnv_same_toCaptured`,
  `agreeValueUnder_same`
- `valueHasETyp_loc_inv` (avoids dependent elimination in `agreeValueUnder_same` loc cases)
- `valueHasETyp_closure_etyp_arrow`, `valueHasETyp_peClosure_etyp_parrow`

### Member-evidence transport
- `memberVarsRegimeEvidence_monotone`, `memberVarsRegimeEvidence_transport_μ`
- `memberCvcrEvidence_monotone`, `memberCvcrEvidence_transport_μ`
- `memberVarsRegimeEvidence_transport_lookup_back`, `memberCvcrEvidence_transport_lookup_back`

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
- `joinPredicates_eq_guardClosure`, `fold_joinPred_guardClosure_init` (in `TypeSafety.lean`)

### Issue tags
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
