# `stepFR_app` Proof Notes

Notes:
- Avoid relying on line numbers; they drift frequently.  Use lemma names / TODO tags and `rg`.
- Current branch compiles with `sorry` warnings only.
- Design history (approaches tried, detailed root cause analysis, chronological evolution) is in
  `doc/app-proof-history.md`.

## 1. Problem Statement

Complete the remaining obligations in the `app` case of the fault-robustness step theorem
(`stepFR_app`) in `LeanProofs/FaultRobustnessProofs.lean`.

Current focus:
- I/O-free `app` path first
- arrow clean/shared-closure branch first (highest complexity)
- parrow mirror second

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

This is not app-specific: `stepFR_ite` modes 3/4 face the same structural issue and should
reuse the same helper pattern.

### E. Shared-member → joined `consistentWithRegime` (resolved)

Resolved by `joinTypeResults_transport_consistentWithRegime_from_member` and
`joinTypeResults_lookup_member_guardClosure_lookup_compat`.

## 3. Current Status and Plan

### What is done

- Phase 0 (invariant initialization): closed with explicit top-level premises.
- Path D / APP-SIGMA-WITNESS-MISMATCH: resolved via direct member-evidence on `agreeValueUnder`.
- Strong mem-join for app/papp: implemented and spec-aligned.
- Member-to-joined transport for `joinTypeResults`: valueHasETyp, valueConsistentWithRegime,
  resultAgreesIfClean, and consistentWithRegime all proved.
- Path D constructor refactor: complete, transport cascade repaired.
- **Step 2 – wfTypeResult from stepFR (no typecheck lemma):** Properties are threaded through
  stepFR instead of a global typecheck-preserves-wf lemma. `applyFnTClosure_ok_wfTypeResult`
  now takes `tcls`, `tcl`, `hetyp1`, `hresTm1`, `hmem_tcl`, `hargTm`; body `wfTypeResult` comes
  from the stepFR IH (`StepFR_implies_wfTypeResult`). `mapM_applyFnTClosure_forall_wfTypeResult`
  and the stepFR_app call site pass these through; `hargTm` is derived from `hresTm2` and `hqt2`.

Build status: `lake build` succeeds.  `sorry` count: use `rg -n -w sorry` in `LeanProofs/` to refresh.

### What remains

- **One sorry in the wfTypeResult chain:** In `applyFnTClosure_ok_wfTypeResult` (regular branch),
  `hTm_ctx''` (wfTagMeaningCtx for the body context `ctx''`) is sorry. The intended proof is
  the same as `wfTagMeaningCtx_closure_body` (defined later in the file); either move that
  lemma earlier or inline its proof.
- Remaining app plumbing: fallback `hOutMapChoice` branches, outer join/static obligations.
- **agreeValueUnder_same:** Four sorries when `internalPoisonClean qt` (closure/peClosure,
  clean and guard) need agreeCapturedEnv_same plus member evidence.
- Parrow mirror.
- Propagation of the Path D transport pattern to `stepFR_ite` modes 3/4.

### Plan (risk-first)

**Step 1: Shared-member → joined transport (completed)**

`joinTypeResults_transport_consistentWithRegime_from_member` and related helpers close the
shared-member final `consistentWithRegime` → joined output transport in the app arrow path.

**Step 2: Remaining app proof plumbing (medium risk)**

Close fallback `hOutMapChoice` branches and outer join/static obligations on top of the
completed Path D transport baseline.  Complete the arrow path end-to-end.

- **Progress (for handover):**
  - **wfTypeResult from stepFR:** No standalone typecheck-preserves-wf lemma. StepFR premises
    and IH are threaded through `applyFnTClosure_ok_wfTypeResult` /
    `mapM_applyFnTClosure_forall_wfTypeResult`; body `wfTypeResult` is obtained via
    `StepFR_implies_wfTypeResult` from the body StepFR (from IH). One sorry remains:
    `hTm_ctx''` (body context wfTagMeaningCtx; proof = `wfTagMeaningCtx_closure_body` once in scope).
  - **StepFR_single_run** still derives one θ' with full pack when both runs are the same.
  - **agreeOnClean_same_config:** Var case closed. Location case: `qt.etyp = ETyp.int` subcase closed;
    `qt.etyp ≠ ETyp.int` (ref) subcase closed by contradiction via `memEnv_lookup_etyp_int`.
  - **agreeValueUnder_same:** **valueHasETyp_loc_inv** and **valueHasETyp_closure_etyp_arrow** /
    **valueHasETyp_peClosure_etyp_parrow** used; loc cases and `¬internalPoisonClean` closure/peClosure
    branches closed. **Sorry (4):** `internalPoisonClean qt` closure/peClosure (clean and guard)
    need agreeCapturedEnv_same plus MemberVarsRegimeEvidence/MemberCvcrEvidence.
  - **agreeCapturedEnv_same:** hcover y=x and hhenv y=x branches closed (with `List.Nodup` premise
    and **CapturedVarEnv_nodup_head_notin_tail**).

- **Next steps to close Step 2:**
  1. Replace the **hTm_ctx''** sorry: move `wfTagMeaningCtx_closure_body` (and dependencies if needed)
     before `applyFnTClosure_ok_wfTypeResult`, or inline its proof there.
  2. **agreeValueUnder_same:** Close the four closure/peClosure sorries (internalPoisonClean;
     clean and guard), e.g. via agreeCapturedEnv_same with `List.Nodup (tenv.map Prod.fst)` and
     member evidence from `consistentWithRegime` or type checker.
  3. In the ¬ qtypCleanUnder fallback: bodyCtx₀/bodyCtx₁, `runtimeInstantiatesCtx` via
     `runtimeInstantiatesCtx_closure_body_from_henv`, `wfTagMeaningCtx` and `consistentWithRegime`
     for body context, then `hIH_body` + **StepFR_single_run** for θ₀_body/θ₁_body and transport
     for the 10 conjuncts.

**Step 3: Parrow mirror (low risk, mechanical)**

Mirror the arrow path fixes into the parrow branch.

**Step 4: Propagate to `stepFR_ite` modes 3/4 (validation)**

Reuse the `joinTypeResults_transport_*_from_member` pair and the helper cluster at the ite
join points.  The ite case is a two-branch join (not a fold), so some adaptation is expected.
This serves as independent validation that Path D generalises beyond app.

### Stop / reassess conditions

Stop and discuss if any of the following happens:
- Reusing the Path D helper pattern at `stepFR_ite` modes 3/4 requires a materially different
  theorem interface (not just local specialisation).
- Helper generalisation causes churn across many callers before a second reuse site is closed.

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
- **wfTypeResult from stepFR (Step 2):** `applyFnTClosure_ok_wfTypeResult`,
  `mapM_applyFnTClosure_forall_wfTypeResult`, `StepFR_implies_wfTypeResult`,
  `applyFnTClosure_regular_body_wfTypeResult`; `wfTagMeaningCtx_closure_body` (used for body context; one sorry at `hTm_ctx''`)

### Same-config agreement (Step 2 dependencies)
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`, `agreeValueUnder_same`
- `valueHasETyp_loc_inv` (inversion for `valueHasETyp θ (Value.loc a) e`; used to avoid dependent elimination in `agreeValueUnder_same` loc cases)

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
- `joinPredicates_eq_guardClosure`, `fold_joinPred_guardClosure_init` (in `TypeSafety.lean`)

### Related join points
- `stepFR_ite_mode3`, `stepFR_ite_mode4`

### Issue tags
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
