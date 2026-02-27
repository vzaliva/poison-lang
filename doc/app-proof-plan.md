# `stepFR_app` Proof Notes

Notes:
- Avoid relying on line numbers; they drift frequently.  Use lemma names / TODO tags and `rg`.
- Current branch compiles with `sorry` warnings only (`rg -n -w sorry LeanProofs/` to count).
- Design history (approaches tried, detailed root cause analysis, chronological evolution) is in
  `doc/app-proof-history.md`.

## 1. Problem Statement

Complete the remaining obligations in the `app` case of the fault-robustness step theorem
(`stepFR_app`) in `LeanProofs/FaultRobustnessProofs.lean`.

Current focus: I/O-free path, arrow branch first, parrow mirror second.

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

### F. `StepFR_implies_wfTypeResult` instantiation (open risk)

`StepFR_implies_wfTypeResult` derives `wfTypeResult res` from `StepFR ... ctx e res` by
instantiating the universally-quantified runtime configs.  The comment claims "premises are
satisfiable (e.g. empty configs when ctx is wf)" but this is not verified: `runtimeInstantiatesCtx`
likely requires every var in `ctx.varEnv` to be covered by `ρ`, which fails for empty `ρ` when
the body context `ctx''` has captured variables.

`wfTypeResult res` is purely `∀ l, res.memEnv'.contains l → l < res.nextLoc'` — a
location-bookkeeping property with no runtime content.  If the StepFR instantiation approach
fails, the fix is a targeted `typecheckExpr_preserves_wfTypeResult` lemma (induction on the
typechecker) rather than routing through runtime semantics.  `typecheck_nextLoc_mono` already
exists in `TypeSafety.lean` and could serve as a template.

## 3. Current Status and Plan

### Checkpoint: 2026-02-27 — Build clean, 38 sorrys total

Build: **clean** (no errors; sorry-only warnings).

**FaultRobustnessProofs.lean** — 34 actual sorry statements:

| Group | Lemma(s) | Count | Risk |
|---|---|---|---|
| Mutual recursion | `agreeCapturedEnv_same_toCaptured` | 1 | Low — logic sound, need `mutual`/`termination_by` |
| `stepFR_ite` modes | `stepFR_ite_mode3`, `stepFR_ite_mode4` | 2 | Medium — branch case analysis on guard-lookup |
| `stepFR_kwhile` | `stepFR_kwhile` | 1 | Low — deferred; while-loop fixpoint reasoning |
| **wfTypeResult** | `StepFR_implies_wfTypeResult` | 1 | **Medium** — see Issue F above |
| Preservation lemmas | `applyFnTClosure_ok_wfTagMeaningCtx`, `_regimeConsistentWithCtx`, `_QTypRespectsTagMeaning` | 3 | Low — standard preservation |
| Arrow fallback (¬ qtypCleanUnder) | 11 sorrys in `stepFR_app` fallback branch | 11 | Low — poison=true makes most obligations trivial |
| Parrow mirror | 15 sorrys in `stepFR_app` parrow branch | 15 | Low — mechanical mirror of arrow path |

**TypeSafety.lean** — 4 actual sorry statements:

| Lemma | Risk | Notes |
|---|---|---|
| `memEnv_lookup_etyp_int` | Low (deferred) | Placeholder for issue #70; all mem etypes are int |
| `closure_same_config_tenv_env` | Medium | Required by `agreeValueUnder_same`; needs RIC inversion |
| `valueHasETyp_det` | Medium | May be false for loc (multiple refs); check carefully |
| `peClosure_same_config_tenv_env` | Medium | Mirror of `closure_same_config_tenv_env` |

### What was done (recent)

- `stepFR_deref`: **proved** (no sorry).
- `joinTypeResults_QTypRespectsTagMeaning` + `QTypRespectsTagMeaning_joinStep`: **proved** (last session).
- `hTm_ctx''` in `applyFnTClosure_ok_wfTypeResult`: **proved**.
- `agreeValueUnder_same` closure/peClosure branches: closed in FaultRobustnessProofs (now call
  `closure_same_config_tenv_env` / `peClosure_same_config_tenv_env` in TypeSafety).
- `agreeOnClean_same_config`, `agreeCapturedEnv_same`: proved.
- Phase 0 (invariant initialization), Path D / APP-SIGMA-WITNESS-MISMATCH, strong mem-join,
  member-to-joined transport cascade: all proved.

### Plan (risk-first)

**Step 1 (immediate): Verify and close Issue F**

Check whether `StepFR_implies_wfTypeResult` can be proved by empty-config instantiation.
If `runtimeInstantiatesCtx ctx'' μ ρ θ` requires non-trivial varEnv coverage, add a focused
`typecheckExpr_preserves_wfTypeResult` lemma (induction on fuel; template: `typecheck_nextLoc_mono`).
No downstream signature impact.

**Step 2: Preservation lemmas**

Fill the three `applyFnTClosure_ok_*` preservation sorrys.  Independent of the runtime proof.

**Step 3: Arrow fallback branch**

Close the `hOutMapChoice` fallback (`¬ qtypCleanUnder`) branch.  Most obligations are vacuous
because `res.qualType.poison = true` and `pred = noPred` (propagated from `applyFnTClosure`
when `p1 = true`).  The one non-trivial item is `resultAgreesIfClean`: the `.clean` case is
impossible (poison=true) and the `.guard` case needs inspection of `res.qualType.pred`.

**Step 4: Parrow mirror**

Mirror the completed arrow path into the parrow branch.  15 sorrys, mechanical.

**Step 5: Same-config agreement infrastructure (TypeSafety.lean)**

Prove `closure_same_config_tenv_env` and `peClosure_same_config_tenv_env` by inverting
`runtimeInstantiatesCtx` at the closure value.  Once done, `agreeValueUnder_same`'s closure
cases are fully closed without TypeSafety sorry dependence.

**Step 6: Mutual recursion and ite modes**

Resolve `agreeCapturedEnv_same_toCaptured` (mutual / `termination_by`).
Tackle `stepFR_ite_mode3` and `stepFR_ite_mode4` (branch case analysis).

**Step 7: kwhile (deferred)**

`stepFR_kwhile` — while-loop fixpoint proof.  Lower priority; depends on fixpoint reasoning infra.

### Stop / reassess conditions

- If Issue F requires a `typecheckExpr_preserves_wfTypeResult` lemma, assess whether it's
  cleanly provable by induction before committing.
- If `closure_same_config_tenv_env` turns out to be false (e.g. σcap can differ from
  ctx.varEnv.toCaptured for multi-alternative closures), the `agreeValueUnder_same` closure
  proof strategy needs revision.
- If the `mutual` block for `agreeCapturedEnv_same_toCaptured` / `agreeValueUnder_same` requires
  a different recursion structure than expected, stop and discuss before large refactors.

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
  `StepFR_implies_wfTypeResult`, `applyFnTClosure_regular_body_wfTypeResult`
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
