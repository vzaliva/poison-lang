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
typechecker) rather than routing through runtime semantics.

**Verify this before spending time on surrounding plumbing.**

## 3. Current Status and Plan

### What is done

- Phase 0 (invariant initialization): closed with explicit top-level premises.
- Path D / APP-SIGMA-WITNESS-MISMATCH: resolved via direct member-evidence on `agreeValueUnder`.
- Strong mem-join for app/papp: implemented and spec-aligned.
- Member-to-joined transport for `joinTypeResults`: valueHasETyp, valueConsistentWithRegime,
  resultAgreesIfClean, and consistentWithRegime all proved.
- Path D constructor refactor: complete, transport cascade repaired.
- wfTypeResult chain: threaded through `applyFnTClosure_ok_wfTypeResult` /
  `mapM_applyFnTClosure_forall_wfTypeResult` via StepFR IH; `agreeOnClean_same_config` closed;
  `agreeValueUnder_same` closed for num/bool/unit/str/loc and `¬internalPoisonClean` closure
  branches; `agreeCapturedEnv_same` proved (with `List.Nodup` and
  `CapturedVarEnv_nodup_head_notin_tail`).

### What remains (38 sorrys as of last count)

| Group | Lemma(s) | Count | Risk |
|---|---|---|---|
| Mutual recursion | `agreeCapturedEnv_same_toCaptured` | 1 | Low — logic sound, need `mutual`/`termination_by` |
| **wfTypeResult instantiation** | `StepFR_implies_wfTypeResult` | 1 | **Medium — verify satisfiability first** |
| Body context wfTagMeaning | `hTm_ctx''` in `applyFnTClosure_ok_wfTypeResult` | 1 | Low — same proof as `wfTagMeaningCtx_closure_body` |
| Preservation lemmas | `applyFnTClosure_ok_wfTagMeaningCtx`, `_regimeConsistentWithCtx`, `_QTypRespectsTagMeaning` | 3 | Low — standard preservation |
| Join tag-meaning | `joinTypeResults_QTypRespectsTagMeaning` | 1 | Low — structural induction on join |
| Arrow fallback (¬ qtypCleanUnder) | `hOutMapChoice` fallback branch | 10 | Low — poison=true makes most obligations trivial |
| Parrow mirror | All arrow-path properties, parrow branch | 13 | Low — mechanical mirror; infrastructure exists |
| Pure-body transport (parrow) | `resultAgreesIfClean` shared/dirty placeholders | 2 | Low — infrastructure exists, just uninstantiated |
| deref / kwhile | `stepFR_deref`, `stepFR_kwhile` | 2 | Low — deferred scope |
| `agreeValueUnder_same` closures | `internalPoisonClean` closure/peClosure (clean + guard) | 4 | Low — blocked only by `agreeCapturedEnv_same_toCaptured` |

### Plan (risk-first)

**Step 1 (immediate): Verify Issue F**

Check whether `StepFR_implies_wfTypeResult` can be proved by empty-config instantiation.
Concretely: what does `runtimeInstantiatesCtx ctx'' μ ρ θ` require when `ctx''` has a
non-trivial `varEnv`?  If empty configs suffice, fill the sorry.  If not, add a focused
`typecheckExpr_preserves_wfTypeResult` lemma (induction on fuel / typecheckExpr) and replace
the StepFR route; this has no downstream signature impact.

**Step 2: Close same-config agreement**

1. Resolve the `agreeCapturedEnv_same_toCaptured` mutual recursion: either use a `mutual` block
   with `agreeValueUnder_same` or make `agreeValueUnder_same` a recursive function with
   `termination_by Value.size v`.  Once done, the four `agreeValueUnder_same` closure/peClosure
   sorrys close immediately.
2. Move `wfTagMeaningCtx_closure_body` (or its proof) before `applyFnTClosure_ok_wfTypeResult`
   and replace the `hTm_ctx''` sorry.

**Step 3: Arrow fallback branch**

Close the `hOutMapChoice` fallback (`¬ qtypCleanUnder`) branch.  Most obligations are vacuous
because `res.qualType.poison = true` and `pred = noPred` (propagated from `applyFnTClosure`
when `p1 = true`).  The one non-trivial item is `resultAgreesIfClean`: the `.clean` case is
impossible (poison=true) and the `.guard` case needs inspection of `res.qualType.pred`.

**Step 4: Preservation lemmas and join tag-meaning**

Fill the three `applyFnTClosure_ok_*` preservation sorrys and
`joinTypeResults_QTypRespectsTagMeaning` (structural induction on the join fold).  These are
independent of the runtime proof and can be done in any order.

**Step 5: Parrow mirror**

Mirror the completed arrow path into the parrow branch.  13 sorrys, mechanical.
The pure-body shared/dirty transport placeholders (2 sorrys) belong here.

### Stop / reassess conditions

- If Issue F turns out to require a `typecheckExpr_preserves_wfTypeResult` lemma, assess whether
  it's cleanly provable by induction on the typechecker before committing.
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
- `wfTagMeaningCtx_closure_body` (body context wfTagMeaning; one sorry at `hTm_ctx''`)

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
- `joinTypeResults_QTypRespectsTagMeaning`
- `joinPredicates_eq_guardClosure`, `fold_joinPred_guardClosure_init` (in `TypeSafety.lean`)

### Issue tags
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
