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

### E. `VARSREGIME_GAP` (active)

Shared-member final `consistentWithRegime` to joined output `consistentWithRegime` transport.
No longer blocked by mem-env semantics (strong join resolved that).  This is the next
proof-infrastructure target now that the qtype transport pair is closed.

## 3. Current Status and Plan

### What is done

- Phase 0 (invariant initialization): closed with explicit top-level premises.
- `APP-SIGMA-WITNESS-MISMATCH`: resolved via Path D direct member-evidence on `agreeValueUnder`.
- Strong mem-join for app/papp: implemented and spec-aligned.
- Member-to-joined transport for `joinTypeResults`: all three proved
  (`valueHasETyp`, `valueConsistentWithRegime`, `resultAgreesIfClean`).
- Path D constructor refactor: complete, transport cascade repaired, selectors removed from code.

Build status: `lake build` succeeds.  `sorry` count: 28 in `FaultRobustnessProofs.lean`, 49 total
in `LeanProofs/` (use `rg -n -w sorry` to refresh).

### What remains

- `VARSREGIME_GAP`: shared-member final `consistentWithRegime` to joined output
- Remaining app plumbing: fallback `hOutMapChoice` branches, outer join/static obligations
- Parrow mirror
- Propagation of the Path D transport pattern to `stepFR_ite` modes 3/4

### Plan (risk-first)

**Step 1: `VARSREGIME_GAP` (highest remaining risk)**

This is the next proof-infrastructure obligation that could expose a design gap.  Use the
strong mem-join helper layer for memory-side cases and the proved member-to-joined qtype
transport lemmas for value-level obligations.

**Step 2: Remaining app proof plumbing (medium risk)**

Close fallback `hOutMapChoice` branches and outer join/static obligations on top of the
completed Path D transport baseline.  Complete the arrow path end-to-end.

**Step 3: Parrow mirror (low risk, mechanical)**

Mirror the arrow path fixes into the parrow branch.

**Step 4: Propagate to `stepFR_ite` modes 3/4 (validation)**

Reuse the `joinTypeResults_transport_*_from_member` pair and the helper cluster at the ite
join points.  The ite case is a two-branch join (not a fold), so some adaptation is expected.
This serves as independent validation that Path D generalises beyond app.

### Stop / reassess conditions

Stop and discuss if any of the following happens:
- `VARSREGIME_GAP` requires strengthening `StepFR`-level statements or changing the proof
  boundary (instead of using the qtype transport layer as-is).
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
- `joinTypeResults_qualType_arrow_member_from_member`
- `joinTypeResults_qualType_parrow_member_from_member`
- `joinTypeResults_transport_resultAgreesIfClean_from_member`
- `joinPredicates_eq_guardClosure`, `fold_joinPred_guardClosure_init` (in `TypeSafety.lean`)

### Related join points
- `stepFR_ite_mode3`, `stepFR_ite_mode4`

### Active issue tags
- `VARSREGIME_GAP` (active)
- `APP-SIGMA-WITNESS-MISMATCH` (resolved)
- `APP-BODYSTART-VARSREGIME` (legacy; may no longer appear)
