# `stepFR_app` Handoff Notes

## 1) Scope

This document tracks only what is needed to finish `stepFR_app` in
`LeanProofs/FaultRobustnessProofs.lean`, with focus on:

- blocker analysis
- design decisions already made
- current proof status and next actions

Non-goal: historical timeline of attempts.

## 2) Blocker Analysis

### A. Core structural mismatch

`typecheckApp_arrow_structure_full` produces:

- `results = first :: rest`
- `joinTypeResults ctx first rest = .ok res`

Runtime inversion on executed closure gives an arbitrary selected member `src ∈ results`.
Most existing transport lemmas are head-seed oriented (use `first`), not arbitrary-member oriented.

### B. Why this is tricky (not a naming issue)

`joinTypeResults` fields are not uniformly monotone by membership:

- `joinRegimes` is meet-like (can drop entries)
- `joinMemEnvs` may drop bindings on conflict

So “member facts -> joined facts” cannot be done by simple monotonicity everywhere.

### C. Main risk area

`agreeOnClean` transport is the highest-risk subproblem.
The hard part is proving that clean lookups in joined `res` can be justified from the
head-seed context (`first`) strongly enough for agreement transport.

### D. Secondary blocker

Both arrow/parrow branches still need clean-back propagation:

- from clean-at-joined-result (`hclean_res`)
- to clean-at-`result1` (`hclean1_e1`)

This gate is required before using synchronized shared-member extraction and body IH.

### E. Temporary assumption in use

There is one temporary axiom in `LeanProofs/TypeSafety.lean:52`:

- `memEnv_lookup_etyp_int` (workaround tied to issue `#70`)

Current join-compat lemmas depend on it for `etyp` compatibility.

## 3) Design Decisions (Committed)

1. No semantic/setoid equality framework.
2. No list permutation / reorder infrastructure for `joinTypeResults`.
3. Keep head-based decomposition (`first :: rest`) and bridge to needed facts locally.
4. Use clean-branch closure synchronization first, then transport.
5. Build narrow, purpose-specific join-compat lemmas (not generic reordering theory).
6. Tackle risky `agreeOnClean` path before lower-risk goals.

## 4) Current Status

### A. Implemented and proved helpers

Synchronization and shared-member extraction:

- `stepFR_app_arrow_sync_from_clean` (`LeanProofs/FaultRobustnessProofs.lean:10650`)
- `stepFR_app_parrow_sync_from_clean` (`LeanProofs/FaultRobustnessProofs.lean:10718`)
- `stepFR_app_arrow_extract_shared_member` (`LeanProofs/FaultRobustnessProofs.lean:10789`)
- `stepFR_app_parrow_extract_shared_member` (`LeanProofs/FaultRobustnessProofs.lean:10835`)

Join-compatibility helpers (head vs joined):

- `joinTypeResults_lookup_head_etyp_compat` (`LeanProofs/FaultRobustnessProofs.lean:10025`)
- `joinTypeResults_lookup_head_poison_imp` (`LeanProofs/FaultRobustnessProofs.lean:10489`)
- `joinTypeResults_lookup_head_clean_compat` (`LeanProofs/FaultRobustnessProofs.lean:10616`)
- plus supporting guard/regime helpers around the same region.
- `applyFnTClosure_ok_poison_pred_of_p1_true` (used to force `poison=true`, `pred=noPred` when `p1=true`)
- `applyPFnTClosure_ok_poison_pred_of_p1_true` (same role for pure closure application)
- `joinTypeResults_poison_pred_of_head_true_noPred` (propagates that head fact to joined `res`)

Risk-path transport helper:

- `agreeValueUnder_clean_transport_by_cleanBack`
  (`LeanProofs/FaultRobustnessProofs.lean:9886`)

### B. Arrow branch status (`stepFR_app`)

In `LeanProofs/FaultRobustnessProofs.lean` under `stepFR_app` (`:10887`):

- local risky transport is now isolated in `_hagree_res_from_first_pack` (`:11265`)
- this pack reduces remaining need to:
  - `runtimeInstantiatesCtx (ctxAfter ctxᵢ first)` for both runs
  - `agreeOnClean ... (ctxAfter ctxᵢ first) ...`

The previous dependency on proving a standalone
`Regime.monotoneStep first.regime' res.regime'` at this spot was removed.

`hclean1_e1` in the arrow branch is now proved:

- prove `p1 = false` by contradiction from `hclean_res`
- contradiction route uses the two new helpers above
- conclude `result1.qualType.poison = false` via `hp1`, then `qtypCleanUnder.clean`

Parrow branch now has the same clean-back bridge proved (`hclean1_e1`) using the
new `applyPFnTClosure_ok_poison_pred_of_p1_true` helper plus the same join propagation lemma.

### C. Remaining open subgoals (in `stepFR_app`)

Arrow branch open region is around lines `11075` and `11279+`:

- structured postconditions still `sorry` (typing/wf/instantiation/CWR/value consistency)
- risky `agreeOnClean` pack at `_hagree_res_from_first_pack` is still `sorry`
- body-IH application and final `resultAgreesIfClean` transport still `sorry`

Parrow branch has symmetric open obligations around `11670+` and `11700+`.
Its clean-back bridge (`hclean1_e1`) is no longer `sorry`; remaining work is body-IH + transport.

Current highest-risk unresolved point remains:

- deriving first-context premises needed by `_hagree_res_from_first_pack`
  (`runtimeInstantiatesCtx ... first` for both runs and `agreeOnClean ... first ...`)
- this is where additional infrastructure/assumptions may still be required.

Latest checkpoint:

- `_hagree_res_from_first_pack` itself is set up and usable as an implication.
- blocker is upstream: no direct derivation yet of
  `runtimeInstantiatesCtx (ctxAfter ctxᵢ first) ...` (both runs) and
  `agreeOnClean ... (ctxAfter ctxᵢ first) ...`
  from the currently available branch hypotheses.
- this appears to require non-trivial strategy change or new helper infrastructure,
  so it is paused for decision.

### D. Build status

`make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean` succeeds
with existing `sorry` warnings.

## 5) Recommended Next Steps

1. Prove derivation of first-context pack used by `_hagree_res_from_first_pack` (highest risk):
   - both runtime-instantiation goals at `(ctxAfter ctxᵢ first)`
   - `agreeOnClean` at `(ctxAfter ctxᵢ first)`
2. Use `_sync_extract_of_clean` output to run body IH and produce member-level postconditions.
3. Lift member-level postconditions to joined `res` with existing join-transport lemmas.
4. After risky path is closed, finish remaining structured obligations (wf/typing/CWR/value consistency).

## 6) Practical Check Command

Use this at each checkpoint:

```bash
make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean
```
