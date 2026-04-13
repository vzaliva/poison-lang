# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Final review gate before closing Step 4: confirm that the remaining 6 axioms
are the current semantic extern contract floor.

Required next action:

1. review each remaining axiom against the criteria in §2
2. confirm that each survivor is irreducibly semantic
3. call Step 4 complete and treat the branch as having reached its extern
   contract floor

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** add any new `axiom`

**Branch status (2026-04-13, branch `new-iofree`)**

- `lake build` succeeds with **0 sorry, 0 warnings**
- all `LeanProofs/` files compile cleanly
- axiom count: **10 → 6** (3 deleted, 1 proved structurally, 1 bundled axiom
  replaced by a focused semantic contract)

## 1. Extern contract floor

The remaining 6 axioms in `LeanProofs/StepFR.lean` represent the current
semantic extern contract floor. Raw extern syntax (`externVal`, `externFn`,
`externPfn`) is operationally unreachable — all fail at runtime. The remaining
proof surface is entirely about the **typing summary layer**:

1. `typecheckExternVal`
2. `applyFnTClosure` on `FnTClosure.extern`
3. `applyPFnTClosure` on `PFnTClosure.extern`

No eval-side extern contract is needed. The open obligations are about typing
artifacts, not executable extern behavior.

## 2. Per-axiom review

### 2.1 `applyFnTClosure_extern_ok_memEnv_QTypRespectsTagMeaning`

**Role:** Every memory cell written by a successful impure extern application
respects `TagMeaning`. Feeds the proved structural theorem
`applyFnTClosure_extern_ok_wfTagMeaningCtx`.

**Why semantic:** The structural shell (context shape, `wfTagMeaningCtx`
preservation) is proved. What remains opaque is the semantic meaning of
predicates embedded in the extern effect summary.

**Verdict:** Likely permanent semantic contract. No further split needed.

### 2.2 `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`

**Role:** The result `QTyp` of an impure extern application respects
`TagMeaning`.

**Why semantic:** The typechecker allocates/resolves tags and packages the
summary but does not justify that the extern summary is semantically faithful.
Even in the simple-return case, the correctness of the resolved predicate is
an assumption about the extern summary.

**Verdict:** Likely permanent semantic contract.

### 2.3 `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`

**Role:** Pure-closure analogue of the previous axiom.

**Why semantic:** Same reasoning — the absence of the effect loop simplifies
structure but not the core semantic opacity.

**Verdict:** Likely permanent semantic contract.

### 2.4 `applyFnTClosure_extern_ok_lookup_origin`

**Role:** Trusted output cells produced by an impure extern application come
from trusted input cells (provenance contract).

**Why semantic:** The effect loop can overwrite referenced locations with
arbitrary summary-provided poison/predicate pairs. Nothing in the typing code
alone guarantees that clean or active-guarded non-function outputs originate
from pre-existing trusted cells.

**Verdict:** Likely permanent semantic contract.

### 2.5 `applyFnTClosure_extern_ok_fresh_loc_not_clean`

**Role:** Fresh memory entries created by impure externs may not be trusted
when the application provenance is tainted.

**Why semantic:** The effect loop does not propagate `p` or `p1` into stored
memory cells (it uses `ctx.pc`), so the conclusion does not follow from the
typechecker equations alone.

**Verdict:** Likely permanent semantic contract.

### 2.6 `typecheckExternVal_QTypRespectsTagMeaning_axiom`

**Role:** The produced result `QTyp` of `externVal` typing respects
`TagMeaning`.

**Why semantic:** The structural parts are already separated
(`typecheckExternVal_preserves_wfTagMeaningCtx` is proved). The remaining
unproved content is semantic interpretation of the resolved extern predicate.

**Verdict:** Likely permanent semantic contract.

### 2.7 Summary

| Axiom | Category |
|------|----------|
| `applyFnTClosure_extern_ok_memEnv_QTypRespectsTagMeaning` | effect-write semantic |
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | result semantic |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | result semantic (pure) |
| `applyFnTClosure_extern_ok_lookup_origin` | provenance |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | trust discipline |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | value semantic |

All 6 are semantic rather than structural. No further reduction route is
currently evident without either weakening the extern model or merely moving
the same semantic assumptions to a different interface.

## 3. Plan

**Current plan status:** structural reduction work is complete (Steps 1–4d).
The branch sits at 6 remaining semantic axioms. The only open item is the
final explicit review gate (Step 4e).

### Step 4e. Accept the 6-axiom contract floor

**Status:** current

Targets:

1. confirm each surviving axiom is irreducibly semantic (§2 above)
2. document the branch's stopping point
3. call Step 4 complete

Done means:

- the document records an explicit keep judgment for each of the 6 axioms
- the branch has a documented reason for stopping at 6
- no additional proof-engineering task remains for the current extern model

## 4. History

This section records completed work and design decisions for reference.

### 4.1 Steps completed

- **Step 1 (ref-location induction):** closed all cases of the new
  ref-location induction in `TypeSafety.lean`.
- **Step 2a (TypeSafety internal):** finished `TypeSafety.lean` internally
  with the strengthened `wfTypeContext`.
- **Step 2b (downstream propagation):** propagated the strengthened
  `wfTypeContext` through all `StepFR*` files. `lake build` clean.
- **Step 3 (axiom triage):** classified all 10 axioms into likely permanent,
  provable now, and provable after statement adjustment.
- **Step 4a (TagBoundedCtx pivot):** introduced `TagBoundedCtx` as a bundled
  input/output invariant on `StepFR` to make tag-boundedness facts available
  for guard-tag-absence replacement.
- **Step 4b (guard-tag-absence elimination):** deleted 3 axioms
  (`applyFnTClosure_extern_ok_guardClosure_tag_absent`,
  `applyPFnTClosure_extern_ok_guardClosure_tag_absent`,
  `typecheckExternVal_guardClosure_pred_implies_tag_absent`); callers switched
  to proved `_of_tagEnvBounded` variants.
- **Step 4c (wfTagMeaningCtx split):** replaced the bundled axiom
  `applyFnTClosure_extern_ok_wfTagMeaningCtx` with a focused per-entry
  semantic contract plus a proved structural preservation lemma.
- **Step 4d (typecheckExternVal lookup-origin):** replaced the axiom with a
  proved structural lemma under `wfTypeContext ctx` precondition.

### 4.2 Key design decisions

- Rejected local-only repair via stronger `contains` plumbing (doesn't solve
  typing-only locations from extern summaries).
- Rejected `wfTypeContext`-first implementation order (turned 6 holes into
  27). Lesson: prove the supporting induction first, then change the public
  meaning.
- Approved the `TagBoundedCtx` pivot when the guard-tag-absence replacement
  exposed a genuine missing input in the `StepFR` chain.
- Approved adding `TagBoundedCtx ctx` to the top-level FR specs
  (`TypeSystemEnforcesFaultRobustness_spec`, `_spec_ioFree`) since the initial
  context trivially satisfies it.

### 4.3 Reference points

Current-branch helpers:

- `LeanProofs/RegimeConsistency.lean`:
  `EnvRespectsTagMeaning_updateMemEnv`,
  `EnvRespectsTagMeaning_list_fold_updateMemEnv`,
  `QTypRespectsTagMeaning_fn_extern`,
  `QTypRespectsTagMeaning_pfn_extern`
- `LeanProofs/TypeSafety.lean`:
  `typecheckExpr_preserves_TagBoundedCtx`,
  `typecheckExpr_TagBoundedCtx_varEnv_update`,
  `matchGuard_tag_bounded`,
  `tagEnvBounded_insert_of_lt`
