# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Contract A unification is complete.
The immediate goal is **Plan step 1**: state and validate the exact local
structural lemma that should replace the poison-side `.1` use of
`applyFnTClosure_extern_ok_lookup_origin` in the app case of
`typecheckExpr_lookup_origin_of_pc_true_split`.
This is a naming-sensitive step: at that call site, the axiom parameter
named `result2` is instantiated by the app case's local `result1`
(function-side result), while the app case's local `result2` is the
argument-side result.

Current status:

1. Contract A is represented by a single unified axiom:
   `externTagMappingRespectsTagMeaning`.
2. Contract B is represented by a single provenance axiom:
   `applyFnTClosure_extern_ok_lookup_origin`.
3. The next executable subgoal is to pin down the smallest proved lemma that
   gets from `srcRes.memEnv'` back to the pre-extern memory used by
   `hbackToCtx_poison`.

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** increase net `axiom` count (new axioms must replace old ones)
- do **not** add a duplicate `ofCaptured` lookup bridge lemma; use
  `list_lookup_of_ofCaptured_lookup`
- prefer helper lemmas over strengthening public corollary interfaces unless
  the existing call-site hypotheses prove insufficient

**Branch status (2026-04-13, branch `new-iofree`)**

- last reported `lake build` succeeds with **0 sorry, 0 warnings**
- last reported `make test` passes after the `applyExternEffect` refactor
- axiom count: **2 declarations**
- The remaining axioms are
  `externTagMappingRespectsTagMeaning` (unified Contract A) and
  `applyFnTClosure_extern_ok_lookup_origin` (Contract B)

## 1. Overview: two high-level contracts

The current contract floor consists of two semantic contracts about extern
typechecking behavior:

**Contract A — Tag Meaning Soundness.** Every `QTyp` produced or stored by
an extern type operation has its guard descriptors properly registered in the
`TagMeaning`.  Covers three independent entry points: impure function
application, pure function application, and extern value declaration.

**Contract B — Trust Provenance (impure only).** Impure extern function
applications do not manufacture trust: clean or guard-protected cells in the
output memory trace back to corresponding cells in the pre-call context.

Pure externs require **no** provenance axioms because
`applyPFnTClosure_extern_memEnv_eq` (TypeSafety.lean:4152) proves
structurally that pure externs do not modify memory.

### Why externs need axioms at all

Raw extern syntax (`externVal`, `externFn`, `externPfn`) is operationally
unreachable — all fail at runtime. The remaining proof surface is entirely
about the **typing summary layer**: when the typechecker resolves symbolic
predicates to concrete guard predicates via `collectAndAllocExternTags` →
`resolveSyntaxPred`, the resulting `QTyp` values must be semantically
coherent with the `TagMeaning` framework and must not introduce untracked
trust.  These facts cannot be derived structurally because:

1. The resolved predicates carry freshly allocated tags that are not yet in
   any pre-existing `TagMeaning`.
2. The effect loop for impure externs can overwrite existing memory cells
   with new predicates, and tracing trust through the overwrite requires
   reasoning about the content of the extern summary, not just its shape.

## 2. Remaining axiom review

### 2.1 `externTagMappingRespectsTagMeaning`

**StepFR.lean:6197.  Contract A.**

**Role:** This is the single semantic boundary for tag-meaning soundness.
It states that the fresh tag mapping produced by
`collectAndAllocExternTags` is compatible with `tm`.

**Why it remains semantic:** `tm` is universally quantified, while
`wfTagMeaningCtx` only constrains already-existing descriptors in the typing
context.  Fresh tags allocated during extern resolution are not forced by any
structural property of the input context, so some assumption connecting the
allocated mapping to `tm` still appears necessary.

**Status:** Current Contract A floor.  No further narrowing is planned unless a
stronger derivation principle for fresh tags is discovered.

### 2.2 `applyFnTClosure_extern_ok_lookup_origin`

**StepFR.lean:6873.  Contract B.**

**Role:** Provenance for trusted outputs of impure extern application.
It says that trusted output cells come from correspondingly trusted input
cells in the pre-call context.

Two pieces remain bundled:

1. **Poison provenance:** if an output cell has `poison = false`, it came from
   a clean input cell in `ctx.memEnv`.
2. **Guard provenance:** if an output cell is trusted via an active guard tag,
   that tag and its trust also came from the input context/regime.

**Current assessment:** the poison conjunct is already proved at the
whole-expression level by
`typecheckExpr_lookup_origin_of_pc_true_split` /
`typecheckExpr_clean_lookup_origin_of_pc_true`.  The remaining work is to
make the impure `FnTClosure.extern` app subcase discharge that poison claim
structurally instead of by axiom.  The guard conjunct still looks semantic,
because impure extern effects can overwrite cells with freshly resolved
guards while preserving the regime.  That said, the guard half may well be
amenable to the same style of local structural treatment; it is simply out
of scope for this step.

**Status:** This is the only realistic remaining axiom-reduction target.

## 3. Current reduction question

The open reduction question is now **local**, not global: can the impure
extern application case prove the poison provenance half structurally, so
the strong-induction theorem no longer needs `.1` of
`applyFnTClosure_extern_ok_lookup_origin`?  The global clean-origin theorem
already shows the desired statement is true for `typecheckExpr` as a whole.

## 4. Consolidated contract floor

### Current state (2 declarations, 2 semantic obligations)

| # | Axiom | Contract | Category |
|---|-------|----------|----------|
| A1 | `externTagMappingRespectsTagMeaning` | A | unified tag-mapping semantic core |
| B1 | `applyFnTClosure_extern_ok_lookup_origin` | B | provenance |

### Plain-English contract summary

An **extern type specification** is a trusted declaration about external
code that the type system cannot verify.  The FR proof accepts it under
two contracts:

**A. Tag Meaning Soundness** — When the typechecker resolves an extern's
symbolic predicates into concrete guard predicates (allocating fresh tags
and building guard closures), every guard descriptor in the resulting
qualified types is properly registered in the tag meaning.  This ensures
that extern-produced guards integrate correctly with the regime-consistency
framework that drives the fault-robustness proof.

**B. Trust Provenance** — When an impure extern function application
modifies the memory type environment (via its declared effect list), it
does not manufacture trust.  Every cell in the output memory that the FR
proof considers "clean" (either by having `poison = false` or by being
guarded by an active regime tag) can be traced to a correspondingly clean
cell in the typing context that existed *before* the function was applied.

## 5. Next goal: extract the poison subproof of Contract B

**Status:** proposed

**Target:** reduce `applyFnTClosure_extern_ok_lookup_origin` by proving its
poison provenance conjunct structurally, leaving only the guard provenance
conjunct axiomatic.

#### Impact assessment

- **Soundness:** No change — proof refactoring only.
- **Precision:** No change — typechecker behaviour unchanged.
- **Language scope:** No change.
- **Operational semantics:** No change.
- **FR property:** Statement unchanged if the factoring succeeds; the aim is
  to shrink the remaining semantic surface, not weaken the theorem.

#### Problem

`applyFnTClosure_extern_ok_lookup_origin` currently bundles two claims:

1. clean output cells came from clean input cells
2. guard-trusted output cells came from guard-trusted input cells

The second claim still appears genuinely semantic.  The first is no longer
an open semantic question: it is already proved at the whole-expression
level, but the current proof still invokes the axiom in the impure extern
app case.  The task is to replace that one local use with a structural
lemma and then shrink the axiom.

#### Analysis

The structural opening is:

1. `typecheckExpr_lookup_origin_of_pc_true_split` already proves the desired
   poison/guard provenance split for the entire typechecker, and
   `typecheckExpr_clean_lookup_origin_of_pc_true` is its clean corollary.
2. In that strong-induction proof's app case, regular closures already use
   IH plus `hbackToCtx_poison`, and pure extern closures already use
   `applyPFnTClosure_extern_memEnv_eq` plus the same back-to-context bridge.
   The impure `FnTClosure.extern` branch is the only non-structural case.
3. The axiom has only two live uses in this proof: `.1` for poison
   provenance and `.2` for guard provenance.
4. The effect loop already has the right structural template:
   `applyExternEffect_preserves_allCellsRespect` and
   `forIn_effects_loop_preserves_allCellsRespect`.
5. Each `applyExternEffect` write stores
   `poison = joinPoison ctx.pc effectQt.poison`.  Under `ctx.pc = true`,
   every effect-written cell is therefore poisoned.
6. `list_fold_updateMemEnv_lookup_eq_of_not_mem` is the key mechanical tool:
   if a location is not written by the fold, its lookup is unchanged.  So a
   clean cell in the final `r.memEnv'` cannot have been written by the
   effect loop.
7. No extra bridge through `returnSpecToQTyp` or
   `normalizeAppResultByProvenance` is needed for memory provenance: in all
   impure extern return branches, the final `memEnv'` is exactly the loop
   result.

So the remaining proof obligation is not a new global
`result2.memEnv' -> ctx.memEnv` theorem.  It is a focused local lemma for
the impure extern arm:

- clean in `r.memEnv'`
- implies clean in `result2.memEnv'`
- then existing `hbackToCtx_poison` finishes the trip back to `ctx.memEnv`

At the concrete call site in `typecheckExpr_lookup_origin_of_pc_true_split`,
this `result2` is the app case's local `result1`, because the axiom is being
instantiated at the function-side `applyFnTClosure` call.

#### Proposed approach

Keep the goal narrow: do **not** try to remove Contract B entirely.
First attempt to prove only the poison conjunct structurally.  If successful,
replace `applyFnTClosure_extern_ok_lookup_origin` with:

- a proved structural poison-provenance lemma
- a smaller axiom covering only guard provenance

Model the new proof on the existing effect-loop invariant pair, but swap the
per-cell "respects `tm`" invariant for a clean-lookup invariant:

- if the post-state lookup at `l` is `some qt` with `qt.poison = false`,
  then the pre-state lookup at `l` is also `some qt_in` with
  `qt_in.poison = false`

This is the same mechanical backbone as the `allCellsRespect` lemmas, but
not the same quantifier shape: the new invariant is intentionally
**pointwise in the caller's chosen `l`**, not a simultaneous statement
about all clean cells at once.

If the focused extern lemma fails, stop and record the exact obstruction
rather than widening the interface or re-proving the whole theorem stack.

#### Plan

1. **Highest-risk first:** state the focused structural replacement for the
   current `.1` call in the app case.  The target statement should match the
   call site directly:
   from `applyFnTClosure (FnTClosure.extern ...) = .ok srcRes`,
   `ctx.pc = true`, `srcRes.memEnv'.lookup l = some qt_src`, and
   `qt_src.poison = false`, derive
   `∃ qt_mid, result2.memEnv'.lookup l = some qt_mid ∧ qt_mid.poison = false`.
   Validate that this is sufficient before broader refactoring.  At the
   app-case call site, remember that this `result2` unifies with the local
   function-side `result1`.
2. Prove the supporting effect-loop helpers
   `applyExternEffect_preserves_clean_lookup` and
   `forIn_effects_loop_preserves_clean_lookup`, cloning the proof shape of
   `applyExternEffect_preserves_allCellsRespect` /
   `forIn_effects_loop_preserves_allCellsRespect` and using
   `list_fold_updateMemEnv_lookup_eq_of_not_mem` as the fold step.  These
   should be framed pointwise in `l`, not as a universal all-cells theorem.
3. Replace the `.1` use of `applyFnTClosure_extern_ok_lookup_origin` in
   `typecheckExpr_lookup_origin_of_pc_true_split` with the new structural
   extern lemma, then finish via the existing `hbackToCtx_poison` bridge.
4. Once the split theorem compiles without the poison half of the axiom,
   shrink `applyFnTClosure_extern_ok_lookup_origin` to a guard-only
   contract, update call sites, and verify `lake build` clean.

#### Risks

- The highest-risk step is pinning down the exact local statement for the
  impure extern helper and decomposing the `applyFnTClosure` effect loop
  without over-strengthening the interface.
- The guard conjunct may still be entangled with the poison conjunct at some
  call sites, requiring small local proof rewrites even if the factorization
  is conceptually clean.

## 6. History

This section records completed work and design decisions for reference.

### 6.1 Steps completed

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
- **Step 4e (contract floor review):** audited all 6 declared axioms,
  identified 1 dead axiom and 1 merge opportunity, organized survivors into
  2-contract framework.
- **Step 4f.1 (dead axiom removal):** deleted unused
  `applyFnTClosure_extern_ok_fresh_loc_not_clean`. Axiom count: 10 → 5.
- **Step 4f.2 (merge):** merged
  `applyFnTClosure_extern_ok_memEnv_QTypRespectsTagMeaning` and
  `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` into
  `applyFnTClosure_extern_ok_outputRespectsTagMeaning` (conjunction).
  Declaration count: 5 → 4.
- **Step 5a (unified axiom validation):** validated Option B on existing
  code.  Added `externTagMappingRespectsTagMeaning`, proved
  `resolveSyntaxPred_respectsTagMeaning`, and derived the `typecheckExternVal`
  and pure-extern-simple corollaries.
- **Step 5b (typechecker refactor):** extracted `applyExternEffect` from the
  impure extern effect loop and repaired the affected `TypeSafety.lean`
  proofs without changing axiom count.  The key repair pattern was to
  decompose the extra bind/match layer introduced by `do`-notation in the
  `for` loop before analyzing the helper's internal match chain.
- **Step 5c (partial):** deleted
  `typecheckExternVal_QTypRespectsTagMeaning_axiom` and switched its caller to
  `typecheckExternVal_QTypRespectsTagMeaning_corollary`.
- **Step 5c (partial, continued):** added the extern captured-env transfer
  helpers for nested pure returns, replaced
  `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` with a proved
  corollary, and updated the pure-extern call sites.  The only remaining
  Contract A axiom is the impure extern output contract
  `applyFnTClosure_extern_ok_outputRespectsTagMeaning`.
- **Step 5c (completed):** added the impure extern corollaries for memEnv
  cells and result QTyp, proved the `applyExternEffect` loop invariant, and
  deleted `applyFnTClosure_extern_ok_outputRespectsTagMeaning`.  Contract A is
  now represented solely by `externTagMappingRespectsTagMeaning`.

### 6.2 Deleted axiom: `fresh_loc_not_clean`

Deleted in Step 4f.1.  Was dead code — declared but never referenced.

```
(h_p1p : joinPoison p1 p = true)
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r)
(l : Loc) (qt : QTyp)
(hlookup_in : result2.memEnv'.lookup l = none)
(hlookup_out : r.memEnv'.lookup l = some qt) :
¬ qtypCleanUnder r.regime' qt
```

Note: this axiom and `applyFnTClosure_extern_ok_lookup_origin` were **not** in a subsumption
relationship — they used orthogonal preconditions (`joinPoison p1 p = true`
vs `ctx.pc = true`) and referenced different memory environments
(`result2.memEnv'` vs `ctx.memEnv`).  Removal rested solely on dead-code
status.

### 6.3 Key design decisions

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
- Chose typechecker-refactoring approach over proof-only approach for Step 5
  axiom unification.  Proof-only approach would require structural lemmas
  connecting each function's output to internal `resolveSyntaxPred` calls
  (especially the inline `for` loop in `applyFnTClosure`).  Extracting the
  effect-loop body as a named helper makes per-cell reasoning direct.
- Rejected no-precondition axiom shape for unified resolution axiom:
  `resolveSyntaxPred_respectsTagMeaning` without a `tm`-to-mapping
  hypothesis is unsound (counterexample: `tm = {}` with any `guardClosure`
  resolution).  With `TagMappingRespectsTagMeaning` as a hypothesis, the
  `resolveSyntaxPred` step is likely provable as a lemma (not an axiom).
  The true semantic boundary is `TagMappingRespectsTagMeaning` itself:
  that `tm` maps freshly allocated tags to the descriptors that the
  resolution pipeline will produce.  Step 5a will confirm this structure.
- Rejected the first Step 5c instinct to prove nested extern cases from
  `wfTagMeaningCtx tm (ctxAfter ctx result2)` alone.  That hypothesis covers
  the current context, but nested extern returns store
  `VarTypeEnv.toCaptured unifiedEnv` inside the returned closure type.  The
  proof needs an extern-specific captured-env transfer lemma.
- Rejected adding a duplicate `VarTypeEnv.ofCaptured` lookup bridge lemma.
  `list_lookup_of_ofCaptured_lookup` already provides the needed bridge;
  the missing ingredient is the extern-return transfer from the returned
  arrow/parrow QTyp back to `unifiedEnv`.
- Confirmed that the nested pure-extern route works without widening the
  public interface beyond the call-site derivable `hcapTm` / `hargTm`
  obligations.  The remaining impure proof should reuse that same return-side
  structure before tackling the effect-loop invariant.
- Confirmed that the full Step 5 factoring works cleanly: one semantic axiom
  about the tag mapping plus structural corollaries for all three former
  per-entry-point Contract A obligations.
- Confirmed the key call-site pattern for nested extern returns: captured-env
  well-formedness is derived where the corollary is used, by descending from
  the enclosing function type's `QTypRespectsTagMeaning` through
  `QTypInQTyp.in_arrow` / `QTypInQTyp.in_parrow` and transitivity, yielding
  the local `hcapTm` / `hargTm` obligations without widening the global proof
  interface.
- Known proof pitfall: lemmas returning `QTypRespectsTagMeaning` often do not
  close goals with a bare `exact`, even when the statement appears
  definitionally identical.  The reliable pattern is
  `intro qt' k d hinq hqd; exact (lemma ...) hinq hqd`, especially around the
  reducible/unfolded presentation of `QTypRespectsTagMeaning`.
- Confirmed that the clean-lookup provenance statement was already proved at
  the whole-expression level.  The remaining Contract B work is therefore a
  **local axiom shrink** in the impure extern app case, not discovery of a
  new global bridge from `result2.memEnv'` back to `ctx.memEnv`.

### 6.4 Reference points

Current-branch helpers:

- `LeanProofs/RegimeConsistency.lean`:
  `QTypInQTyp_fn_extern_root_or_self`,
  `QTypInQTyp_pfn_extern_root_or_self`,
  `list_lookup_of_ofCaptured_lookup`,
  `EnvRespectsTagMeaning_updateMemEnv`,
  `EnvRespectsTagMeaning_list_fold_updateMemEnv`,
  `QTypRespectsTagMeaning_fn_extern`,
  `QTypRespectsTagMeaning_pfn_extern`
- `LeanProofs/TypeSafety.lean`:
  `typecheckExpr_preserves_TagBoundedCtx`,
  `typecheckExpr_TagBoundedCtx_varEnv_update`,
  `matchGuard_tag_bounded`,
  `tagEnvBounded_insert_of_lt`,
  `list_fold_updateMemEnv_lookup_eq_of_not_mem`,
  `applyPFnTClosure_extern_memEnv_eq` (proves pure extern memory identity),
  `applyPFnTClosure_extern_regime_eq`
- `LeanProofs/StepFR.lean`:
  `list_lookup_mem`,
  `QTypRespectsTagMeaning_fn_extern_ofCaptured`,
  `QTypRespectsTagMeaning_pfn_extern_ofCaptured`,
  `QTypRespectsTagMeaning_noPred_poison_transport`,
  `locset_fold_updateMemEnv_allCellsRespect`,
  `applyExternEffect_preserves_allCellsRespect`,
  `forIn_effects_loop_preserves_allCellsRespect`,
  `applyFnTClosure_extern_ok_memCellsRespect`,
  `applyFnTClosure_extern_ok_qualTypeRespects`,
  `applyFnTClosure_extern_ok_outputRespectsTagMeaning_corollary`,
  `typecheckExpr_lookup_origin_of_pc_true_split`,
  `typecheckExpr_clean_lookup_origin_of_pc_true`,
  `QTypRespectsTagMeaning_of_arrow_captured_lookup`,
  `QTypRespectsTagMeaning_of_parrow_captured_lookup`,
  `wfTagMeaningCtx_closure_body`,
  `wfTagMeaningCtx_pclosure_body`,
  `typecheckExternVal_QTypRespectsTagMeaning_corollary`
