# Extern Functions: Remaining Axioms on `new-iofree`

## Purpose

This note records the current extern-related proof surface on the `new-iofree`
branch, explains why the remaining axioms exist, and classifies each one as:

- a **foundational extern contract** obligation that is not expected to be
  provable from the current typechecker alone, or
- a **provable proof obligation** that should disappear once the right
  infrastructure or theorem shape is in place.

It is modeled on the older `iofree` branch document, but reflects the current
state of this branch rather than the earlier migration attempt.

## Current Status

As of the current repository state:

- `lake build` succeeds
- `LeanProofs/` contains **8 `sorry`** statements in **4 declarations**
- there are **11 explicit axiom declarations**
  - 10 in `LeanProofs/StepFR.lean`
  - 1 in `LeanProofs/TypeSafety.lean`

### Axiom table

| # | Axiom | File | Group | Assessment |
|---|-------|------|-------|------------|
| 1 | `applyFnTClosure_extern_ok_wfTagMeaningCtx` | StepFR | 3 | Bundled effect-loop obligation |
| 2 | `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | StepFR | 1 | Foundational semantic extern contract |
| 3 | `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | StepFR | 1 | Foundational semantic extern contract |
| 4 | `applyFnTClosure_extern_ok_lookup_origin` | StepFR | 4 | Hard effect-loop provenance |
| 5 | `applyFnTClosure_extern_ok_fresh_loc_not_clean` | StepFR | 3 | Likely collapses with LocSet invariant |
| 6 | `applyFnTClosure_extern_ok_guardClosure_tag_absent` | StepFR | 2 | **Proved alternative exists** (`*_of_tagEnvBounded`) |
| 7 | `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | StepFR | 2 | **Proved alternative exists** (`*_of_tagEnvBounded`) |
| 8 | `typecheckExternVal_QTypRespectsTagMeaning_axiom` | StepFR | 1 | Foundational (split from old bundled axiom) |
| 9 | `typecheckExternVal_preserves_lookup_origin_axiom` | StepFR | 4 | **Restated** with `hpre : ctx.memEnv.contains l` |
| 10 | `typecheckExternVal_guardClosure_pred_implies_tag_absent` | StepFR | 2 | **Proved alternative exists** (`*_of_tagEnvBounded`) |
| 11 | `applyFnTClosure_extern_wfTypeResult` | TypeSafety | 3 | Likely provable from LocSet allocation invariant |

### Sorry table

| File | Declaration | Count | Cause |
|------|------------|-------|-------|
| TypeSafety.lean | `typecheckExpr_preserves_tagEnvBounded_main` | 2 | ite mode 1/2 (matchGuard predicate-tag bound) |
| StepFRIte.lean | `stepFR_ite` (inside `hclean_back_to_res1`) | 4 | Phase 1: fresh-location contradiction |
| StepFRAssign.lean | `assign_final_clean_preservation` | 1 | Phase 1: fresh-location contradiction |
| StepFRApp.lean | `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true` | 1 | Phase 1: fresh-location contradiction |

## Changes From Original State

### 1. Restated `typecheckExternVal_preserves_lookup_origin_axiom` (was false)

The original axiom was false for `ref int` extern values: `surfaceSpecToQTyp`
allocates a fresh location with a clean `noPred` cell, violating the claim
that clean output cells must have clean input origins.

**Fix**: Added `(hpre : ctx.memEnv.contains l)` restricting the conclusion to
pre-existing locations. Cascaded through:
- `typecheckExpr_lookup_origin_of_pc_true_split` (conclusion + ~28 IH calls
  threaded with `typecheckExpr_mem_contains_preserved` for monotonicity)
- `typecheckExpr_lookup_poison_origin_of_pc_true`
- `typecheckExpr_lookup_guard_origin_of_pc_true`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- ~18 consumer sites across `FaultRobustnessProofs.lean`, `StepFROp.lean`,
  `StepFRSeq.lean`, `StepFRIte.lean`, `StepFRVlet.lean`, `StepFRAssign.lean`,
  `StepFRApp.lean`
- `typecheckExpr_lookup_clean_back_of_pc_true` was unchanged (already had
  `ctx.memEnv.lookup l = some qt_in`)

**Exposed 6 sorry** in 3 declarations that previously relied on the false
axiom's contrapositive ("fresh locations can't be clean under `pc = true`"),
which is also false for `externVal ref int`. These sorry are in
fresh-location code paths where the old proof derived contradiction by calling
`typecheckExpr_clean_lookup_origin_of_pc_true` on a location known to be absent
from the input, then contradicting the result. With the `hpre` precondition,
the lemma can't be called for absent locations. See "Design Decisions Needed"
below for resolution options.

### 2. Split `typecheckExternVal_preserves_wfTagMeaningCtx_axiom`

The old axiom bundled two conjuncts:
```
wfTagMeaningCtx tm (ctxAfter ctx res) ∧ QTypRespectsTagMeaning tm res.qualType
```

Split into:
- **Proved lemma** `typecheckExternVal_preserves_wfTagMeaningCtx` — the
  structural half. Proof uses `EnvRespectsTagMeaning_updateMemEnv`: the only
  memEnv change is inserting a `⟨ETyp.int, false, Predicate.noPred⟩` cell
  (for `ref int`), which trivially satisfies `QTypRespectsTagMeaning`.
  Helper: `surfaceSpecToQTyp_preserves_EnvRespectsTagMeaning`.
- **Axiom** `typecheckExternVal_QTypRespectsTagMeaning_axiom` — the
  foundational semantic half. This is irreducible: it asserts that the
  resolved extern predicate's guard tags map to the right `GuardDesc` in `tm`.

### 3. Bounded-tags invariant infrastructure (Group 2 axioms)

All infrastructure lives in `TypeSafety.lean` (typechecker layer, no FR leak).
The 3 Group 2 axioms are **NOT yet eliminated** — they remain as axioms used
by the FR proofs. But proved alternative lemmas exist alongside them, ready
for when the design decision on threading is made.

#### Definitions

- `tagEnvBounded (tagEnv : TagEnv) (nextTag : Tag) : Prop` — all keys in
  tagEnv are < nextTag
- `tagEnvBoundedInCtx (ctx : TypeContext) : Prop` — abbreviation for
  `tagEnvBounded ctx.tagEnv ctx.nextTag`

#### Key lemmas (TypeSafety.lean)

| Lemma | Purpose |
|-------|---------|
| `tagEnvBounded_get_none_of_ge` | If `k ≥ nextTag` and tagEnv bounded, then `tagEnv.get? k = none` |
| `tagEnvBounded_mono` | Bounded at `nt` implies bounded at `nt' ≥ nt` |
| `collectAndAllocExternTags_mapping_values_ge` | All tags in the allocation mapping are ≥ input nextTag |
| `forIn_tag_mapping_values_ge` | Helper: inductive core of the above |
| `joinTagEnvs_preserves_tagEnvBounded` | `joinTagEnvs` produces a subset of keys → bounded preserved |
| `joinTagEnvs_get_none_of_left_none` | Helper: join drops keys absent from left input |
| `invalidateTagDeps_preserves_tagEnvBounded` | Filter-based assign helper |
| `applyFnTClosure_tagEnvBounded_normal` | Closure application preserves bounded-tags |
| `applyPFnTClosure_tagEnvBounded_normal` | Pure closure application preserves bounded-tags |
| `joinTypeResults_tagEnvBounded` | joinTypeResults fold preserves bounded-tags |
| `typecheckApp_tagEnvBounded_normal` | Full app case helper |
| `typecheckExpr_preserves_tagEnvBounded` | **Preservation theorem** (sorry for ite mode 1/2 only) |

#### Proved alternatives (StepFR.lean, alongside axioms)

| Alternative lemma | Replaces axiom | Extra hypothesis |
|-------------------|----------------|------------------|
| `applyFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded` | axiom #6 | `tagEnvBounded result2.tagEnv' result2.nextTag'` |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded` | axiom #7 | `tagEnvBounded result2.tagEnv' result2.nextTag'` |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent_of_tagEnvBounded` | axiom #10 | `tagEnvBoundedInCtx ctx` |

These are fully proved. They use:
1. Structural tagEnv equality (`applyFnTClosure_extern_tagEnv_eq` etc.)
2. `collectAndAllocExternTags_mapping_values_ge` to show `k ≥ nextTag`
3. `tagEnvBounded_get_none_of_ge` to conclude absence

Helper lemmas used by the proofs:
- `resolveSyntaxPred_guardClosure_tag_from_mapping` — if `resolveSyntaxPred`
  produces `guardClosure k ...`, then `k` came from the mapping
- `returnSpecToQTyp_pred_eq` — `returnSpecToQTyp` preserves the predicate
- `surfaceSpecToQTyp_pred_eq` — `surfaceSpecToQTyp` preserves the predicate

## Why Extern Obligations Remain

Raw extern syntax is still vacuous on the **runtime** side of fault-robustness:

- `Expr.externVal`
- `Expr.externFn`
- `Expr.externPfn`

all evaluate to runtime errors in `LeanPoison/BigStep.lean`.

So the top-level FR theorem still treats raw extern expressions as unreachable
runtime cases. The remaining proof obligations come from the **typing**
machinery instead:

1. `typecheckExternVal`
2. `applyFnTClosure` on `FnTClosure.extern`
3. `applyPFnTClosure` on `PFnTClosure.extern`

These functions resolve symbolic extern predicates, allocate fresh tags, thread
captured environments, and in the impure extern case update memory through the
effects loop. Those typing-side artifacts must satisfy the same internal proof
invariants that regular closures satisfy by induction on their bodies.

## Grouped Analysis

### Group 1: Foundational semantic extern contract

| Axiom | Status |
|-------|--------|
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | Foundational |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | Foundational |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | Foundational (split from old bundled axiom) |

The irreducible semantic content: when extern typing resolves a
`SyntaxPredicate.guardClosure idx arg body`, the resulting concrete tag must
map to the right `GuardDesc` in `tm`. This is a statement about the intended
meaning of the extern spec, not about a structural property of the typechecker.

The old bundled `typecheckExternVal_preserves_wfTagMeaningCtx_axiom` has been
**split**: its `wfTagMeaningCtx` conjunct is now a proved lemma
(`typecheckExternVal_preserves_wfTagMeaningCtx`), and the semantic conjunct
is isolated as `typecheckExternVal_QTypRespectsTagMeaning_axiom`.

### Group 2: Tag freshness via bounded-tags invariant

| Axiom | Status |
|-------|--------|
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | **Proved alternative exists** |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | **Proved alternative exists** |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | **Proved alternative exists** |

These axioms are logically redundant given `tagEnvBounded`. Proved alternative
lemmas (`*_of_tagEnvBounded`) exist in `StepFR.lean`. The axioms remain only
because `tagEnvBounded` has not yet been threaded to the consumption sites in
the FR proofs. See "Design Decisions Needed" for options.

### Group 3: Impure extern effect-loop infrastructure

| Axiom | Status |
|-------|--------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | Bundled effect-loop obligation |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | Likely collapses with LocSet invariant |
| `applyFnTClosure_extern_wfTypeResult` | Likely provable from LocSet allocation invariant |

These require formalizing the LocSet allocation invariant (captured reference
LocSets only contain allocated locations) and reasoning through the effects
loop. See the original analysis (preserved below in the appendix) for detailed
proof routes and `iofree` references.

### Group 4: Provenance obligations

| Axiom | Status |
|-------|--------|
| `applyFnTClosure_extern_ok_lookup_origin` | Hard effect-loop provenance |
| `typecheckExternVal_preserves_lookup_origin_axiom` | **Restated** with pre-existence |

The `typecheckExternVal` axiom has been restated (no longer false). The
`applyFnTClosure` provenance axiom requires dedicated effect-loop reasoning.

## Design Decisions Needed

### Decision 1: How to eliminate Group 2 axioms

The three freshness axioms have proved alternatives that require `tagEnvBounded`
as a hypothesis. The question is how to deliver this hypothesis at the
consumption sites (inside `ioFree_guardClosure_pred_implies_tag_absent` and
two app-branch helpers in `StepFRAssign.lean`).

**Option A: Thread through the typechecker-level lemma only.**
`ioFree_guardClosure_pred_implies_tag_absent` is a standalone typechecker
lemma (not part of `StepFR_IH`). It does its own strong induction on fuel.
Add `tagEnvBoundedInCtx ctx` as a hypothesis, thread through the ~2 IH calls
using `typecheckExpr_preserves_tagEnvBounded`, and pass it to the proved
alternatives at the extern cases. The 5 callers in `stepFR_assign` would
then need to provide `tagEnvBounded` — which could be derived from the
initial context (empty tagEnv, nextTag = 1) plus the preservation theorem,
without modifying `StepFR_IH`.

*Advantage*: No changes to `StepFR_IH` or the FR proof structure.
*Difficulty*: The 5 callers need `tagEnvBounded` for intermediate contexts
derived from the FR proof. This requires proving that the initial context
satisfies `tagEnvBounded` (trivial: empty tagEnv) and that the preservation
theorem delivers it at the right point. May need the FR proof to carry
`tagEnvBounded` anyway, at least for the assign case.

**Option B: Add `tagEnvBounded` to `StepFR_IH`.**
Thread the invariant through the FR proof's inductive hypothesis. This makes
`tagEnvBounded` available at all consumption sites automatically.

*Advantage*: Clean and uniform. All Group 2 axioms eliminated at once.
*Difficulty*: Very invasive. `StepFR_IH` is referenced throughout the FR
proof stack. Every case proof would need to thread the invariant.

**Option C: Prove `tagEnvBounded` is a consequence of `typecheckExpr` success.**
If we could prove `typecheckExpr ctx e fuel = .ok res → tagEnvBoundedInCtx ctx`
(i.e., any context that successfully typechecks an expression is bounded), then
no threading is needed — the hypothesis is free. This would require showing
that the initial context is bounded and that only bounded contexts reach the
typechecker.

*Advantage*: No threading at all. The hypothesis would be derivable on-the-fly.
*Difficulty*: Requires a separate argument about the initial context and the
call chain. May not hold for all intermediate contexts (e.g., ite mode 1/2
inserts matchGuard tags).

**Recommendation**: Option A is the most surgical. The ite mode 1/2 sorry in
the preservation theorem is the only blocker; it requires formalizing that
matchGuard-extracted tags are < nextTag (a predicate-tag-bound invariant).
The `iofree` branch already had `matchGuard_tag_in_bound` as a template.

### Decision 2: How to fix the Phase 1 sorry (fresh-location contradiction)

The 6 sorry exposed by the `lookup_origin` restatement are in fresh-location
code paths. The old proofs used `typecheckExpr_clean_lookup_origin_of_pc_true`
by contrapositive: "location not in input → contradiction with the lemma's
output." With the `hpre` precondition, this contrapositive is blocked.

The underlying issue: `externVal ref int` can create fresh clean locations
under `pc = true`. The old axiom (which was false) hid this.

**Option A: Prove fresh locations under `pc = true` are tainted for non-extern expressions.**
If the body/branch expression doesn't contain `externVal`, fresh locations
are always tainted. Add a predicate `noExternVal e` or use the existing
`pureCtx` flag to restrict.

*Difficulty*: Requires reasoning about expression structure, not just typing.

**Option B: Derive `ctx.memEnv.contains l` from the FR context.**
The FR proofs reason about locations that exist in the pre-body memory. If
the location was inherited from the pre-body context, it exists there. For
truly fresh locations, the FR proof should handle them differently.

*Difficulty*: Site-specific. Some sites (StepFRIte) need `res1.memEnv'.contains l`
which requires `typecheckExpr_mem_contains_preserved` plus `htc1`. The helper
`hclean_back_to_res1` currently lacks `htc1`.

**Option C: Restructure the fresh-location proofs.**
Instead of deriving contradiction, handle the fresh-location case positively:
show that fresh clean extern-allocated cells satisfy the FR spec directly.

*Difficulty*: Requires understanding what the FR spec needs for fresh locations.

**Recommendation**: Option B for StepFRIte and StepFRAssign (thread `htc1`
through the helpers). Option C may be needed for StepFRApp where the location
provably doesn't pre-exist.

## Preservation Theorem Status

`typecheckExpr_preserves_tagEnvBounded` in `TypeSafety.lean` proves that
`tagEnvBounded` is preserved by the typechecker. Current case coverage:

| Expression type | Status |
|----------------|--------|
| num, bool, unit, str | Proved (tagEnv/nextTag unchanged) |
| var | Proved |
| fn, pfn | Proved (tagEnv/nextTag unchanged) |
| externVal | Proved (tagEnv unchanged, nextTag grows) |
| externFn, externPfn | Proved (tagEnv/nextTag unchanged) |
| unaryop, deref | Proved (single sub-expression IH) |
| op, seq | Proved (two sub-expressions IH) |
| vlet | Proved |
| newRef | Proved |
| assign | Proved (uses `invalidateTagDeps_preserves_tagEnvBounded`) |
| ite mode 3/4 (standard) | Proved (uses `joinTagEnvs_preserves_tagEnvBounded`) |
| ite mode 1/2 (guard) | **sorry** — needs `k < ctx.nextTag` for matchGuard tag |
| app | Proved (uses `typecheckApp_tagEnvBounded_normal`) |

The 2 remaining sorry both need the same thing: a proof that `matchGuard`
returns a tag `k < ctx.nextTag`. This requires either:
- A predicate-tag-bound invariant (all tags in predicates in varEnv/memEnv
  are < nextTag), or
- A direct lemma about matchGuard extracting only bounded tags.

The `iofree` branch had `matchGuard_tag_in_bound` in `StepFRIte.lean` as a
template for this.

## Expected End State

The most plausible long-term outcome is:

- the current 11 axioms do **not** represent the true minimum
- the likely permanent floor is the semantic tag-meaning contract:
  - `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`
  - `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`
  - `typecheckExternVal_QTypRespectsTagMeaning_axiom`

Everything else should be treated as either:

- a proof-engineering obligation
- a missing invariant
- or a theorem-shape issue that still needs to be restated cleanly

## Appendix: Detailed Proof Routes (from original analysis)

### Effect-loop infrastructure

`applyFnTClosure_extern_ok_wfTagMeaningCtx`: The semantic split is only the
first step. The real work is the impure extern effects loop: one must reason
through the resolved effect predicates written by `LocSet.fold ... updateMemEnv`,
then lift those writes through the tag-meaning infrastructure. Once one assumes
the relevant `QTypRespectsTagMeaning` facts for those effect predicates, the
remaining proof should be structural. Use `EnvRespectsTagMeaning_updateMemEnv`
and `EnvRespectsTagMeaning_list_fold_updateMemEnv` from `RegimeConsistency.lean`.

`applyFnTClosure_extern_wfTypeResult`: Requires the LocSet allocation invariant
linking captured reference LocSets to allocated memory locations. The `iofree`
branch had `locset_fold_max_ge_init`, `locset_fold_max_succ_ge_of_mem`, and
`locset_fold_updateMemEnv_preserves_contains` as local helpers.

`applyFnTClosure_extern_ok_fresh_loc_not_clean`: Likely collapses once the
LocSet invariant shows effect-loop writes only touch already-allocated
locations. The regular-case template is
`applyFnTClosure_fresh_lookup_not_clean_of_p1p_true` in `StepFRApp.lean`.

### Provenance

`applyFnTClosure_extern_ok_lookup_origin`: Genuinely hard. The effects loop
can update memory at multiple reference targets from the captured environment.
Needs: "all writes come from these effect targets" + provenance back to
already-originating memory. Better treated as a dedicated task after simpler
invariants are in place.

`typecheckExternVal_preserves_lookup_origin_axiom`: Restated (no longer false).
The `iofree` branch warned this was partly a theorem-shape issue. Further work
should focus on the restated version.

### iofree branch references

- `predTagsBoundedInCtx` in `iofree:LeanProofs/StepFR.lean` — old bounded-tags
  invariant (architecture-specific, don't copy literally)
- `matchGuard_tag_in_bound` in `iofree:LeanProofs/StepFRIte.lean` — bridge
  from matchGuard to bounded tag
- `collectAndAllocExternTags_nextTag_ge` and `typecheckExternVal_nextTag_mono`
  in `iofree:LeanProofs/TypeSafety.lean` — fresh-tag monotonicity templates
  (already ported to this branch)
- `QTypRespectsTagMeaning_fn_extern` and `QTypRespectsTagMeaning_pfn_extern`
  in `LeanProofs/RegimeConsistency.lean` — captured-environment tag-meaning
  helpers (already available on this branch)
- `EnvRespectsTagMeaning_updateMemEnv` in `RegimeConsistency.lean` — key
  building block for effect-loop tag-meaning proofs (already available)
