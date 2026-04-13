# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Step 4f cleanup complete.  The branch is at its extern contract floor.

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** add any new `axiom`

**Branch status (2026-04-13, branch `new-iofree`)**

- `lake build` succeeds with **0 sorry, 0 warnings**
- all `LeanProofs/` files compile cleanly
- axiom count: **4 declarations** (5 semantic obligations)

## 1. Overview: two high-level contracts

The 4 axiom declarations in `LeanProofs/StepFR.lean` fall into two semantic
contracts about extern typechecking behavior:

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

## 2. Per-axiom review

### 2.1 `applyFnTClosure_extern_ok_outputRespectsTagMeaning`

**StepFR.lean:6098.  Contract A.  Two conjuncts.**

```
(hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r) :
(∀ l qt, r.memEnv'.lookup l = some qt → QTypRespectsTagMeaning tm qt) ∧
QTypRespectsTagMeaning tm r.qualType
```

**Role:** All `QTyp` values produced by an impure extern application —
memory cells written by the effect loop AND the result type — respect
`TagMeaning`.

- **Conjunct 1** (memEnv cells): feeds the proved structural theorem
  `applyFnTClosure_extern_ok_wfTagMeaningCtx` (line 6113) via `.1`.
- **Conjunct 2** (result QTyp): used directly in the FR proof
  (StepFR.lean:8451 via `.2`, StepFRApp.lean:1373 via `.2`).

**Why semantic:** The effect loop writes cells with resolved predicates whose
guard tags are freshly allocated.  The return predicate is similarly resolved
via `resolveSyntaxPred`.  When `normalizeAppResultByProvenance` preserves the
predicate (i.e., when `joinPoison p1 p = false`), the result `QTyp` contains
a fresh guard tag that must be covered by `tm`.  Whether freshly allocated
tags are consistent with an arbitrary `tm` satisfying the precondition is a
semantic claim about the tag-allocation/resolution pipeline.

**Verdict:** Irreducibly semantic.  Both conjuncts required.

### 2.2 `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`

**StepFR.lean:6145.  Contract A.  Used at lines 8679, StepFRApp:2012.**

```
(hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
(happly : applyPFnTClosure (PFnTClosure.extern …) … = .ok r) :
QTypRespectsTagMeaning tm r.qualType
```

**Role:** Pure-closure analogue of §2.1 (second conjunct).

**Why semantic:** Same reasoning as §2.1 — the absence of the effect loop
simplifies the output (no memory writes), but the return predicate resolution
is equally opaque.

**Why not merged with §2.1:** Different function (`applyPFnTClosure` vs
`applyFnTClosure`), different closure type, no `effects` parameter.

**Why no companion memEnv axiom:** Pure externs don't modify memory.
`applyPFnTClosure_extern_memEnv_eq` (TypeSafety.lean:4152) proves
`r2.memEnv' = r1.memEnv'` structurally.

**Verdict:** Irreducibly semantic.  Standalone; no further split or merge.

### 2.3 `applyFnTClosure_extern_ok_lookup_origin`

**StepFR.lean:6158.  Contract B.  Used at lines 11498, 11672.**

```
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r)
(l : Loc) (qt_out : QTyp) (hlookup : r.memEnv'.lookup l = some qt_out)
(hpc : ctx.pc = true) :
(qt_out.poison = false →
   ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false) ∧
∀ k, qtypGuardTag qt_out = some k → r.regime'.lookup? k = some true →
   qt_out.etyp.isFunctionType = false →
   ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
     qtypGuardTag qt_in = some k ∧ ctx.regime.lookup? k = some true ∧
     qt_in.etyp.isFunctionType = false
```

**Role:** Provenance: trusted output cells produced by an impure extern
application come from trusted input cells.  Two conjuncts:

1. **Poison provenance:** Clean outputs (poison = false) came from clean
   inputs in `ctx.memEnv`.
2. **Guard provenance:** Guard-protected non-function outputs traced back to
   guard-protected inputs with the same tag, and the tag was already active
   in the input regime.

**Why semantic:** The axiom traces trust through `ctx.memEnv`, which is the
memory **before** both argument and function evaluation.  The effect loop
operates on `result2.memEnv'` (which extends `ctx.memEnv` via argument/function
evaluation).  The axiom's strength lies in bridging this gap:

- The poison conjunct is *partially* structural: the effect loop writes with
  `joinPoison ctx.pc effectQt.poison`, which equals `true` when
  `ctx.pc = true`, so no effect-written cell can have `poison = false`.
  This means clean cells in `r.memEnv'` are untouched cells from
  `result2.memEnv'`.  The remaining gap—tracing from `result2.memEnv'`
  back to `ctx.memEnv`—could in principle be factored into a separate
  structural memory-monotonicity lemma, but this refactoring has not been
  done.

- The guard conjunct is genuinely semantic: the effect loop can overwrite
  cells with new guard predicates (freshly resolved), and the regime passes
  through unchanged (`r.regime' = result2.regime'`).  Tracing guard tags
  and regime membership all the way back to `ctx.regime` requires reasoning
  about what the extern summary preserves.

**Why no pure analogue:** Pure externs don't modify memory, so provenance is
trivial (the output IS the input).  Proved via
`applyPFnTClosure_extern_memEnv_eq`.

**Verdict:** Irreducibly semantic.  Standalone.  Poison conjunct is a
candidate for partial structural factoring in a future pass.

### 2.4 `typecheckExternVal_QTypRespectsTagMeaning_axiom`

**StepFR.lean:6362.  Contract A.  Used at line 9110.**

```
(hwf : wfTagMeaningCtx tm ctx)
(htc : typecheckExternVal ctx typ poison pred = .ok res) :
QTypRespectsTagMeaning tm res.qualType
```

**Role:** The result `QTyp` of `typecheckExternVal` respects `TagMeaning`.

**Why semantic:** The structural parts are already separated
(`typecheckExternVal_preserves_wfTagMeaningCtx` is proved).  The remaining
content is semantic: `typecheckExternVal` allocates fresh tags
(`collectAndAllocExternTags [pred] ctx.nextTag`), resolves the predicate
(`resolveSyntaxPred`), and converts the surface type (`surfaceSpecToQTyp`).
The claim that the resulting QTyp's guard descriptors are all registered in
`tm` is an assumption about the resolution pipeline.

**Why no companion memEnv axiom:** `typecheckExternVal` only modifies memory
when the surface type is `ref int` (adding a fresh cell with
`⟨ETyp.int, false, Predicate.noPred⟩`).  A cell with `noPred` has no guard
descriptors, so `QTypRespectsTagMeaning` holds trivially for such cells.
The structural `wfTagMeaningCtx` preservation proof handles this.

**Verdict:** Irreducibly semantic.  Standalone; no merge opportunity.

## 3. Redundancy and overlap analysis

### 3.1 Shared semantic root of Contract A axioms

All `QTypRespectsTagMeaning` obligations (§2.1 both conjuncts, §2.2, §2.4) express the same
fundamental principle:

> **Resolved extern predicates respect tag meaning.**  When the
> typechecker's tag-allocation/resolution pipeline
> (`collectAndAllocExternTags` → `resolveSyntaxPred`) produces concrete
> predicates from symbolic extern specifications, the resulting `QTyp`
> values have all guard descriptors properly registered in the `TagMeaning`.

They cannot be unified today because they occur inside three separate
functions (`applyFnTClosure`, `applyPFnTClosure`, `typecheckExternVal`) with
different signatures.  A future refactoring that extracts the shared
resolution primitive as a standalone function could potentially express the
semantic core as a **single axiom** about that primitive, with the per-entry-
point axioms becoming proved structural corollaries.

### 3.2 Pure vs impure coverage

| Entry point | Contract A (tag meaning) | Contract B (provenance) |
|-------------|--------------------------|-------------------------|
| Impure fn app (`applyFnTClosure`) | §2.1 (memEnv + result) | §2.3 (lookup_origin) |
| Pure fn app (`applyPFnTClosure`) | §2.2 (result only) | Not needed (proved: memEnv unchanged) |
| Extern value (`typecheckExternVal`) | §2.4 (result only) | Not needed (fresh cell has `noPred`) |

This coverage is complete and minimal for the current extern model.

## 4. Consolidated contract floor

### Current state (4 declarations, 5 semantic obligations)

| # | Axiom | Contract | Category |
|---|-------|----------|----------|
| A1 | `applyFnTClosure_extern_ok_outputRespectsTagMeaning` | A | impure fn (memEnv + result) |
| A2 | `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | A | pure fn (result) |
| A3 | `typecheckExternVal_QTypRespectsTagMeaning_axiom` | A | extern val (result) |
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

## 5. Future directions (speculative)

### 5.1 Axiomatize resolution primitive

All Contract A axioms derive from the same semantic principle about
`collectAndAllocExternTags` → `resolveSyntaxPred`.  If this pipeline were
extracted as a standalone lemma target, a single axiom about the resolution
step could replace all three per-entry-point declarations.  This would
require:

1. Refactoring `applyFnTClosure`, `applyPFnTClosure`, and
   `typecheckExternVal` to expose the resolution result as an
   intermediate value.
2. Proving structural lemmas that connect each function's output to the
   resolution step.

Estimated reduction: 3 declarations → 1 axiom (plus ~3 structural lemmas).
This is a significant refactoring effort.

### 5.2 Factor poison conjunct of B1

The first conjunct of `lookup_origin` (§2.3) — that clean cells in the
extern output were not written by the effect loop — is partially structural:

1. The effect loop writes every cell with
   `poison = joinPoison ctx.pc effectQt.poison`.
2. When `ctx.pc = true`, this is always `true`.
3. Therefore no effect-written cell has `poison = false`.

The remaining gap (tracing from `result2.memEnv'` back to `ctx.memEnv`)
could be bridged by memory-monotonicity.  However, the guard conjunct
remains genuinely semantic, so the axiom cannot be fully eliminated this
way.  A partial factoring would reduce the axiom's surface but not remove
it.

## 6. Plan

Step 4f is complete.  The branch is at its extern contract floor:
4 axiom declarations, 5 semantic obligations, `lake build` clean.

## 7. History

This section records completed work and design decisions for reference.

### 7.1 Steps completed

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

### 7.2 Deleted axiom: `fresh_loc_not_clean`

Deleted in Step 4f.1.  Was dead code — declared but never referenced.

```
(h_p1p : joinPoison p1 p = true)
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r)
(l : Loc) (qt : QTyp)
(hlookup_in : result2.memEnv'.lookup l = none)
(hlookup_out : r.memEnv'.lookup l = some qt) :
¬ qtypCleanUnder r.regime' qt
```

Note: this axiom and `lookup_origin` (§2.3) were **not** in a subsumption
relationship — they used orthogonal preconditions (`joinPoison p1 p = true`
vs `ctx.pc = true`) and referenced different memory environments
(`result2.memEnv'` vs `ctx.memEnv`).  Removal rested solely on dead-code
status.

### 7.3 Key design decisions

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

### 7.4 Reference points

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
  `tagEnvBounded_insert_of_lt`,
  `applyPFnTClosure_extern_memEnv_eq` (proves pure extern memory identity),
  `applyPFnTClosure_extern_regime_eq`
