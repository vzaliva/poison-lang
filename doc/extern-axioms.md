# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Step 4e review completed. The 6 declared axioms have been audited against
the codebase, revealing:

- **1 dead axiom** (`fresh_loc_not_clean`) — declared but never used
- **2 mergeable axioms** (#1 + #2, identical preconditions, different outputs)
- **5 live axioms**, naturally organized into 2 high-level contracts
- **4 declarations** after merging #1 + #2 (bundling 2 conjuncts)

Required next action: remove the dead axiom and optionally merge #1 + #2
(see §5 for concrete proposal).

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** add any new `axiom`

**Branch status (2026-04-13, branch `new-iofree`)**

- `lake build` succeeds with **0 sorry, 0 warnings**
- all `LeanProofs/` files compile cleanly
- axiom count: **6 declared, 5 live** (1 dead axiom to remove;
  2 declarations mergeable into 1, bundling 2 conjuncts)

## 1. Overview: two high-level contracts

The 6 declared axioms in `LeanProofs/StepFR.lean` fall into two semantic
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

### 2.1 `applyFnTClosure_extern_ok_memEnv_QTypRespectsTagMeaning`

**StepFR.lean:6099.  Contract A.  LIVE — used at line 6141.**

```
(hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r)
(l : Loc) (qt : QTyp)
(hlookup : r.memEnv'.lookup l = some qt) :
QTypRespectsTagMeaning tm qt
```

**Role:** Every memory cell in the output of an impure extern application
respects `TagMeaning`.  Feeds the proved structural theorem
`applyFnTClosure_extern_ok_wfTagMeaningCtx` (line 6113).

**Why semantic:** The effect loop writes cells with resolved predicates whose
guard tags are freshly allocated.  Whether those tags are consistent with an
arbitrary `tm` satisfying the precondition is a semantic claim about the
tag-allocation/resolution pipeline.

**Overlap with §2.2:** Identical preconditions (`hwf`, `happly`); differs
only in conclusion target (memory cells vs result `QTyp`).  These two can be
**merged** into a single axiom with a conjunction (see §5).

**Verdict:** Irreducibly semantic.  Merge candidate with §2.2.

### 2.2 `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`

**StepFR.lean:6146.  Contract A.  LIVE — used at lines 8465, StepFRApp:1373.**

```
(hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r) :
QTypRespectsTagMeaning tm r.qualType
```

**Role:** The result `QTyp` of an impure extern application respects
`TagMeaning`.

**Why semantic:** The return predicate is resolved via
`resolveSyntaxPred` using freshly allocated tags.  When
`normalizeAppResultByProvenance` preserves the predicate (i.e., when
`joinPoison p1 p = false`), the result `QTyp` contains a fresh guard tag
that must be covered by `tm`.  This is a genuine assumption about the extern
summary, not derivable from the typechecker equations.

**Overlap with §2.1:** Same preconditions.  Merge candidate.

**Verdict:** Irreducibly semantic.  Merge candidate with §2.1.

### 2.3 `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`

**StepFR.lean:6159.  Contract A.  LIVE — used at lines 8679, StepFRApp:2012.**

```
(hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
(happly : applyPFnTClosure (PFnTClosure.extern …) … = .ok r) :
QTypRespectsTagMeaning tm r.qualType
```

**Role:** Pure-closure analogue of §2.2.

**Why semantic:** Same reasoning as §2.2 — the absence of the effect loop
simplifies the output (no memory writes), but the return predicate resolution
is equally opaque.

**Why not merged with §2.2:** Different function (`applyPFnTClosure` vs
`applyFnTClosure`), different closure type, no `effects` parameter.

**Why no companion memEnv axiom:** Pure externs don't modify memory.
`applyPFnTClosure_extern_memEnv_eq` (TypeSafety.lean:4152) proves
`r2.memEnv' = r1.memEnv'` structurally.

**Verdict:** Irreducibly semantic.  Standalone; no further split or merge.

### 2.4 `applyFnTClosure_extern_ok_lookup_origin`

**StepFR.lean:6172.  Contract B.  LIVE — used at lines 11498, 11672.**

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

### 2.5 `applyFnTClosure_extern_ok_fresh_loc_not_clean`

**StepFR.lean:6195.  Contract B.  DEAD — not used anywhere.**

```
(h_p1p : joinPoison p1 p = true)
(happly : applyFnTClosure (FnTClosure.extern …) … = .ok r)
(l : Loc) (qt : QTyp)
(hlookup_in : result2.memEnv'.lookup l = none)
(hlookup_out : r.memEnv'.lookup l = some qt) :
¬ qtypCleanUnder r.regime' qt
```

**Role (intended):** Fresh memory entries created by impure externs may not
be trusted when the application provenance is tainted.

**Status:** **Dead code.** Declared but not referenced by any lemma or proof
in the codebase.  Grep for `fresh_loc_not_clean` returns only the
declaration site (line 6195).

**Analysis:** Unused and plausibly obsolete.  Likely introduced anticipating
a proof need that was later resolved differently — the provenance proof for
the impure extern case (lines ~11498–11676) uses `lookup_origin` (§2.4)
directly and never invokes this axiom.

Note that §2.4 and §2.5 are **not** ordered by strength.  They use
orthogonal preconditions and reference different memory environments:

| | §2.4 (`lookup_origin`) | §2.5 (`fresh_loc_not_clean`) |
|--|------------------------|------------------------------|
| Precondition | `ctx.pc = true` | `joinPoison p1 p = true` |
| Reference memory | `ctx.memEnv` (pre-argument) | `result2.memEnv'` (post-argument) |
| Concern | Effect-write tainting (line 1294) | Return-QTyp normalization (line 1304) |

The two conditions are independent: `ctx.pc` governs poison on effect-
written cells (`joinPoison ctx.pc effectQt.poison`), while `joinPoison p1 p`
governs the return QTyp normalization (`normalizeAppResultByProvenance`).
Neither subsumes the other.

**Verdict:** Remove — the axiom is dead code regardless of the subsumption
question.

### 2.6 `typecheckExternVal_QTypRespectsTagMeaning_axiom`

**StepFR.lean:6390.  Contract A.  LIVE — used at line 9110.**

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

All four `QTypRespectsTagMeaning` axioms (§2.1–§2.3, §2.6) express the same
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

### 3.2 Overlap between §2.1 and §2.2

These two axioms are about the **same** operation (`applyFnTClosure` for
`FnTClosure.extern`) with **identical** preconditions (`hwf`, `happly`)
and differ only in their conclusion:

| Axiom | Conclusion target |
|-------|-------------------|
| §2.1 (`memEnv_QTypRespectsTagMeaning`) | ∀ l qt in `r.memEnv'` |
| §2.2 (`QTypRespectsTagMeaning`) | `r.qualType` |

They can be merged into a single axiom (see §5).

### 3.3 §2.5 is unused

Axiom §2.5 (`fresh_loc_not_clean`) is declared but never referenced in any
proof.  The provenance proof for the impure extern case uses §2.4
(`lookup_origin`) directly.

§2.4 and §2.5 are **not** in a subsumption relationship — they use
orthogonal preconditions (`ctx.pc = true` vs `joinPoison p1 p = true`) and
reference different memory environments (`ctx.memEnv` vs
`result2.memEnv'`).  See §2.5 for details.  The removal recommendation
rests solely on the axiom being dead code, not on any coverage argument.

### 3.4 Pure vs impure coverage

| Entry point | Contract A (tag meaning) | Contract B (provenance) |
|-------------|--------------------------|-------------------------|
| Impure fn app (`applyFnTClosure`) | §2.1 (memEnv) + §2.2 (result) | §2.4 (lookup_origin) |
| Pure fn app (`applyPFnTClosure`) | §2.3 (result only) | Not needed (proved: memEnv unchanged) |
| Extern value (`typecheckExternVal`) | §2.6 (result only) | Not needed (fresh cell has `noPred`) |

This coverage is complete and minimal for the current extern model.

## 4. Consolidated contract floor

### After removing dead axiom (5 axioms)

| # | Axiom | Contract | Category |
|---|-------|----------|----------|
| A1 | `applyFnTClosure_extern_ok_memEnv_QTypRespectsTagMeaning` | A | effect-write semantic |
| A2 | `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | A | result semantic (impure) |
| A3 | `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | A | result semantic (pure) |
| A4 | `typecheckExternVal_QTypRespectsTagMeaning_axiom` | A | value semantic |
| B1 | `applyFnTClosure_extern_ok_lookup_origin` | B | provenance |

### After merging A1 + A2 (4 declarations, 5 semantic obligations)

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

## 5. Proposed changes

### 5.1 Remove dead axiom (immediate, no proof impact)

Delete `applyFnTClosure_extern_ok_fresh_loc_not_clean` (StepFR.lean:6195–
6207).  It is unused; removal requires no proof changes.

### 5.2 Merge A1 + A2 (optional, cosmetic consolidation)

Replace axioms §2.1 and §2.2 with:

```lean
axiom applyFnTClosure_extern_ok_outputRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect)
  (capturedEnv : CapturedVarEnv)
  (r : TypeResult)
  (hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv)
    st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  (∀ (l : Loc) (qt : QTyp), r.memEnv'.lookup l = some qt →
    QTypRespectsTagMeaning tm qt) ∧
  QTypRespectsTagMeaning tm r.qualType
```

Proof-site changes:

- `applyFnTClosure_extern_ok_wfTagMeaningCtx` (line 6141): extract `.1`
- StepFR.lean:8465: extract `.2`
- StepFRApp.lean:1373: extract `.2`

This is a small, mechanical refactoring with no semantic change.

### 5.3 Future: axiomatize resolution primitive (speculative)

All Contract A axioms derive from the same semantic principle about
`collectAndAllocExternTags` → `resolveSyntaxPred`.  If this pipeline were
extracted as a standalone lemma target, a single axiom about the resolution
step could replace all three per-entry-point axioms.  This would require:

1. Refactoring `applyFnTClosure`, `applyPFnTClosure`, and
   `typecheckExternVal` to expose the resolution result as an
   intermediate value.
2. Proving structural lemmas that connect each function's output to the
   resolution step.

Estimated reduction: 3 axioms → 1 axiom (plus ~3 structural lemmas).
This is a significant refactoring effort and is recorded here as a
potential future direction, not an immediate action.

### 5.4 Future: factor poison conjunct of B1 (speculative)

The first conjunct of `lookup_origin` (§2.4) — that clean cells in the
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

**Current plan status:** structural reduction work is complete (Steps 1–4d).
Step 4e review is complete.  The branch sits at 6 declared axioms (5 live,
1 dead).

### Step 4e. Accept the contract floor ✓

**Status:** complete

Findings:

1. All 5 live axioms are irreducibly semantic — no further reduction route
   is available without either weakening the extern model, refactoring the
   typechecker to expose shared primitives, or moving assumptions to a
   different interface.
2. The 1 dead axiom (`fresh_loc_not_clean`) should be removed.
3. Merging §2.1 + §2.2 is a clean cosmetic improvement.
4. The declaration count can be reduced to **4** (by bundling §2.1 + §2.2),
   packaging **5 semantic obligations** (the merged axiom carries two
   conjuncts) into 3 Tag Meaning Soundness declarations + 1 Trust
   Provenance declaration.

### Step 4f. Clean up (proposed)

Targets:

1. Delete `applyFnTClosure_extern_ok_fresh_loc_not_clean`
2. (Optional) Merge §2.1 + §2.2 into `…_outputRespectsTagMeaning`
3. Verify `lake build` clean

Done means:

- axiom count is 5 (after deletion) or 4 (after merge)
- `lake build` succeeds with 0 sorry, 0 warnings
- this document updated with final status

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

### 7.2 Key design decisions

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

### 7.3 Reference points

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
