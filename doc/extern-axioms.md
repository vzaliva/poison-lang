# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Step 5 is complete.  The Contract A unification target has been reached.

Current status:

1. `§2.4` (`typecheckExternVal_QTypRespectsTagMeaning_axiom`) is replaced by
   `typecheckExternVal_QTypRespectsTagMeaning_corollary`.
2. `§2.2` (`applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`) is replaced by
   `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_corollary`.
3. `§2.1` (`applyFnTClosure_extern_ok_outputRespectsTagMeaning`) is replaced by
   structural corollaries for memEnv cells and result QTyp, combined in
   `applyFnTClosure_extern_ok_outputRespectsTagMeaning_corollary`.
4. The contract floor is now the intended minimum: 1 unified Contract A axiom
   plus 1 Contract B axiom.

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
- Step 5 complete: the remaining axioms are
  `externTagMappingRespectsTagMeaning` (unified Contract A) and
  `applyFnTClosure_extern_ok_lookup_origin` (Contract B)

## 1. Overview: two high-level contracts

The original 4 axiom declarations in `LeanProofs/StepFR.lean` fell into two semantic
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

## 5. Future: factor poison conjunct of B1 (speculative)

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

### Step 5. Unify Contract A into a single tag-mapping axiom

**Status:** completed

**Goal:** Replace the 3 Contract A declarations (§2.1, §2.2, §2.4) with a
single semantic axiom about how freshly allocated tag mappings relate to
`TagMeaning`, plus structural lemmas and corollaries.
Axiom count: 4 → 2 (1 Contract A + 1 Contract B).

**Approach:** First validate the axiom shape on the easiest cases (no code
changes).  Then extract a helper in `Typecheck.lean` to make the impure
effect-loop case provable.  Finally, prove all corollaries and delete the
old axioms.

#### Impact assessment

- **Soundness:** No change — same type system behavior.
- **Precision:** No change — same programs accepted/rejected.
- **Language scope:** No change.
- **Operational semantics:** No change — `beval` unaffected (externs fail
  at runtime regardless).
- **FR property:** Statement unchanged.  Proof restructured internally:
  3 per-entry-point axioms become 1 semantic tag-mapping axiom +
  structural lemmas/corollaries.

#### Analysis: two sources of guard descriptors

Guard descriptors reachable from extern output QTyps come from two sources:

1. **Resolved predicates** (semantic).  Simple returns and effect cells
   produce base-type QTyps (via `returnSpecToQTyp` / `effectSpecToQTyp` —
   both reject arrow types).  `QTypInQTyp` has only the `self` case, so
   the only guard descriptor is in the resolved `Predicate`.

2. **Inherited captures** (structural).  Nested returns (`nestedFn` /
   `nestedPfn`) produce arrow/parrow QTyps with `Predicate.noPred` at the
   top level.  Guard descriptors are reachable only through
   `QTypInQTyp.in_arrow` / `in_parrow`, descending into the deferred
   closure's captured env (`VarTypeEnv.toCaptured unifiedEnv`).  This env
   inherits from the pre-existing context + the argument binding, both of
   which already respect `tm` via `wfTagMeaningCtx` and the IH.

Additionally, `normalizeAppResultByProvenance` (Typecheck.lean:1241) strips
the predicate to `noPred` when `joinPoison p1 p = true`, which eliminates
source 1 in tainted contexts.  In that case, only source 2 remains.

Source 1 is the semantic core — it needs the axiom.  Source 2 is structural
and should be provable from the `wfTagMeaningCtx` precondition.

#### Unified axiom shape

Define a predicate-level respect property:

```lean
inductive PredicateRespectsTagMeaning (tm : TagMeaning) : Predicate → Prop where
  | noPred : PredicateRespectsTagMeaning tm .noPred
  | guardOnly (k : Tag) : PredicateRespectsTagMeaning tm (.guardOnly k)
  | guardClosure (k : Tag) (arg : Name) (body : PExpr) (cap : CapturedVarEnv)
      (hlookup : tm.lookup k = some { argName := arg, body := body, capEnv := cap }) :
      PredicateRespectsTagMeaning tm (.guardClosure k arg body cap)
```

The axiom must include a hypothesis connecting `tm` to the tag mapping.
Without it the axiom is unsound: take `tm = {}`, any successful
`guardClosure` resolution produces a tag not in `tm`, and the conclusion
is immediately false.

Define a `TagMappingRespectsTagMeaning` predicate connecting `tm` to the
tag mapping (see Option A / Option B below for the exact formulation —
the `toPExpr` scoping matters).

Given `TagMappingRespectsTagMeaning`, the `resolveSyntaxPred` step is
likely **provable**, not semantic.  For `guardClosure`: `hcompat` +
`hmember` + `hresolve` yield the exact `tm.lookup` fact.  For `guardOnly`
and `noPred`: `PredicateRespectsTagMeaning` holds immediately via the
corresponding constructor.  (There
is already a related extraction helper at StepFR.lean:6181.)

So `resolveSyntaxPred_respectsTagMeaning` should first be attempted as a
**lemma**:

```lean
lemma resolveSyntaxPred_respectsTagMeaning
  (tm : TagMeaning)
  (pred : SyntaxPredicate) (env : VarTypeEnv)
  (mapping : ExtTreeMap TagIndex Tag)
  (preds : List SyntaxPredicate)
  (resolvedPred : Predicate)
  (hcompat : TagMappingRespectsTagMeaning tm mapping preds env)
  (hmember : pred ∈ preds)
  (hresolve : resolveSyntaxPred pred env mapping = .ok resolvedPred) :
  PredicateRespectsTagMeaning tm resolvedPred
```

If this proof goes through, the **only** remaining semantic boundary is
`TagMappingRespectsTagMeaning` itself: each call site must establish
that `tm` maps the freshly allocated tags to the guard descriptors that
`resolveSyntaxPred` will produce.

Since `tm` is universally quantified and `wfTagMeaningCtx` does not
constrain `tm` for fresh tags, this derivation is almost certainly
**not** structurally possible.  Therefore `TagMappingRespectsTagMeaning`
is the single surviving Contract A axiom.

However, the axiom must not be stronger than the current contract.
`collectAndAllocExternTags` only allocates tags and checks index
consistency (Typecheck.lean:814) — it does not call `body.toPExpr`,
which can fail for non-pure expressions (Syntax.lean:380).  So an axiom
conditioned solely on `collectAndAllocExternTags` success would assert
`toPExpr` success for bodies that might fail, making it stronger than the
current axioms (which are conditioned on full entry-point success).

Two options to match the current strength:

**Option A — scope to successful resolution** (simplest; folds structural
reasoning into the axiom but keeps the axiom small):

```lean
axiom externResolvedPredRespectsTagMeaning
  (tm : TagMeaning)
  (pred : SyntaxPredicate) (env : VarTypeEnv)
  (mapping : ExtTreeMap TagIndex Tag)
  (resolvedPred : Predicate)
  (hresolve : resolveSyntaxPred pred env mapping = .ok resolvedPred)
  : PredicateRespectsTagMeaning tm resolvedPred
```

This says: when resolution succeeds (implying `toPExpr` succeeded), the
resolved predicate respects `tm`.  Advantage: ties the semantic claim to
the same success condition as the current axioms and is about a single
predicate, not an entire `TypeResult`.  Disadvantage: folds the structural
`resolveSyntaxPred` case analysis into the axiom rather than separating
it as a lemma.

**Option B — separate structural from semantic** (cleaner layering):

Weaken `TagMappingRespectsTagMeaning` to only cover bodies whose
`toPExpr` succeeds:

```lean
def TagMappingRespectsTagMeaning (tm : TagMeaning)
    (mapping : ExtTreeMap TagIndex Tag)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : Prop :=
  ∀ idx tag, mapping.get? idx = some tag →
    ∀ arg body pbody,
      (SyntaxPredicate.guardClosure idx arg body) ∈ preds →
      body.toPExpr = .ok pbody →
      tm.lookup tag = some { argName := arg, body := pbody,
                             capEnv := VarTypeEnv.toCaptured env }
```

Then `resolveSyntaxPred_respectsTagMeaning` is a proved lemma (structural),
and the axiom is:

```lean
axiom externTagMappingRespectsTagMeaning
  (tm : TagMeaning)
  (mapping : ExtTreeMap TagIndex Tag)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag : Tag) (nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag'))
  : TagMappingRespectsTagMeaning tm mapping preds env
```

Advantage: clean separation — the axiom is purely about the tag-to-
descriptor mapping, and the structural resolution reasoning is proved.
The `toPExpr` guard in the definition prevents the axiom from asserting
facts about bodies that fail to convert.

Step 5a will determine which option is cleaner in practice.

#### Step 5a. Validate axiom shape on existing code

**Files:** `LeanProofs/RegimeConsistency.lean`, `LeanProofs/StepFR.lean`
**Verification:** `lake build` — 0 sorry, 0 warnings.  Axiom count
temporarily +1 (new axiom added, old axioms not yet deleted; net reduction
deferred to 5c).
**Highest-risk step** — tests whether the abstraction actually works.

Validate the axiom shape by proving the two easiest corollaries on the
**existing** code (no typechecker change):

1. Define `PredicateRespectsTagMeaning` (RegimeConsistency.lean).
2. Prove lifting lemma: for non-function-type QTyps,
   `QTypRespectsTagMeaning tm qt ↔ PredicateRespectsTagMeaning tm qt.pred`.
3. Choose between Option A and Option B:
   - **Try Option B first** (cleaner layering): define
     `TagMappingRespectsTagMeaning` with the `toPExpr` guard, attempt
     `resolveSyntaxPred_respectsTagMeaning` as a proved **lemma**, state
     `externTagMappingRespectsTagMeaning` as the axiom.
   - **Fall back to Option A** if the structural lemma proof is
     unexpectedly difficult: use `externResolvedPredRespectsTagMeaning`
     as the axiom (scoped to successful resolution).
4. Prove `§2.4` as corollary (simplest — `typecheckExternVal` calls
   `resolveSyntaxPred` once, result is base type → lifting lemma +
   axiom/lemma from sub-step 3).
5. Prove `§2.2` for the `ExternReturn.simple` case of pure extern (no
   effect loop, base-type return).

This is the go/no-go gate for the entire Step 5.  If neither option
produces a working corollary for §2.4, the approach needs redesign.

**What this step does NOT do:** nested-return cases, effect-loop
memEnv reasoning, or any typechecker changes.

#### Step 5b. Typechecker refactoring + proof adjustment

**Files:** `LeanPoison/Typecheck.lean`, then `LeanProofs/` as needed.
**Verification:** `make test` (unit tests), then `lake build` — 0 sorry,
0 warnings, no net axiom increase.

Only proceed here after 5a succeeds.  The goal is to make the impure
effect-loop case provable as a corollary.

**Typechecker change:** extract the effect-loop body into a named helper:

```lean
/-- Resolve one extern effect and write the result to memory at the
    locations referenced by the effect target. -/
def applyExternEffect (effect : Effect) (unifiedEnv : VarTypeEnv)
    (tagMapping : ExtTreeMap TagIndex Tag) (pc : Poison)
    (memEnv : MemoryTypeEnv) : TypecheckM MemoryTypeEnv
```

The effect loop becomes:
```lean
let mut memEnv := result2.memEnv'
for effect in effects do
  memEnv ← applyExternEffect effect unifiedEnv tagMapping ctx.pc memEnv
```

Existing functions keep their signatures; the helper is called internally.
No behavioral change — `make test` must pass.

**Proof adjustment:** fix proofs broken by the changed function body.
This is mechanical — same obligations, different terms after unfolding.
State auxiliary lemmas about the helper as needed (e.g.,
`applyExternEffect_memEnv_subset`, `applyExternEffect_regime_eq`).

**Constraint:** No net increase in `sorry` or `axiom`.

#### Step 5c. Complete axiom unification

**Files:** `LeanProofs/StepFR.lean`, `LeanProofs/RegimeConsistency.lean`,
`LeanProofs/StepFRApp.lean` (as needed).
**Verification:** `lake build` — 0 sorry, 0 warnings.  Axiom count: 2.

Completed:

1. Replaced `§2.1` with structural corollaries:
   - result-QTyp respect via the same return-spec split validated for `§2.2`
   - memEnv-cell respect via an `applyExternEffect` loop invariant
2. Deleted the final old Contract A axiom declaration
   `applyFnTClosure_extern_ok_outputRespectsTagMeaning`.
3. Updated all remaining call sites.
4. Verified `lake build` clean.

#### Risks

- **`tm`-mapping precondition** (step 5a, gate): the central risk is
  whether `TagMappingRespectsTagMeaning` can be derived from
  `wfTagMeaningCtx` or must itself become the axiom.  Step 5a is
  specifically designed to resolve this before any refactoring.
- **Nested extern captures** (resolved in step 5c): the returned nested
  extern closure stores `VarTypeEnv.toCaptured unifiedEnv`, not the ambient
  context's original captured env.  This required extern-specific transfer
  helpers plus the existing `ofCaptured` lookup bridge
  (`list_lookup_of_ofCaptured_lookup`).
- **`toPExpr` in `resolveSyntaxPred`**: the `body.toPExpr` call converts
  `Expr → PExpr`.  The guard descriptor in the resolved predicate contains
  the `PExpr`, which must match what `tm` maps the tag to.  This is part
  of the semantic claim covered by the axiom and feeds into the
  `TagMappingRespectsTagMeaning` definition.
- **Effect loop invariant** (resolved in step 5c): the fold over effects now
  preserves the "all cells respect `tm`" property via per-effect preservation
  and loop composition lemmas built around `applyExternEffect`.
- **Proof churn in step 5b**: if many proofs unfold the extern case,
  repair may be extensive.  Mitigation: keep the helper as a thin wrapper
  so `simp` can unfold it when needed.

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
- **Step 5a (unified axiom validation):** validated Option B on existing
  code.  Added `externTagMappingRespectsTagMeaning`, proved
  `resolveSyntaxPred_respectsTagMeaning`, and derived the `typecheckExternVal`
  and pure-extern-simple corollaries.
- **Step 5b (typechecker refactor):** extracted `applyExternEffect` from the
  impure extern effect loop and repaired the affected `TypeSafety.lean`
  proofs without changing axiom count.
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

### 7.4 Reference points

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
  `applyPFnTClosure_extern_memEnv_eq` (proves pure extern memory identity),
  `applyPFnTClosure_extern_regime_eq`
- `LeanProofs/StepFR.lean`:
  `QTypRespectsTagMeaning_of_arrow_captured_lookup`,
  `QTypRespectsTagMeaning_of_parrow_captured_lookup`,
  `wfTagMeaningCtx_closure_body`,
  `wfTagMeaningCtx_pclosure_body`,
  `typecheckExternVal_QTypRespectsTagMeaning_corollary`
