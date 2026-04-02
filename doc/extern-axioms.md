# Extern Functions: FR Contract Surface on `new-iofree`

## 1. Goal

This note records the extern-related assumptions currently used by the
fault-robustness proof stack on `new-iofree`, separates principled extern
contracts from proof obligations that should be discharged inside Lean, and
outlines the implementation path to eliminate the non-contract axioms and
`sorry`s.

The target is:

- eliminate all `sorry` and all non-contract axioms
- keep only the extern contracts that cannot be derived from the typechecker in
  principle
- do this **without** adding new invariants to `StepFR` or `StepFR_IH`
- keep any new typing invariants **below** the `StepFR` abstraction boundary

More concretely, the intended boundary rule is:

- acceptable: strengthen local `TypeSafety` lemmas, local helper lemmas, or
  intermediate theorem shapes used only below `StepFR`
- unacceptable: add new hypotheses to `StepFR`, `StepFR_IH`,
  `FaultRobustnessSpec`, or the top-level FR theorem interface just to carry a
  local typing invariant

The tactical convention for proof gaps is:

- `sorry` = an obligation we expect to prove
- `axiom` = an obligation we currently believe is unprovable in principle and
  therefore part of the intended contract surface

So, in the current repository state, both `sorry` and `axiom` count as proof
gaps. The distinction is about intended end state, not about severity.

## 2. Scope

Raw extern syntax is operationally unreachable in the current evaluator:

- `Expr.externVal`
- `Expr.externFn`
- `Expr.externPfn`

all produce runtime errors in `LeanPoison/BigStep.lean`.

So the remaining extern proof surface concerns **typing-layer artifacts and the
FR witness maps built for them**, rather than runtime execution:

1. `typecheckExternVal`
2. `applyFnTClosure` on `FnTClosure.extern`
3. `applyPFnTClosure` on `PFnTClosure.extern`

These typing functions:

- resolve syntax-level predicates to fresh concrete tags
- thread captured environments
- allocate fresh tags
- and, for impure externs, update memory through the declared effects

The FR proof must therefore reason about the typing artifacts created by extern
specs, and about how the single-run witness maps realize those artifacts, even
though the runtime never evaluates raw extern expressions.

No eval-side extern contract is currently required. All remaining extern
assumptions on this branch are about the **typing summary layer**, not about
`beval` behavior of actual extern execution.

This note therefore does **not** try to solve:

- executable semantics for externs
- semantic adequacy of extern summaries with respect to future runtime behavior

It only addresses the contracts needed for the current FR proof stack.

## 3. Current State

As of **2026-04-02** on `new-iofree`:

- `lake build` succeeds
- the current proof-gap inventory is:
  - **7 `sorry`** statements in **3 declarations**
  - **11 explicit `axiom`** declarations
    - 10 in `LeanProofs/StepFR.lean`
    - 1 in `LeanProofs/TypeSafety.lean`
- so the branch currently has **18 proof gaps** total
- only a small subset of the 11 axioms should survive as actual axioms; the
  rest should be treated as provisional proof gaps that still need proofs
- the current build warnings point at exactly these declarations:
  - `typecheckExpr_preserves_tagEnvBounded_main`
  - `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
  - `stepFR_ite_standard`
- this is a snapshot of the branch at that date; the counts should be re-checked
  after proof edits
- `assign_final_clean_preservation` is already resolved on the current branch

Build warnings only report the `sorry` declarations. The `axiom` declarations
must therefore be tracked separately in the document.

### 3.1 Current axiom inventory

The `Status` column below uses this convention:

- `Transitional bundle` = currently axiomatized wrapper that is planned to be
  replaced by a smaller contract plus an internal theorem
- `Candidate contract` = plausible permanent extern assumption
- `Provisional proof gap` = currently axiomatized, but intended to become a
  theorem

| Axiom | File | Status |
|------|------|--------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | `StepFR` | Transitional bundle; planned to be split into a small contract plus internal theorem |
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | `StepFR` | Candidate contract |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | `StepFR` | Candidate contract |
| `applyFnTClosure_extern_ok_lookup_origin` | `StepFR` | Provisional proof gap |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | `StepFR` | Provisional proof gap |
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | `StepFR` | Provisional proof gap |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | `StepFR` | Provisional proof gap |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | `StepFR` | Candidate contract |
| `typecheckExternVal_preserves_lookup_origin_axiom` | `StepFR` | Provisional proof gap |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | `StepFR` | Provisional proof gap |
| `applyFnTClosure_extern_wfTypeResult` | `TypeSafety` | Provisional proof gap |

### 3.2 Current `sorry` inventory

| File | Declaration | Count | Assessment |
|------|-------------|-------|------------|
| `TypeSafety.lean` | `typecheckExpr_preserves_tagEnvBounded_main` | 2 | Real proof gap in `ite` mode 1/2; the public theorem `typecheckExpr_preserves_tagEnvBounded` delegates to this `_main` proof |
| `StepFRIte.lean` | `stepFR_ite_standard` | 4 | Current local helper route is likely too strong |
| `StepFRApp.lean` | `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true` | 1 | Current theorem shape is false |

## 4. What Must Be Assumed About Extern Functions For FR

The typechecker can manipulate an extern specification, but it cannot prove
from ordinary typing structure alone that the resolved tags introduced by that
summary have the intended interpretation in `TagMeaning`. That summary-opacity
is the principled source of extern contracts on the current branch.

### 4.1 FR interpretation of resolved return predicates

When an extern spec resolves a syntax predicate to a fresh concrete tag `k`,
FR needs to know that `k` really carries the intended guard interpretation in
`TagMeaning`.

This is the content of:

- `typecheckExternVal_QTypRespectsTagMeaning_axiom`
- `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`
- `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`

These are the clearest examples of axioms that are unavoidable in principle on
the current branch. They state that the resolved guard tag attached to an
extern result has the intended `TagMeaning` interpretation.

### 4.2 FR interpretation of predicates introduced by impure extern effect summaries

Impure externs can write predicates into memory through their declared
`effects` at the **typechecking** level. FR needs to know that those written
predicates are well-interpreted in `TagMeaning`.

This is **not** an eval-side contract about actual runtime extern execution.
Because raw extern syntax does not execute on this branch, FR does not need any
assumption of the form:

- "the runtime writes exactly these cells"
- "the runtime produces exactly these effects"
- "the runtime return value matches the extern spec"

What FR does need is weaker and purely typing-side:

- if extern typing writes a resolved predicate into the post-typing memory
  summary, the introduced tag must be interpretable enough for
  `wfTagMeaningCtx`-style reasoning to continue

Today that FR-side interpretation requirement is bundled together with
structural reasoning in:

- `applyFnTClosure_extern_ok_wfTagMeaningCtx`

Conceptually this mixes two pieces:

1. a **typing-summary interpretation** contract: the resolved effect predicates
   introduced into the post-typing context have the intended `TagMeaning`
2. a **structural** proof obligation: once those interpretation facts are
   assumed, the
   `LocSet.fold ... updateMemEnv` loop preserves `wfTagMeaningCtx`

Only the first part is principled extern opacity for the current FR proof. The
second part should be provable.

### 4.3 Contract floor

After the planned split of the impure-effect bundle, the most defensible
permanent contract surface is:

- definitely the 3 result-side `QTypRespectsTagMeaning` contracts above
- plus the smaller FR-interpretation contract for impure extern effect
  predicates that will remain after splitting the current bundle

So the likely permanent floor is:

- **3 core result-side contracts**
- **plus 1 impure-effect interpretation contract** after splitting the current
  bundle

No parallel `PFnTClosure.extern` effect contract is expected, because the pure
extern path has no effect list and no memory-summary update loop.

## 5. What Should Be Provable Rather Than Assumed

Everything below looks like proof engineering, missing local invariants, or
theorem-shape cleanup, not principled extern opacity.

These are FR / typing theorems about the summary artifacts created by extern
typing, and about the witness maps chosen by the existing single-run FR
theorem. They are not claims about executable extern semantics.

### 5.1 Guard-tag absence / freshness

These should be provable from boundedness of the typing context rather than
axiomatized:

- `applyFnTClosure_extern_ok_guardClosure_tag_absent`
- `applyPFnTClosure_extern_ok_guardClosure_tag_absent`
- `typecheckExternVal_guardClosure_pred_implies_tag_absent`

The branch already contains proved replacements:

- `applyFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded`
- `applyPFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded`
- `typecheckExternVal_guardClosure_pred_implies_tag_absent_of_tagEnvBounded`

The missing bridge is a proof that successful `matchGuard` returns a tag below
`ctx.nextTag` once top-level predicate tags in the context are bounded.

### 5.2 Structural well-formedness for impure extern application

These should become structural consequences of an explicit captured-locset
allocation invariant:

- `applyFnTClosure_extern_wfTypeResult`
- `applyFnTClosure_extern_ok_fresh_loc_not_clean`

The key observation is that `returnSpecToQTyp` rejects reference returns for
extern functions. So impure extern application can only affect memory through
the effects loop. If all captured `ETyp.ref ls` locsets are already allocated
in `result2.memEnv'`, then the effects loop does not introduce fresh keys.

This is one-sided because `PFnTClosure.extern` has no `effects` list. The pure
extern path does not update `memEnv'`, and current structural lemmas such as
`applyPFnTClosure_extern_memEnv_eq`, `applyPFnTClosure_extern_tagEnv_eq`, and
`applyPFnTClosure_extern_regime_eq` already reflect that. So the effect-loop
obligations appear only on the `FnTClosure.extern` side.

### 5.3 Provenance / lookup-origin facts

These should be proved from explicit freshness and type-level effect-loop provenance
facts:

- `typecheckExternVal_preserves_lookup_origin_axiom`
- `applyFnTClosure_extern_ok_lookup_origin`

The extern-value theorem needs a stronger statement than it currently has.
Adding `hpre : ctx.memEnv.contains l` removed one false shape, but the theorem
is still false on arbitrary contexts unless freshness of `ctx.nextLoc` is
assumed. The natural premise is `wfTypeContext ctx`, or an equivalent
fresh-location hypothesis.

The impure-extern application theorem is harder: it needs a precise account of
which effect targets may be written by the typing summary, plus provenance back
to already-originating memory.

## 6. Known Theorem-Shape Issues

These are not merely unfinished proofs. The current statements are too strong.

### 6.1 `StepFRApp`: regular closures may allocate fresh clean extern refs

The theorem

- `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`

is false for the regular-closure case. A concrete counterexample is:

```lean
FnTClosure.regular "x" (Expr.externVal (Typ.ref Typ.int) false SyntaxPredicate.noPred) []
```

applied with `joinPoison p1 p = true`.

What happens:

- the body context has `pc = true`
- `typecheckExternVal` allocates a fresh memory cell `⟨ETyp.int, false, noPred⟩`
- `normalizeAppResultByProvenance` poisons the result `qualType`, but it does
  not poison that fresh memory cell

So the theorem must be restated or split. This is not a proof-search problem.

This is specifically an extern regression relative to `main`: on `main`, the
`ioFree` typing path rejected externs, so FR never had to consider regular
closure bodies that allocate fresh clean memory through `externVal ref int`.

### 6.2 `StepFRIte`: branch-fresh clean extern refs can survive the join

The local helper `hclean_back_to_res1` inside `stepFR_ite_standard` tries to send every
clean final location back to `res1.memEnv'`.

That is too strong in the standard join mode. Both branches may allocate fresh
clean `externVal ref int` cells, and `joinMemEnvsStrong` preserves those
single-sided cells with `noPred`.

So the current helper should be replaced by a case split:

- inherited locations: send them back through
  `typecheckExpr_clean_lookup_origin_of_pc_true`
- branch-fresh extern allocations: prove the FR obligation directly, without
  forcing an origin in `res1`

The four actual `sorry`s are not in the statement of `hclean_back_to_res1`
itself. They occur in the downstream calls to
`typecheckExpr_clean_lookup_origin_of_pc_true` inside the helper. The reason
those calls become unprovable is exactly that the helper route is trying to send
all clean final locations back through `res1`.

Why this is specifically extern-related:

- on `main`, the `ioFree` typing path rejected externs, so FR never had to
  reason about fresh clean cells introduced by extern typing
- before externs mattered on the FR path, fresh branch-local locations came
  mainly from ordinary `newRef`
- under `pc = true`, `newRef` stores a poisoned cell, so those fresh locations
  were not clean
- `externVal ref int` behaves differently: it allocates a fresh memory cell
  `⟨ETyp.int, false, Predicate.noPred⟩`
- the returned reference value may be control-poisoned, but the allocated
  memory cell itself is clean
- `joinMemEnvsStrong` can therefore preserve branch-fresh clean cells that do
  not come from `res1.memEnv'`

So the `stepFR_ite_standard` regression is a direct consequence of allowing extern
typing summaries on the FR path.

### 6.3 The remaining issue-1 fix is not purely typing-local

The obvious local replacement route for issue 1 was:

- classify a clean post-typing logical location as either inherited, or
  branch/body-fresh from `externVal ref int`
- then handle the fresh case by showing it is unrealized on both runs

That idea is still directionally correct, but it cannot be discharged by a
purely typing-local lemma.

Why:

- the existing single-run theorem only gives
  `PreservesInheritedFinalCleanLocsOneRun`
- that relation talks only about clean locations that were already present in
  the input typing context
- it says nothing about fresh clean logical locations introduced by extern
  typing summaries

So the remaining `StepFRApp` / `StepFRIte` work needs a new **internal
single-run sidecar theorem** below `StepFR`, describing how the chosen witness
map `θ'` treats fresh clean extern-ref logical locations.

The generic strengthening

- "every fresh clean output location is unrealized in `θ'`"

cannot be added to the global single-run theorem, because it is false for
`newRef`: `newRef` intentionally creates and realizes a fresh logical location.

So the required next theorem must be:

- internal
- specific to the extern-ref issue
- and kept below `StepFR`, `StepFR_IH`, and the top-level FR interface

### 6.4 `typecheckExternVal_preserves_lookup_origin_axiom` still needs a freshness premise

If `ctx.nextLoc` already collides with an existing memory key, then
`externVal ref int` can overwrite that pre-existing key with a fresh clean
cell. So the current statement is still false on arbitrary ill-formed contexts.

This should be fixed by strengthening the theorem shape, not by adding more
case-by-case proof plumbing downstream.

### 6.5 `matchGuard` boundedness is about extern-allocated tags

The remaining `matchGuard` proof gap is also extern-related, but through fresh
tags rather than fresh locations.

`matchGuard` does not invent tags. It only returns a tag already present in a
predicate stored in:

- `ctx.varEnv`, or
- `ctx.memEnv`

This is specifically an extern regression relative to `main`: on `main`, the
`ioFree` typing path rejected externs, so FR never had to reason about fresh
concrete tags allocated from extern syntax predicates.

The fresh tags appearing in those predicates come from the extern typing
pipeline:

```lean
collectAndAllocExternTags
  -> resolveSyntaxPred
  -> typecheckExternVal / applyFnTClosure extern / applyPFnTClosure extern
```

So the real missing fact is:

- if a predicate tag currently appears in `ctx.varEnv` or `ctx.memEnv`, and
  that tag originated from extern allocation, then it is still below
  `ctx.nextTag`

This is exactly what is needed to finish the `tagEnvBounded` route:

- the proved `*_of_tagEnvBounded` lemmas show that tags `>= nextTag` are absent
  from `tagEnv`
- `matchGuard` returns a tag extracted from predicates in `varEnv` / `memEnv`
- therefore we need a bridge from "returned by `matchGuard`" to
  "`< ctx.nextTag`"

That bridge became necessary only because extern typing now allocates fresh
concrete tags on the FR path.

The old `iofree` branch phrased a related result against `ctx.regime.bound`.
The current branch instead needs a `< ctx.nextTag` bound, because the active
proof route is based on:

- `collectAndAllocExternTags_mapping_values_ge`
- `tagEnvBounded_get_none_of_ge`

Both are stated in terms of the fresh-tag supply `nextTag`. The current branch
does not carry the old `regime.bound`-based interface.

## 7. Implementation Constraints

### 7.1 Boundary rule: no invariant leakage into FR

The last failed direction on this branch was to make a useful local typing
invariant available by threading it through FR-facing helper interfaces. That
should not be repeated. The relevant rollback is commit `f43c3b8`
("removed invariant leak to FR").

For this document, the operative rule is:

- local typing invariants may be introduced and proved inside `TypeSafety.lean`
- they may be consumed by local helper lemmas in files such as
  `StepFRAssign.lean`
- they must **not** become part of:
  - `StepFR`
  - `StepFR_IH`
  - `FaultRobustnessSpec`
  - the statement of the top-level FR theorem

So, for example, `tagEnvBounded` is acceptable as:

- a premise to a proved replacement lemma such as
  `*_of_tagEnvBounded`
- a local hypothesis in a helper below `StepFR`

but not as:

- a new field in the main FR abstraction
- a new hypothesis threaded through the step theorem interface

Every proposed invariant should therefore be classified before implementation:

1. Is it purely typechecker-local?
2. Can it be derived on demand from existing typing results?
3. Can it be consumed entirely below `StepFR`?

If the answer to (3) is "no", the plan should be rejected or restated.

The same rule applies to single-run helper theorems:

- strengthening the global single-run theorem interface is not acceptable
- adding a new sidecar single-run theorem below `StepFR` is acceptable

## 8. Plan

High-risk-first is the intended order.

### 8.1 Phase 1. Repair theorem shapes first

Before investing in more plumbing, repair the statements that are currently too
strong:

1. restate or split `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
2. replace the `stepFR_ite_standard` back-to-`res1` route with an
   inherited/fresh split
3. add an internal single-run sidecar theorem for the fresh extern-ref case:
   fresh clean logical locations introduced by extern typing summaries are
   handled by the chosen witness map `θ'` without changing the `StepFR`
   interface
4. strengthen `typecheckExternVal_preserves_lookup_origin_axiom` with
   `wfTypeContext ctx` or an equivalent freshness premise

This is the highest-risk work because it can invalidate later proof plans if
left unresolved.

### 8.2 Phase 2. Finish the `tagEnvBounded` path without touching `StepFR`

The intended route is:

1. prove a `matchGuard`-bound bridge usable from `TypeSafety.lean`
2. add a local predicate-tag-bounded invariant at the typechecker level, with
   shape
   `((∀ x qt k, ctx.varEnv.lookup x = some qt → qtypGuardTag qt = some k → k < ctx.nextTag) ∧
     (∀ l qt k, ctx.memEnv.lookup l = some qt → qtypGuardTag qt = some k → k < ctx.nextTag))`
   and keep it entirely below `StepFR`
3. finish the two `ite` mode 1/2 `sorry`s in
   `typecheckExpr_preserves_tagEnvBounded_main`, thereby completing the public
   theorem `typecheckExpr_preserves_tagEnvBounded`
4. thread `tagEnvBounded` only through local helper lemmas such as:
   - `ioFree_guardClosure_pred_implies_tag_absent`
   - `typecheckApp_arrow_branch_guardClosure_pred_implies_tag_absent`
   - `typecheckApp_parrow_branch_guardClosure_pred_implies_tag_absent`
5. replace the three guard-tag-absence axioms with the existing proved
   alternatives:
   - `applyFnTClosure_extern_ok_guardClosure_tag_absent`
   - `applyPFnTClosure_extern_ok_guardClosure_tag_absent`
   - `typecheckExternVal_guardClosure_pred_implies_tag_absent`

This stays within the user constraint: no new `StepFR` invariant.

Phase dependencies inside this phase are:

- 8.2.1 + 8.2.2 → 8.2.3
- 8.2.3 → 8.2.4
- 8.2.4 → 8.2.5

### 8.3 Phase 3. Make the captured-locset allocation invariant explicit

For impure externs, the key missing invariant is:

- every location in a captured `ETyp.ref ls` is already present in
  `result2.memEnv'`

Once this is formalized, it should unlock:

- `applyFnTClosure_extern_wfTypeResult`
- vacuity of `applyFnTClosure_extern_ok_fresh_loc_not_clean`
- a cleaner proof path for `applyFnTClosure_extern_ok_lookup_origin`

Do not confuse the extern-only axiom
`applyFnTClosure_extern_ok_fresh_loc_not_clean` with the broader
`StepFRApp` theorem-shape issue
`applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`. The former is an
extern-only typing-summary obligation; the latter is a current false statement
about all closure applications.

### 8.4 Phase 4. Split the impure-effect extern bundle

The current bundled axiom

- `applyFnTClosure_extern_ok_wfTagMeaningCtx`

should be split as planned into:

1. FR-interpretation assumptions for effect predicates
2. structural fold/update lemmas proving preservation of `wfTagMeaningCtx`

This split is intended to be **internal** to the extern helper layer:

- `StepFR`
- `StepFR_IH`
- `FaultRobustnessSpec`
- the top-level FR theorem interface

should remain unchanged. In other words, the split should live in lemmas below
these interfaces, not in the interfaces themselves.

The old shape of `applyFnTClosure_extern_ok_wfTagMeaningCtx` should then be
recovered as a proved wrapper lemma from the smaller ingredients. That leaves
the long-term extern contract surface closer to the true FR contract minimum
without repeating the invariant-leak error.

## 9. Useful References

These `iofree` references are useful as proof templates, but the current branch
should reuse only the specific lemma shapes it needs:

These names exist only on the `iofree` branch; they will not appear in a grep
of the current `new-iofree` checkout.

- `iofree:LeanProofs/StepFRIte.lean`
  - `matchGuard_tag_in_bound`
- `iofree:LeanProofs/StepFR.lean`
  - `predTagsBoundedInCtx`
- `iofree:LeanProofs/TypeSafety.lean`
  - `collectAndAllocExternTags_nextTag_ge`
  - `typecheckExternVal_nextTag_mono`

The old `predTagsBoundedInCtx` route was explicitly deleted on this branch in
commit `2062907`. Phase 8.2 uses a different route: a local predicate-tag bound
relative to `ctx.nextTag`, combined with `tagEnvBounded`.

Current-branch helpers already available:

- `LeanProofs/RegimeConsistency.lean`
  - `EnvRespectsTagMeaning_updateMemEnv`
  - `EnvRespectsTagMeaning_list_fold_updateMemEnv`
  - `QTypRespectsTagMeaning_fn_extern`
  - `QTypRespectsTagMeaning_pfn_extern`
