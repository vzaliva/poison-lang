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

As of **2026-04-06** at commit `a062e59` on `new-iofree`:

- the worktree is clean
- `make lean-build` succeeds
- the current warnings are:
  - **7 `declaration uses 'sorry'` warnings** in `LeanProofs/TypeSafety.lean`
  - several low-value linter warnings (`unusedSimpArgs`, `unusedTactic`,
    `unreachableTactic`, `unnecessarySeqFocus`) in `LeanProofs/TypeSafety.lean`
- the current proof-gap inventory is:
  - **33 explicit `sorry` terms** in **7 declarations**
    - all are in `LeanProofs/TypeSafety.lean`
  - **11 explicit `axiom`** declarations
    - 10 in `LeanProofs/StepFR.lean`
    - 1 in `LeanProofs/TypeSafety.lean`
- the branch therefore has **44 explicit proof gaps** by raw count
- the raw `sorry` count now **overstates** the number of conceptual blockers:
  many of those terms are repeated inline placeholders for
  `closureEnvBoundedInCtx` inside one theorem, plus two temporary wrapper
  defaults
- only a small subset of the 11 axioms should survive as actual axioms; the
  rest should be treated as provisional proof gaps that still need proofs
- the section 6.3 work remains complete on the branch: the strengthened
  single-run infrastructure is in place, `StepFR` / `StepFR_IH` are unchanged,
  and the old local 6.3 blockers are resolved
- the current active proof work is still concentrated in **Phase 8.5** local
  `TypeSafety.lean` plumbing
- the recent growth in local invariants is explained by a real application-side
  gap: boundedness of the **current** typing context does not by itself imply
  boundedness of **captured** environments nested inside function-valued result
  types
- that new invariant family remains entirely below `StepFR` and has not leaked
  into `StepFR`, `StepFR_IH`, or the top-level FR theorem interface

**Phase 8.5 progress (2026-04-06, `a062e59`)**:

- Step 1 (current-context definitions): **done** —
  `predTagBounded`, `qtypPredTagBounded`, `predTagsBoundedInVarEnv`,
  `predTagsBoundedInMemEnv`, `predTagsBoundedInCtx`
- Step 2 (current-context helpers): **mostly done** — monotonicity,
  `tagEnvBounded_insert_of_lt`, `predTagsBoundedInVarEnv_update`,
  `predTagsBoundedInMemEnv_update`, `predTagBounded_joinPredicates`,
  `predTagsBoundedInMemEnv_joinMemEnvsStrong`, `typecheckIf_pred_noPred`,
  `mergeFnTClosures_mem`, `mergePFnTClosures_mem`, and the `joinETyps`
  closure-merge helper are proved; the remaining local helper work is
  `updateLocsetWeak` plus a small deref structure lemma
- Step 3 (matchGuard bridge): **done** — `matchGuard_tag_bounded` is proved in
  `TypeSafety.lean`
- Step 4 (new local closure-captured boundedness subphase): **in progress** —
  the branch now defines:
  - `capturedPredTagsBounded`
  - `etypClosuresCapturedPredTagsBounded`
  - `varEnvClosuresCapturedBounded`
  - `closureEnvBoundedInCtx`
  together with monotonicity / update / `toCaptured` / `ofCaptured` bridge
  lemmas; this is the local fix for the real mismatch that closure bodies are
  typed under `VarTypeEnv.ofCaptured env`, not under the caller's `ctx.varEnv`
- Step 5 (predicate-tag preservation theorem): **in progress** —
  `typecheckExpr_preserves_predTagsBounded_main` now carries
  `closureEnvBoundedInCtx ctx`; literals, vars, unary/binops, seq, vlet,
  newRef, `externVal`, and all `ite` modes are structurally understood, but the
  declaration still contains the remaining local holes for:
  - `assign`
  - `deref`
  - `app`
  - extern closure helper cases
  - repeated inline `closureEnvBoundedInCtx` derivations
- Step 6 (closure theorem): **in progress** —
  `typecheckExpr_preserves_closureCapturedBounded` is proved for all non-`app`
  cases; the `app` case is the current high-risk local blocker because it must
  feed the captured-env hypotheses required by the closure-application helper
  lemmas
- Step 7 (tagEnv integration): **in progress** —
  `typecheckExpr_preserves_tagEnvBounded_main` is reduced to the `app`
  helper/app case; the old `vlet` and `ite` local holes are gone

Build warnings report only the declarations containing `sorry`, not the raw
number of `sorry` terms. So the current build shows **7** declarations using
`sorry`, while the raw token count in `TypeSafety.lean` is **33** explicit
`sorry` terms.

The `axiom` declarations must therefore be tracked separately in the document.

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
| `TypeSafety.lean` | `predTagsBoundedInMemEnv_updateLocsetWeak` | 1 | Routine fold/update lemma for weak locset writes |
| `TypeSafety.lean` | `applyFnTClosure_predTagsBounded` | 1 | Remaining extern closure case |
| `TypeSafety.lean` | `applyPFnTClosure_predTagsBounded` | 1 | Remaining extern pure closure case |
| `TypeSafety.lean` | `typecheckExpr_preserves_predTagsBounded_main` | 25 | Dominant cluster: assign/deref/app plus repeated inline `closureEnvBoundedInCtx` placeholders |
| `TypeSafety.lean` | `typecheckDeref_etyp_int` | 1 | Small local structure lemma; no conceptual risk |
| `TypeSafety.lean` | `typecheckExpr_preserves_closureCapturedBounded` | 1 | `app` case; current high-risk local blocker |
| `TypeSafety.lean` | `typecheckExpr_preserves_tagEnvBounded_main` | 1 | Final app helper/app case after the predTags theorem stabilizes |

Two wrappers in `TypeSafety.lean` also still carry temporary default arguments
of the form `:= by exact sorry`; these inflate the raw count but are not
separate conceptual blockers.

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

That bridge is now proved in `TypeSafety.lean` as `matchGuard_tag_bounded`.
The remaining work is downstream: finish the local predicate-tag preservation
plumbing so the three `_of_tagEnvBounded` lemmas can replace the corresponding
axioms in `StepFR.lean`.

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

So the remaining `StepFRApp` / `StepFRIte` work needs a strengthened
**internal single-run theorem package** below `StepFR`, describing how the
chosen witness map `θ'` treats fresh clean extern-ref logical locations.

The concrete unresolved corner is narrower than section 6.2 by itself might
suggest:

- `StepFRApp`, arrow case, `p1 = true`, with different selected regular-closure
  bodies on the two runs
- `StepFRIte` standard mode, when the two runs take different branches

What these sites have in common is:

- there is no shared executed subexpression on which the two-run FR IH can be
  applied
- the proof therefore falls back to **one-run** witness theorems on each side
- the current one-run package only exports
  `PreservesInheritedFinalCleanLocsOneRun`

That is enough for inherited locations, but not for locations that appear in
the final typing result only because typing joined in non-executed
alternatives.

Two different "fresh" cases must be kept separate:

1. a location is absent from the actually executed member/branch result
2. a location is present in that executed result's `memEnv'`, but only because
   the executed expression itself contains a nested `app` / `ite` whose typing
   joined in non-executed extern summaries

Case 1 is already under control:

- `theta_not_contains_if_not_in_memEnv` applies directly once the selected
  result context is known
- the shared-body `StepFRApp` proof already uses exactly this
  source-or-unrealized transport pattern via
  `join_transport_agreeOnClean_from_member`

Case 2 is the real blocker for issue 1:

- absence lemmas do not apply, because the typing-only location is already in
  the executed result's `memEnv'`
- `runtimeInstantiatesCtx (ctxAfter ctx res) ... θ'` does not force such a
  location either to be realized or to stay unrealized
- `wfExtendsMap` constrains only old mappings
- `PreservesInheritedFinalCleanLocsOneRun` constrains only locations already in
  the input context

So the missing ingredient is specifically a theorem about the **chosen witness
construction**, not just about the final package of facts it satisfies.

This also explains why the pure-function case is not the right template:

- the `PFnTClosure` different-body branch already closes the fresh case by
  contradiction using `applyPFnTClosure_mem_subset`
- pure bodies cannot grow `memEnv'`
- the remaining issue is therefore specific to the effectful arrow path, where
  typing joins can add fresh locations even when the runtime path that produced
  `θ'` never realizes them

Re-evaluating the interface choice, the more realistic route is now:

- strengthen the **global single-run theorem family**
  (`StepFRSingleRunFinalCleanPcTrue`,
  `StepFRSingleRunFinalCleanPcTrueParam`,
  `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`)
- keep `StepFR` itself unchanged unless that stronger single-run proof later
  reveals a genuinely missing input invariant

Why the earlier "parallel theorem family used only by app/ite" idea is likely
the wrong abstraction:

- the stronger fact must compose through syntax such as `seq`, `vlet`, and
  nested `app` / `ite`, not just be available at the outermost repair sites
- composition of the fresh case depends on a mix of:
  - the stronger fresh-clean postcondition from earlier subexpressions
  - the existing `PreservesInheritedFinalCleanLocsOneRun` relation on later
    subexpressions
- so in practice the stronger invariant has to be threaded through the
  single-run induction stack anyway

The code structure supports that route:

- `TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree` is proved
  by a separate masked single-run induction, not extracted from `StepFR`
- `stepFR_app` and `stepFR_ite` receive
  `StepFRSingleRunFinalCleanPcTrue_IH` directly, independently of `StepFR_IH`
- representative composition proofs such as `StepFRSeq` and `StepFRVlet`
  already show the right shape: inherited-clean preservation composes across
  subexpressions, so a fresh-clean-unrealized postcondition can piggyback on
  that same structure

The key composition bridge is already present in the existing infrastructure:

- `PreservesInheritedCleanLocOneRun.both_unrealized` propagates
  `θ.lookup l = none` through a later evaluation step
- so once a stronger single-run theorem shows that a fresh clean location is
  unrealized after an earlier subexpression, the existing inherited-clean
  preservation relation can carry that unrealized status forward through later
  subexpressions that inherit the location

The plausible strengthened postcondition is unary and local to one run:

- if `l` is absent from the input typing context
- and the final output typing result contains a clean `qt` at `l`
- then the chosen witness map satisfies `θ'.lookup l = none`

At the FR use sites this is exactly the shape we want, because the fresh branch
of `agreeLocUnder` only needs:

- `θ₀'.lookup l = none`
- `θ₁'.lookup l = none`

not any stronger cross-run memory relation.

Current assessment about whether `StepFR` itself must change:

- there is currently no concrete reason to change `StepFR`
- strengthening the single-run theorem family appears sufficient if the new
  invariant is added as an extra **postcondition**, with no new input
  hypotheses
- `StepFR` should be reconsidered only if, during the strengthened single-run
  proof, we discover that some operator case needs an additional **input**
  invariant that is not derivable from the current single-run hypotheses
  (`wfTypeContext`, `runtimeInstantiatesCtx`, regime consistency, and `pc=true`)

The generic strengthening

- "every fresh clean output location is unrealized in `θ'`"

still needs bounded falsification before committing to it as the new
single-run theorem shape. The obvious quick checks are:

- `newRef` under `pc = true`
- nested `ite`
- nested `app`

If that candidate fails even in the pc-true setting, then the strengthened
single-run postcondition must be
phrased in a more provenance-sensitive way instead of as a blanket fresh-clean
statement. But the first place to repair it should still be the single-run
theorem family, not `StepFR`.

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

This extern-related fresh-tag bridge is now proved in `TypeSafety.lean` as
`matchGuard_tag_bounded`. The remaining work is to thread that proved bridge
through the local `tagEnvBounded` helper path and then switch the three
guard-tag-absence axioms in `StepFR.lean` over to their proved
`_of_tagEnvBounded` replacements.

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

The key fact is:

- if a predicate tag currently appears in `ctx.varEnv` or `ctx.memEnv`, and
  that tag originated from extern allocation, then it is still below
  `ctx.nextTag`

This is exactly what the `tagEnvBounded` route needs:

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

- strengthening the global single-run theorem family is acceptable
  (`StepFRSingleRunFinalCleanPcTrue`,
  `StepFRSingleRunFinalCleanPcTrueParam`,
  `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`)
- extending `StepFR` itself is not acceptable unless the strengthened
  single-run proof reveals a genuinely missing input invariant that cannot be
  recovered below `StepFR`

## 8. Plan

High-risk-first is the intended order.

Status of section 6.3 implementation: **complete**.

- `FreshCleanLocsUnrealizedOneRun` added as the 7th conjunct to the single-run
  theorem family (`StepFRSingleRunFinalCleanPcTrue*`)
- proved for all 13 expression cases (literal, var, op, unaryop, fn, pfn,
  deref, assign, newRef, seq, vlet, app, ite) including the induction
  dispatcher in `FaultRobustnessProofs.lean`
- the false lemma `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true` has been
  deleted; its call sites replaced with `agreeLocUnder.both_unrealized`
- the broken `hclean_back_to_res1` in `stepFR_ite_standard` has been deleted;
  consumption sites replaced with inherited/fresh case splits
- `StepFR`, `StepFR_IH`, and `FaultRobustnessSpec` unchanged
- current sorry count: **10 explicit `sorry` terms** in **2 declarations**
  (`typecheckExpr_preserves_predTagsBounded_main` and
  `typecheckExpr_preserves_tagEnvBounded_main` in `TypeSafety.lean`), all local
  to Phase 8.5 and unrelated to section 6.3

### 8.1 Phase 1. Validate the strengthened single-run postcondition

Before changing interfaces, validate the candidate extra postcondition for the
global single-run theorem family:

1. define a standalone unary property expressing:
   - `l` absent from input `ctx.memEnv`
   - `l` clean in the final output typing result
   - `θ'.lookup l = none`
2. test the blanket pc-true candidate against:
   - `newRef`
   - nested `ite`
   - nested `app`
3. check one representative composition proof (`seq` is the best first target)
   to confirm that the new postcondition composes using:
   - the stronger single-run fact on the left
   - `PreservesInheritedFinalCleanLocsOneRun` on the right
   - explicitly test the `both_unrealized` propagation path where `e1`
     introduces the location and `e2` merely inherits it
4. if the proof attempt demands a **new input precondition** rather than just a
   new postcondition, stop and reassess whether `StepFR` itself must be
   extended
5. otherwise freeze the strengthened single-run theorem shape and proceed

This is the highest-risk work because it can invalidate later proof plans if
left unresolved.

### 8.2 Phase 2. Strengthen the global single-run theorem family

Once the theorem shape is validated:

1. strengthen the output package of:
   - `StepFRSingleRunFinalCleanPcTrue`
   - `StepFRSingleRunFinalCleanPcTrueParam`
   - `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`
2. update the corresponding IH abbreviations and masked/unmasked bridges in
   `FaultRobustnessProofs.lean`
3. keep the change purely as an extra **postcondition**
4. do **not** change:
   - `StepFR`
   - `StepFR_IH`
   - `FaultRobustnessSpec`
   - the top-level FR theorem interface

This is an internal proof-interface change below `StepFR`, not an FR theorem
change.

### 8.3 Phase 3. Thread the stronger single-run invariant through syntax

This is the broad but mostly routine phase. The strengthened single-run theorem
must be carried through all operators that participate in the single-run
induction, not just `app` and `ite`.

Expected touch points include:

- `FaultRobustnessProofs.lean`
- `StepFRSeq.lean`
- `StepFRVlet.lean`
- `StepFRNewRef.lean`
- `StepFRAssign.lean`
- `StepFRDeref.lean`
- `StepFRApp.lean`

Representative proof shapes:

1. literals / closures: immediate or vacuous
2. `newRef`: fresh allocated cell is not clean under `pc = true`
3. sequential composition (`seq`, `vlet`, `assign`-style pipelines):
   combine:
   - stronger fresh-clean postcondition from the first subexpression
   - inherited-clean preservation for the second
   - in particular, use `PreservesInheritedCleanLocOneRun.both_unrealized` to
     propagate `θ.lookup l = none` when the later subexpression only inherits
     the location
4. `app` / `ite`: the high-risk cases, but now handled through the same
   strengthened single-run API rather than an app/ite-specific auxiliary route

### 8.4 Phase 4. Repair the current false / over-strong local routes

Once the stronger single-run infrastructure is in place:

1. restate or delete the false theorem
   `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
2. rewrite the arrow/different-body `StepFRApp` fresh-location case to use:
   - inherited locations: existing `PreservesInheritedFinalCleanLocsOneRun`
   - fresh clean locations: the strengthened single-run theorem giving
     `θ.lookup l = none`
3. rewrite `stepFR_ite_standard` to replace `hclean_back_to_res1` with an
   inherited/fresh split
4. use the existing shared-body / source-or-unrealized transport pattern as the
   implementation template where possible, rather than inventing a second join
   framework

### 8.5 Phase 5. Finish the `tagEnvBounded` path without touching `StepFR`

Status: **in progress** (2026-04-06, `a062e59`). The `matchGuard` bridge is
proved, the `ite` mode 1/2 `tagEnvBounded` proofs are real, and the active
front is still local `TypeSafety.lean` plumbing. The one important update to
the original plan is that the `app` case revealed a genuine missing local fact:
`predTagsBoundedInCtx` bounds the **current** typing context, but closure
application types bodies under `VarTypeEnv.ofCaptured env`, so the proof also
needs boundedness for closure-captured environments nested inside function
types. This has been addressed by introducing a second local invariant family
entirely below `StepFR`. No changes to `StepFR`, `StepFR_IH`, or
`FaultRobustnessSpec`.

The implemented route is:

1. **done** — `matchGuard_tag_bounded` is proved in `TypeSafety.lean`
2. **done** — `predTagsBoundedInCtx` defined with `predTagsBoundedInVarEnv` and
   `predTagsBoundedInMemEnv` components; helper lemmas (mono, insert, update,
   joinPredicates) proved; `predTagsBoundedInMemEnv_joinMemEnvsStrong` and
   `typecheckIf_pred_noPred` are also now proved; kept entirely below `StepFR`
3. **done** — closure-captured boundedness definitions and bridges are in place:
   - `capturedPredTagsBounded`
   - `etypClosuresCapturedPredTagsBounded`
   - `varEnvClosuresCapturedBounded`
   - `closureEnvBoundedInCtx`
   together with local monotonicity/update/`toCaptured`/`ofCaptured` lemmas
4. **in progress** — `typecheckExpr_preserves_closureCapturedBounded` is proved
   for all non-`app` cases; the `app` case is now the main local blocker
5. **in progress** — `typecheckExpr_preserves_predTagsBounded_main` now carries
   `closureEnvBoundedInCtx ctx`; the remaining local holes are:
   - `assign`
   - `deref`
   - `app`
   - extern closure helper cases
   - repeated inline `closureEnvBoundedInCtx` derivations that should collapse
     once the closure theorem is finished
6. **in progress** — `typecheckExpr_preserves_tagEnvBounded_main` is reduced to
   the `app` helper/app case. The earlier `vlet` and `ite` local holes are
   resolved.
7. still to do — thread `tagEnvBounded` only through local helper lemmas such
   as:
   - `ioFree_guardClosure_pred_implies_tag_absent`
   - `typecheckApp_arrow_branch_guardClosure_pred_implies_tag_absent`
   - `typecheckApp_parrow_branch_guardClosure_pred_implies_tag_absent`
8. still to do — replace the three guard-tag-absence axioms with the existing
   proved alternatives:
   - `applyFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded`
   - `applyPFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded`
   - `typecheckExternVal_guardClosure_pred_implies_tag_absent_of_tagEnvBounded`

This stays within the user constraint: no new `StepFR` invariant.

Phase dependencies inside this phase are now:

- bullets 1-2 are done and unlocked the original current-context predicate route
- bullet 3 was added after the `app` case exposed the captured-env gap; it stays
  entirely below `StepFR`
- finish bullet 4 → discharge most of the inline `closureEnvBoundedInCtx`
  placeholders in bullet 5
- finish bullet 5 → bullet 6
- finish bullet 6 → bullets 7-8

### 8.6 Phase 6. Make the captured-locset allocation invariant explicit

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

### 8.7 Phase 7. Split the impure-effect extern bundle

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

## 9. History

### 9.1 Rejected local-only repair

An earlier direction was to keep strengthening the local
`typecheckExpr_clean_lookup_origin_of_pc_true` calls by threading more
`contains` facts into the current helpers.

That route is insufficient:

- it only repairs the inherited-location case
- it does not address locations that are present in the final typing result only
  because non-executed extern summaries were joined in
- it therefore cannot solve the remaining arrow/different-body app case

### 9.2 Design pivot: do not isolate the new fact to app/ite only

An earlier revision of this note preferred a "parallel theorem family" consumed
only by `StepFRApp` and `StepFRIte`.

After re-checking the induction structure, that is no longer the recommended
route:

- the stronger fact must compose through intermediate syntax such as `seq` and
  `vlet`
- the single-run theorem family is already proved by a separate induction stack
- `stepFR_app` and `stepFR_ite` already consume that single-run IH directly

So the more coherent design is to strengthen the **global single-run theorem
family** and keep `StepFR` unchanged unless a new input precondition later
proves unavoidable.

### 9.3 Current implementation status of the 6.3 repair

The current branch has now implemented the 6.3 repair completely:

- `FreshCleanLocsUnrealizedOneRun` has been added to the single-run theorem
  package in `StepFR.lean`
- the strengthened postcondition has been threaded through the low-risk
  constructor families (`var`, `op`, `deref`, `seq`, `vlet`, `newRef`,
  `assign`)
- `StepFRApp.lean` and `StepFRIte.lean` now use the strengthened single-run
  invariant at the fresh-location sites
- the false theorem
  `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true`
  has been removed from the active proof path
- there are no remaining `sorry`s in the single-run repair stack

So section 6.3 is no longer an active source of proof-shape uncertainty. The
remaining work has moved back to local typing infrastructure in
`TypeSafety.lean`.

### 9.4 Why the shared-body transport works

The shared-body `StepFRApp` path already has the right high-level shape:

- transport agreement from one selected member result
- for locations missing from that selected result, prove both witness maps omit
  them

So the join transport itself is not the blocker. The blocker is only the lack
of a corresponding omission theorem for the different-body / mixed-branch
one-run setting.

### 9.5 Design note: the new closure invariant is justified

The recent growth in local invariants inside `TypeSafety.lean` is not a sign
that the branch is fighting the wrong high-level strategy. It comes from one
specific real gap:

- `predTagsBoundedInCtx` constrains the **current** typing context
- but `applyFnTClosure` and `applyPFnTClosure` type regular bodies under
  `VarTypeEnv.ofCaptured env`
- so the `app` proof needs boundedness of **captured** environments nested
  inside function-valued result types, not just boundedness of the caller's
  `ctx.varEnv`

That is why the branch introduced the local family:

- `capturedPredTagsBounded`
- `etypClosuresCapturedPredTagsBounded`
- `varEnvClosuresCapturedBounded`
- `closureEnvBoundedInCtx`

Current assessment of this move:

- it is a real typing-local repair, not an arbitrary invariant leak
- it stays entirely below `StepFR`
- it does **not** currently require any new `StepFR` or FR-theorem hypotheses
- it is the correct local fix unless a second, unrelated invariant family is
  later needed

That last point is the main strategic watch item going forward. If more new
invariant families appear after closure-captured boundedness is finished, the
approach should be re-evaluated. At present, there is no evidence that this is
necessary.

### 9.6 Why `PFnTClosure` is not the hard case

The pure-function different-body branch closes the fresh-location case by
contradiction because pure bodies do not grow `memEnv'`.

That is useful as a sanity check, but it is not a template for the remaining
problem. The unresolved issue is specific to effectful arrow bodies.

## 10. Useful References

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
commit `2062907`. Phase 8.5 uses a different route: a local predicate-tag bound
relative to `ctx.nextTag`, combined with `tagEnvBounded`.

Current-branch helpers already available:

- `LeanProofs/RegimeConsistency.lean`
  - `EnvRespectsTagMeaning_updateMemEnv`
  - `EnvRespectsTagMeaning_list_fold_updateMemEnv`
  - `QTypRespectsTagMeaning_fn_extern`
  - `QTypRespectsTagMeaning_pfn_extern`

### 9.7 Future refactoring: extract shared matchGuard analysis module

The `matchGuard_tag_bounded` proof in `TypeSafety.lean` duplicates ~200 lines of
fold analysis that already exists as ~600 lines in `StepFRIte.lean`
(`matchGuard_varMatches`, `matchGuard_refMatches`, `var_match_from_varMatches`,
`ref_match_from_refMatches`, `matchGuard_ok_extract_owner_in_ctx`, etc.).

The duplication exists because:

- `matchGuard_ok_extract_owner_in_ctx` is `private` in `StepFRIte.lean`
- the import direction is `TypeSafety ← StepFR ← StepFRIte`, so `TypeSafety`
  cannot import anything from `StepFRIte`

**Proposed cleanup**: extract the matchGuard analysis lemmas into a shared module
`LeanProofs/MatchGuardAnalysis.lean` that both `TypeSafety.lean` and
`StepFRIte.lean` import. The extracted lemmas only depend on
`LeanPoison.Typecheck` and `Std.ExtTreeMap` — no dependency on `StepFR` types.

This would:

1. eliminate the ~200 lines of duplicated fold analysis in `TypeSafety.lean`
   (`foldl_tags_bounded`, `foldlM_tags_bounded`, `predMergeFold_bounded`, the
   varMatches/refMatches fold proofs, and the
   `LocSet.foldM_Except_preserves_property` application)
2. make `matchGuard_ok_extract_owner_in_ctx` available to `TypeSafety.lean`
3. simplify `matchGuard_tag_bounded` to a ~10-line proof:
   - call `matchGuard_ok_extract_owner_in_ctx` to get the var/ref disjunction
   - for the var case: `predTagsBoundedInVarEnv` gives the bound
   - for the ref case: `predTagsBoundedInMemEnv` gives the bound
4. the existing `StepFRIte.lean` code would re-import from the shared module
   with no proof changes

The shared module sits alongside `TypeSafety.lean` in the import graph (both
below `StepFR`). No changes to `StepFR`, `StepFR_IH`, or `FaultRobustnessSpec`
are needed.
