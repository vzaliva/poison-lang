# Extern Functions: FR Contract Surface on `new-iofree`

**Current status (2026-04-08, branch `new-iofree`, commit `f6b3c7f`)**

- worktree clean
- `lake build` succeeds
- the branch still has the same **6 explicit `sorry` terms** in **3 declarations**
  and **10 explicit `axiom` declarations** in `StepFR.lean`
- the active blocker is providing
  `capturedEnvRefLocsBounded` / `etypRefLocsBounded` at the extern-closure
  `wfTypeResult` call sites
- the proposed solution is to strengthen `wfTypeContext` from a shallow
  memEnv-only bound to a **deep nextLoc-boundedness property** that also covers
  ref locations mentioned inside `varEnv` entries and recursively inside
  captured closures
- the recommended next move is to prove the ref-location typing induction
  first, then atomically switch `wfTypeContext` to that deeper property and fix
  the callers
- this requires one explicit design decision: allow a semantic strengthening of
  `wfTypeContext` as the single justified exception to the "keep new invariants
  below `StepFR`" rule

## 1. Problem

This note tracks the remaining extern-related proof gaps on `new-iofree`,
separates principled extern contracts from obligations that should be proved in
Lean, and records the implementation plan for removing the non-contract gaps.

The end-state goal is:

- eliminate all `sorry`
- eliminate all non-contract `axiom`
- keep only the extern contracts that are unavoidable in principle
- avoid adding new standalone hypotheses to `StepFR`, `StepFR_IH`,
  `FaultRobustnessSpec`, or the top-level FR theorem interface unless a real
  proof obstruction forces that change

The immediate blocker is the last **6 `sorry` terms**, all of the same shape:

1. `capturedEnvRefLocsBounded capturedEnv result.nextLoc'`
2. `etypRefLocsBounded argEtyp result.nextLoc'`

These are needed at call sites of `applyFnTClosure_extern_wfTypeResult` or
`mapM_applyFnTClosure_forall_wfTypeResult` in:

- `LeanProofs/TypeSafety.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/StepFRApp.lean`

Operational constraint:

- the typing-induction work and the `wfTypeContext` change must land
  together
- changing `wfTypeContext` first creates more holes than it closes
- no plan step is acceptable if it causes net `sorry` inflation without a
  clearly staged removal path

Done conditions for the active blocker:

- all 6 ref-location `sorry`s are removed
- no new `sorry` or `axiom` is introduced
- the unused helper `applyFnTClosure_ok_wfTypeResult` is either deleted or
  repaired without leaving latent proof debt

## 2. Analysis

### 2.1 Scope of the extern proof surface

Raw extern syntax is operationally unreachable on this branch:

- `Expr.externVal`
- `Expr.externFn`
- `Expr.externPfn`

all fail at runtime in `LeanPoison/BigStep.lean`.

So the remaining extern proof surface is entirely about the **typing summary
layer** and the FR witness maps built for it:

1. `typecheckExternVal`
2. `applyFnTClosure` on `FnTClosure.extern`
3. `applyPFnTClosure` on `PFnTClosure.extern`

No eval-side extern contract is currently needed. The open obligations are
about typing artifacts, not executable extern behavior.

### 2.2 Current proof-gap inventory

Verified on 2026-04-08 at `f6b3c7f`:

- `lake build` completes successfully
- the only proof warnings are the known declarations containing the 6
  remaining `sorry`s
- the branch still contains 10 explicit `axiom` declarations in
  `LeanProofs/StepFR.lean`

Current `sorry` inventory:

| File | Declaration | Count | Shape |
|------|-------------|-------|-------|
| `TypeSafety.lean` | `typecheckApp_wfTypeResult` | 2 | `capturedEnvRefLocsBounded` + `etypRefLocsBounded` at `mapM_applyFnTClosure_forall_wfTypeResult` |
| `StepFR.lean` | `applyFnTClosure_ok_wfTypeResult` | 2 | same pair at the extern branch |
| `StepFRApp.lean` | app-side `mapM_applyFnTClosure_forall_wfTypeResult` call | 2 | same pair |

Current axiom inventory:

| Axiom | Status |
|------|--------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | Transitional bundle; should be split into a smaller contract plus an internal theorem |
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | Candidate permanent contract |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | Candidate permanent contract |
| `applyFnTClosure_extern_ok_lookup_origin` | Provisional proof gap |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | Provisional proof gap |
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | Provisional proof gap |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | Provisional proof gap |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | Candidate permanent contract |
| `typecheckExternVal_preserves_lookup_origin_axiom` | Provisional proof gap |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | Provisional proof gap |

Progress state by major line of work:

- single-run strengthening for fresh clean locations: **complete**
- predicate-tag / captured-env boundedness work: **complete**
- captured-locset allocation work: **partially complete**
  - definitions proved
  - `applyFnTClosure_extern_wfTypeResult` proved
  - caller-side invariant provision still open

### 2.3 Contract floor versus proof obligations

The principled extern opacity on this branch is narrow.

What likely remains as permanent contract surface:

- the 3 result-side `QTypRespectsTagMeaning` contracts
- a smaller FR-interpretation contract for effect predicates introduced by
  impure extern summaries, after splitting the current
  `applyFnTClosure_extern_ok_wfTagMeaningCtx` bundle

What should be proved, not assumed:

- guard-tag absence / freshness
- structural `wfTypeResult` preservation for extern application
- lookup-origin / provenance facts
- local boundedness facts needed to feed those proofs

This means the active blocker is a proof-engineering issue, not a
new permanent extern contract.

### 2.4 Simple intuition for the blocker

In plain terms, the proof currently knows how to say:

- every location already present in the memory summary is below `nextLoc`

But the extern application proof also needs to know something stronger:

- every location mentioned *inside types* is below `nextLoc`
- that includes locations hidden inside the argument type
- and locations hidden inside closures captured in the environment

That is the gap.

The current well-formedness invariant only watches the memory summary. It does
not watch references that are stored indirectly inside `varEnv` entries or
inside closure payloads. So when the extern proof tries to show that its
typing-side memory updates stay within bounds, it lacks a global guarantee that
those already-mentioned locations are old enough to be safe.

Why existing runtime facts do not fix this:

- runtime instantiation tells us that a typed variable has some runtime value
- for a reference-typed value, that only exposes one realized location at a
  time
- but the type-level proof needs a bound on *all* logical locations mentioned
  in the type annotation, not just the one runtime witness we happen to see

Why the proposed approach fixes it:

- the new typing induction proves that successful typechecking preserves these
  hidden location bounds for results, arguments, and captured closures
- strengthening `wfTypeContext` packages those bounds into the existing notion
  of context well-formedness, so the context tracks not only memory locations
  but also locations buried inside types and closures
- after that, the extern call sites can obtain the exact boundedness facts they
  need from the same `wfTypeContext` premise they already carry

### 2.5 Why the blocker is real

`applyFnTClosure_extern_wfTypeResult` needs **static** bounds on all logical
locations that may appear in:

- the captured environment of an extern closure
- the argument `ETyp`

The existing exported theorem stack only gives `wfTypeResult`, which bounds
`memEnv'` against `nextLoc'`. It does **not** bound ref-location sets stored in
`varEnv` or inside function-valued `ETyp`s.

Existing FR-side runtime facts are not enough to recover the missing static
bound:

- `runtimeInstantiatesCtx` gives one runtime witness value per typed variable
- `valueHasETyp` for `ETyp.ref ls` only witnesses that **some** `l ∈ ls` is
  realized in `θ`
- but `etypRefLocsBounded` needs **all** `l ∈ ls` to satisfy `l < nextLoc`

So the missing fact cannot be reconstructed from the current `StepFR`
hypotheses. This is exactly why the 4 holes outside `TypeSafety.lean` do not
admit a purely local repair.

Consequences:

- fixing only the `TypeSafety.lean` proof is insufficient
- threading a separate local invariant below `StepFR` is insufficient for the
  4 external call sites
- the real missing input invariant is static well-formedness of `varEnv`

### 2.6 Exact shape of the proposed strengthening

The intended blocker fix is:

- **yes**: strengthen `wfTypeContext` from the current shallow property
  ("all locations in `memEnv` are below `nextLoc`")
- to a **deep nextLoc-boundedness property**
- where "deep" means:
  - memory locations in `memEnv` are below `nextLoc`
  - locations mentioned in ref-typed `varEnv` entries are below `nextLoc`
  - if a `varEnv` entry is a function type, then the captured environment of
    each closure it contains also satisfies the same location-boundedness
    condition recursively

So the answer to the design question is:

- the fix is **not** just "add one more shallow `varEnvRefLocsBounded`
  conjunct"
- the fix **does** need the recursive closure-aware part as well

The document currently exposes that deep property through two top-level
ingredients:

1. `varEnvRefLocsBounded`
2. `varEnvClosuresCapturedRefLocsBounded`

but the implementation should use recursive helper machinery internally rather
than treating those as unrelated facts.

Recommended style for the implementation:

- follow the same pattern already used for recursive tag-boundedness in
  `TypeSafety.lean`, where the proof uses helper notions like
  `CapturedEnvFullBounded` and `etypClosuresFullBounded`
- for ref-location boundedness, introduce the analogous recursive helper layer
  if that keeps the proof cleaner
- keep the public theorem-level interface simple: externally the change is
  "stronger `wfTypeContext`", internally the proof may use a deeper recursive
  property to derive the two concrete facts needed at call sites

### 2.7 Impact assessment

Recommended change: strengthen the *meaning* of `wfTypeContext` so it carries
the needed static `varEnv` bounds.

Impact on the proof stack:

- **Top-level fault-robustness theorem:** no intended statement change
- **`StepFR` / `StepFR_IH`:** no new standalone parameters, but the existing
  `wfTypeContext` premise becomes semantically stronger
- **`FaultRobustnessSpec`:** no intended change

Semantic impact on the language:

- **Soundness:** none; this is proof-only strengthening of a well-formedness
  invariant
- **Precision:** none
- **Language scope:** none
- **Operational semantics:** none

This is still a serious design decision, because it is the one place where the
proof appears to need a justified boundary exception rather than a purely local
repair.

## 3. Approach

I agree with the corrected blocker analysis and with the proposed repair
strategy, with one explicit qualification:

- the semantic strengthening of `wfTypeContext` should be treated as an
  approved design pivot, not as an incidental local refactor

**Explicit statement of the blocker solution:**

- change `wfTypeContext` from the current shallow memEnv-only invariant to a
  deep nextLoc-boundedness invariant
- use recursive closure-aware helper machinery internally so that the new
  `wfTypeContext` really covers captured environments, not only the top-level
  `varEnv`
- continue exposing only `wfTypeContext` at the `StepFR` boundary, rather than
  adding a new separate parameter bundle there

Recommended approach:

1. prove a **private combined typing-induction theorem** with the required
   deep ref-location invariants supplied explicitly, without changing
   `wfTypeContext` yet
2. once that theorem is complete, **atomically** strengthen `wfTypeContext`
   to the deep version and update the downstream callers
3. do not add new separate hypotheses to `StepFR`, `StepFR_IH`, or the
   top-level FR theorem; keep the change packaged inside the existing
   `wfTypeContext` premise

At the level of immediately usable facts, the induction needs:

1. `varEnvRefLocsBounded ctx.varEnv ctx.nextLoc`
2. `varEnvClosuresCapturedRefLocsBounded ctx.varEnv ctx.nextLoc`

These are the concrete projections the call sites need, but conceptually they
come from one deeper recursive nextLoc-boundedness story.

Preferred implementation strategy:

- do **not** build a completely independent second syntax induction if it can
  be avoided
- instead, extend the existing combined `TypeSafety` induction machinery in
  the style of `typecheckExpr_preserves_combined_main`
- the new ref-location outputs should become additional projections from that
  same static induction stack, just as the existing combined theorem already
  feeds the predicate-tag and closure-boundedness projections

Sketch of the deep helper layer Step 1 should use internally:

```lean
-- Shallow: the ETyp itself mentions only locations < nl.
def etypRefLocsBounded (etyp : ETyp) (nl : Loc) : Prop := ...

-- Deep: every closure inside the ETyp has a captured env whose entries are
-- themselves deep-bounded at nl.
def etypClosuresRefLocsFullBounded (etyp : ETyp) (nl : Loc) : Prop := ...

-- Deep captured-env boundedness, recursive through closure-valued entries.
def CapturedEnvRefLocsFullBounded (env : CapturedVarEnv) (nl : Loc) : Prop := ...

-- Top-level projection for the current varEnv.
def varEnvClosuresCapturedRefLocsBounded (S : VarTypeEnv) (nl : Loc) : Prop := ...
```

The intended relationship is:

- `etypRefLocsBounded` gives the shallow fact needed at the extern effect loop
- `etypClosuresRefLocsFullBounded` / `CapturedEnvRefLocsFullBounded` supply the
  recursive closure part
- `varEnvRefLocsBounded` and `varEnvClosuresCapturedRefLocsBounded` are the
  concrete top-level projections exposed at the call sites

So Step 1 is not “prove one isolated lemma and move on”. It is:

1. introduce or identify the deep recursive nextLoc-boundedness predicates
2. extend the existing combined static induction so it preserves them
3. expose the two concrete projections the extern `wfTypeResult` callers need

Recommended handling of the active `StepFR.lean` helper:

- `applyFnTClosure_ok_wfTypeResult` currently has zero callers
- prefer deleting it rather than threading the new obligations through an
  unused wrapper
- only keep it if a real caller appears and the wrapper still earns its place

Secondary implementation guideline:

- if the paired `*_RefLocsBounded` /
  `*_ClosuresCapturedRefLocsBounded` lemmas start to proliferate badly, then
  consider collapsing them to one recursive predicate
- do **not** start with that refactor; first try the minimal proof that unlocks
  the 6 remaining holes

## 4. Plan

High-risk-first. This section is forward-looking only.

**Current plan status:** blocked on the ref-location invariant gap described
above. The next blocker is the
`wfTypeContext` strengthening route described above.

### Step 1. Define and prove `typecheckExpr_wfTypeResult_and_refLocs`

**Status:** next step

Files:

- `LeanProofs/TypeSafety.lean`

Goals:

- define or extend the deep recursive nextLoc-boundedness helper layer
- define and prove the combined typing-induction theorem
  `typecheckExpr_wfTypeResult_and_refLocs`
- prove the core helper lemmas it needs
- if helpful, introduce recursive helper machinery for ref-location
  boundedness, analogous to the existing recursive closure-boundedness
  machinery used for tag reasoning
- keep the theorem private and independent of the new `wfTypeContext` shape

Target theorem sketch:

```lean
private lemma typecheckExpr_wfTypeResult_and_refLocs :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    (∀ l, ctx.memEnv.contains l → l < ctx.nextLoc) →
    varEnvRefLocsBounded ctx.varEnv ctx.nextLoc →
    varEnvClosuresCapturedRefLocsBounded ctx.varEnv ctx.nextLoc →
    typecheck ctx e fuel = .ok res →
    wfTypeResult res ∧
    etypRefLocsBounded res.qualType.etyp res.nextLoc' ∧
    etypClosuresCapturedRefLocsBounded res.qualType.etyp res.nextLoc'
```

What this theorem should give us:

1. the existing shallow result fact: `wfTypeResult res`
2. the shallow ref-location fact needed directly at extern effect loops
3. the recursive closure-captured ref-location fact needed to rebuild stronger
   context well-formedness after inserts, captures, and body typing

Expected helper families:

- monotonicity:
  - `etypRefLocsBounded_mono`
  - `varEnvRefLocsBounded_mono`
  - `capturedEnvRefLocsBounded_mono`
  - `etypClosuresCapturedRefLocsBounded_mono`
  - `varEnvClosuresCapturedRefLocsBounded_mono`
- environment update:
  - `varEnvRefLocsBounded_update`
  - `varEnvClosuresCapturedRefLocsBounded_update`
- captured-env bridges:
  - `capturedEnvRefLocsBounded_of_varEnvRefLocsBounded_toCaptured`
  - `varEnvRefLocsBounded_ofCaptured`
  - `varEnvClosuresCapturedRefLocsBounded_ofCaptured`
- join preservation:
  - `etypRefLocsBounded_joinETyps`
  - `etypClosuresCapturedRefLocsBounded_joinETyps`

Done means:

- the private theorem compiles without changing `wfTypeContext`
- the theorem is clearly a projection/extension of the existing static
  induction stack, not an unrelated duplicate induction unless duplication
  turned out to be strictly simpler
- the hard cases (`var`, `fn`/`externFn`, `vlet`, `app`, `ite`) are all closed
- no downstream file has been changed yet

### Step 2. Atomically strengthen `wfTypeContext` and eliminate the 6 `sorry`s

**Status:** blocked on Step 1

Files:

- `LeanProofs/TypeSafety.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/StepFRApp.lean`
- any downstream FR files touched by `wfTypeContext_of_wfTypeResult`

Changes:

- strengthen `wfTypeContext` from the shallow memEnv-only property to the deep
  nextLoc-boundedness property, exposing at least:
  - `varEnvRefLocsBounded ctx.varEnv ctx.nextLoc`
  - `varEnvClosuresCapturedRefLocsBounded ctx.varEnv ctx.nextLoc`
- update `wfTypeContext_of_wfTypeResult`
- replace `typecheckExpr_preserves_wfTypeResult_main` with the strengthened
  result coming from Step 1
- repair the caller chain in one pass
- delete `applyFnTClosure_ok_wfTypeResult` if it is still unused; otherwise
  update it with the new inputs and discharge its branch-local proof

Done means:

- all 6 remaining ref-location `sorry`s are gone
- there is no net increase in `sorry` or `axiom`
- `lake build` succeeds

### Step 3. Revisit the extern-only axioms unlocked by Step 2

**Status:** pending

Files:

- `LeanProofs/StepFR.lean`
- `LeanProofs/TypeSafety.lean`

Targets:

- reassess `applyFnTClosure_extern_ok_fresh_loc_not_clean`
- reassess `applyFnTClosure_extern_ok_lookup_origin`

Rationale:

- both proofs should become cleaner once caller-side ref-location boundedness is
  available
- do not over-invest in these before Step 2 is complete

### Step 4. Resume axiom reduction on the remaining extern surface

**Status:** pending

Targets:

1. finish the `tagEnvBounded` replacement route and switch the three
   guard-tag-absence axioms to their proved `_of_tagEnvBounded` variants
2. split `applyFnTClosure_extern_ok_wfTagMeaningCtx` into:
   - a smaller effect-predicate interpretation contract
   - proved structural `wfTagMeaningCtx` preservation lemmas

Done means:

- the provisional proof-gap axioms shrink further
- the long-term contract floor is reduced to the genuinely opaque extern facts

## 5. History

### 5.1 Completed work that is no longer on the critical path

- The single-run repair for fresh clean locations is complete.
  - `FreshCleanLocsUnrealizedOneRun` was added to the single-run theorem family.
  - The false local routes in `StepFRApp` / `StepFRIte` were removed.
  - That work no longer blocks extern progress.

- The predicate-tag / captured-env boundedness work is complete.
  - predicate-tag boundedness and closure-captured boundedness are in place
  - `matchGuard_tag_bounded` is proved
  - the old local blockers in that stack are resolved

- The captured-locset allocation work is partially complete.
  - `etypRefLocsBounded`, `capturedEnvRefLocsBounded`, and
    `varEnvRefLocsBounded` are already defined
  - `applyFnTClosure_extern_wfTypeResult` is already proved
  - only the caller-side invariant provision remains

### 5.2 Design decisions already made

- Rejected the old "repair app/ite only with a parallel theorem family" idea.
  The stronger fact needed to compose through `seq`, `vlet`, nested `app`, and
  nested `ite`, so the right home was the global single-run theorem family.

- Approved the local closure-captured boundedness family in `TypeSafety.lean`.
  This stayed below `StepFR` and solved a real gap exposed by the `app` case.

- Approved the recursive captured-entry boundedness direction for the
  predicate-tag work, to reduce duplicated paired hypotheses in closure
  reasoning.

### 5.3 Rejected routes and lessons

- Rejected local-only repair via stronger `contains` plumbing.
  That route only addresses inherited locations and does not solve typing-only
  locations introduced by extern summaries.

- Rejected `wfTypeContext`-first implementation order.
  A prior attempt changed `wfTypeContext` before the supporting induction
  existed and turned 6 holes into 27.

  Verified lesson from that failed attempt:

  - the `wfTypeContext` change and the typing induction are co-dependent
  - the induction must be proved first as a private lemma with explicit inputs
  - only then should the public `wfTypeContext` meaning be changed

### 5.4 Why the `wfTypeContext` change is now considered justified

The earlier boundary rule was:

- keep new invariants below `StepFR`
- do not strengthen the FR-facing interface unless there is a genuine missing
  input invariant

The current blocker is the first place where that escape clause appears to
apply:

- the missing fact is static boundedness of ref-location sets in `varEnv`
- it is not derivable from the current `wfTypeContext`
- it is not reconstructible from runtime instantiation or witness-map facts

So the recommended pivot is not "leak every useful local invariant into FR".
It is a single, narrow strengthening of the existing notion of type-context
well-formedness.

### 5.5 Reference points

Historical references that may still be useful during implementation:

- `iofree:LeanProofs/StepFRIte.lean`
  - `matchGuard_tag_in_bound`
- `iofree:LeanProofs/StepFR.lean`
  - old `predTagsBoundedInCtx`
- `iofree:LeanProofs/TypeSafety.lean`
  - `collectAndAllocExternTags_nextTag_ge`
  - `typecheckExternVal_nextTag_mono`

Current-branch helpers already available:

- `LeanProofs/RegimeConsistency.lean`
  - `EnvRespectsTagMeaning_updateMemEnv`
  - `EnvRespectsTagMeaning_list_fold_updateMemEnv`
  - `QTypRespectsTagMeaning_fn_extern`
  - `QTypRespectsTagMeaning_pfn_extern`
