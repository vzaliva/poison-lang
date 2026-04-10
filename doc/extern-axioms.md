# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Do per-axiom triage now that the `sorry` elimination phase is complete.

What remains open now:

- `lake build` succeeds with **0 sorry warnings**
- the remaining proof debt is the 10 extern axioms in `LeanProofs/StepFR.lean`
- the next task is no longer generic sorry cleanup; it is deciding which axioms
  are genuine permanent extern contracts and which now have a concrete proof
  route

Required next action:

1. classify each remaining axiom in `LeanProofs/StepFR.lean` as:
   - likely permanent extern contract
   - likely provable now with the current helper stack
   - blocked on one specific missing structural lemma
2. update this document with a concrete per-axiom strategy table
3. choose one small, high-confidence structural target from the “likely
   provable now” class as the first Step 4 execution item

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** add any new `axiom`
- do **not** change `StepFR`, `StepFR_IH`, `FaultRobustnessSpec`, or the
  top-level FR theorem interface unless the axiom triage exposes a genuine new
  blocker
- prefer proving a proved alternative and switching callers over editing the
  semantic contract surface blindly

Done means:

- this document records a concrete strategy for each remaining axiom
- the next execution step can target a specific axiom or small axiom cluster
  instead of “reassess axiom surface”

**Current status (2026-04-09, branch `new-iofree`, base commit `f6b3c7f`)**

- `TypeSafety.lean`: 0 `sorry`; downstream helper APIs and monotonicity lemmas
  added
- `StepFR.lean`: 0 `sorry`; dead helper wrappers removed
- `StepFRApp.lean`: 0 `sorry`; Step 2b propagation complete
- `StepFRAssign.lean`, `StepFRIte.lean`, `StepFRNewRef.lean`,
  `StepFRVlet.lean`, and `FaultRobustnessProofs.lean` have been repaired to
  the strengthened `wfTypeContext`
- `lake build` succeeds cleanly
- no new theorem-interface or semantic blocker has appeared; the remaining debt
  is entirely the 10 extern axioms in `LeanProofs/StepFR.lean`

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

The original blocker was the last **6 `sorry` terms**, all of the same shape:

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
- the current worktree now carries temporary `TypeSafety` and downstream
  placeholder `sorry`s from the first all-at-once Step 2 attempt; this plan
  now splits the work so those are removed in two stages rather than one

Done conditions for the active blocker:

- the original 6 ref-location caller `sorry`s are removed
- the temporary `app` `sorry` introduced during Step 1 is also removed
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

Verified on 2026-04-09 after Step 2b completion:

- `lake build` completes successfully
- there are no `sorry`-warning declarations in `LeanProofs/`
- the branch still contains 10 explicit `axiom` declarations in
  `LeanProofs/StepFR.lean`

Current `sorry` inventory:

There are currently **no remaining `sorry` declarations** in `LeanProofs/`.

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
- captured-locset allocation work: **complete on the `TypeSafety` side and
  fully propagated**
  - the `TypeSafety` and `StepFR` layers are clean
  - downstream `StepFRApp` propagation is complete
  - the remaining work is axiom triage and reduction

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

### 2.8 Current assessment after Step 2b completion

The overall plan is still viable.

What the current state demonstrates:

- the strengthened meaning of `wfTypeContext` was sufficient to clean
  `TypeSafety.lean` and `StepFR.lean`
- the downstream propagation has now succeeded in `StepFRApp.lean` as well
- the remaining debt does **not** point to a new missing theorem-interface
  invariant; it points to the still-unreduced extern axiom surface

The remaining work now has two distinct tiers:

1. **Tier 1: `sorry` elimination**
   - complete
   - validates the strengthened `wfTypeContext` architecture end-to-end through
     the current proof stack
2. **Tier 2: axiom reduction**
   - still centered in `StepFR.lean`
   - materially less analyzed than the `sorry` elimination work
   - likely contains a mix of genuine permanent extern contracts and still-provable
     structural obligations

This means the end-state goal remains realistic, but the remaining distance is
not uniform: the `sorry` elimination is done, while the axiom-reduction phase
still needs explicit per-axiom proof planning.

What does **not** appear to be needed:

- no further strengthening of `wfTypeContext`
- no new premise on `StepFR`, `StepFR_IH`, or `FaultRobustnessSpec`
- no implementation or specification change in `LeanPoison/` or
  `poison-lang-spec/`

So the planning conclusion is:

- keep the current proof architecture
- treat Step 2b as complete
- move to per-axiom triage before any further proof implementation

### 2.9 Preliminary per-axiom triage

Based on the current code, the remaining 10 axioms fall into three groups.

Likely permanent extern contracts:

- `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`
- `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`
- `typecheckExternVal_QTypRespectsTagMeaning_axiom`

Reason:

- these are the semantic obligations that connect opaque extern summaries to
  `TagMeaning`; they are not obviously derivable from the structural
  typechecking code alone

Likely provable now with the current helper stack:

- `applyFnTClosure_extern_ok_guardClosure_tag_absent`
- `applyPFnTClosure_extern_ok_guardClosure_tag_absent`
- `typecheckExternVal_guardClosure_pred_implies_tag_absent`

Reason:

- all three already have proved `_of_tagEnvBounded` variants
- `TypeSafety.lean` now proves `typecheckExpr_preserves_tagEnvBounded`
- the remaining task is to feed the appropriate `tagEnvBounded` premise to the
  proved alternatives and switch callers

Still needs focused structural analysis:

- `applyFnTClosure_extern_ok_wfTagMeaningCtx`
- `applyFnTClosure_extern_ok_lookup_origin`
- `applyFnTClosure_extern_ok_fresh_loc_not_clean`
- `typecheckExternVal_preserves_lookup_origin_axiom`

Reason:

- these look more structural than semantic, but the exact proof route is not
  yet pinned down enough to schedule implementation blindly
- `applyFnTClosure_extern_ok_wfTagMeaningCtx` in particular likely wants to be
  split into a smaller semantic effect-predicate contract plus proved
  structural preservation lemmas

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

**Current plan status:** Step 1, Step 2a, and Step 2b are complete. The
current step is Step 3 axiom triage.

### Step 2b. Finish the remaining `StepFRApp` propagation work

**Status:** complete

Most reusable helper first:

- close `join_transport_wfTypeContext`, because several surviving app proofs
  depend on the same transport shape and this helper should collapse the
  repeated join-side obligations once finished

Files:

- `LeanProofs/StepFRApp.lean`

Changes:

- finish `join_transport_wfTypeContext`
- in that helper, make the `nextLoc` transport explicit rather than implicit:
  prove the two `varEnv` projections by monotonicity from
  `wfTypeContext (ctxAfter ctx first)` to `ctxAfter ctx res`
- replace the remaining manual closure-body `wfTypeContext` constructions with
  `wfTypeContext_closureBody`
- use the public `TypeSafety` APIs
  `typecheckExpr_preserves_etypRefLocsBounded` and
  `typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded`
  at the remaining app-body sites
- at each closure-body site, explicitly project the per-closure
  `CapturedEnvRefLocsFullBounded` witness from the full
  `etypClosuresCapturedRefLocsBounded` result using the closure membership
  hypothesis available at that site
- discharge the remaining `wfTypeContext_of_wfTypeResult` join instantiations
  using explicit `ctx.nextLoc ≤ ... ≤ first.nextLoc'` monotonicity chains,
  including `applyFnTClosure_nextLoc_mono` where the chain passes through a
  closure application
- treat one arrow site and one parrow site as templates first; the remaining
  Pattern A sites are similar but not literally identical in local context

Done:

- `LeanProofs/StepFRApp.lean` has no `sorry` warnings
- `lake build` succeeds without `sorry` warnings
- no new interface changes were needed beyond the already-approved
  strengthening of `wfTypeContext`

### Step 3. Do per-axiom triage before any axiom-reduction implementation

**Status:** current

Files:

- `LeanProofs/StepFR.lean`
- `LeanProofs/TypeSafety.lean`
- `doc/extern-axioms.md`

Targets:

- classify each remaining axiom into one of:
  - likely permanent extern contract
  - likely provable now with the current helper stack
  - blocked on a specific missing structural lemma
- for every axiom in the second and third classes, record a concrete intended
  proof route in this document
- specifically revisit:
  - the three guard-tag-absence axioms
  - `applyFnTClosure_extern_ok_fresh_loc_not_clean`
  - `applyFnTClosure_extern_ok_lookup_origin`
  - `typecheckExternVal_preserves_lookup_origin_axiom`
  - the `applyFnTClosure_extern_ok_wfTagMeaningCtx` bundle

Rationale:

- the current permanent/provisional classification is useful but still only
  partially tested
- after Step 2b, the proof state should be stable enough to separate genuine
  contracts from ordinary proof debt with much less guesswork

Done means:

- the document contains a per-axiom strategy table or equivalent prose
  classification
- the next execution step can target one concrete axiom or one small axiom
  cluster rather than “reassess”

### Step 4. Execute the axiom-reduction plan from Step 3

**Status:** pending

Targets:

1. finish the `tagEnvBounded` replacement route and switch the three
   guard-tag-absence axioms to their proved `_of_tagEnvBounded` variants
2. prove any provisional axioms that Step 3 classified as structurally
   derivable with the current helper stack
3. split `applyFnTClosure_extern_ok_wfTagMeaningCtx` if Step 3 still judges the
   bundled statement too coarse:
   - a smaller effect-predicate interpretation contract
   - proved structural `wfTagMeaningCtx` preservation lemmas
4. leave only the axioms that Step 3 classified as genuine permanent extern
   contracts

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

### 5.4 New finding from the current Step 1 execution

- Step 1 closed 15/16 cases of the new ref-location induction in
  `LeanProofs/TypeSafety.lean`.
- The remaining `app` case is co-dependent with the stronger `wfTypeContext`
  bridge, for the same reason as the original 6 caller holes: the extern
  application path needs ref-location boundedness facts from the typing IH at
  exactly the point where the stronger context invariant is needed.
- Therefore Step 1 should be considered **substantially complete**, not blocked
  in the wrong direction.
- The right next move is to carry the temporary `app` `sorry` into the
  strengthened-`wfTypeContext` work, but only after the `TypeSafety` layer is
  finished internally; the later plan split makes this explicit as Step 2a
  followed by Step 2b.

### 5.5 New finding from the first all-at-once Step 2 attempt

- Strengthening `wfTypeContext` and immediately propagating the new interface
  through `StepFR*` files created a large temporary proof-debt spike.
- The core issue was not that the stronger `wfTypeContext` idea was wrong.
  The issue was step granularity.
- The merged `TypeSafety` induction needed inline `wfTypeResult` proofs in
  compound cases before the old helper stack could be reused cleanly.
- Pushing the stronger interface downstream before stabilizing that internal
  `TypeSafety` layer caused placeholder `sorry`s to spread through many
  `StepFR*` files.
- The revised plan therefore splits the old Step 2 into:
  - Step 2a: finish `TypeSafety` internally
  - Step 2b: only then propagate downstream and close the original caller
    holes

### 5.6 New finding from the `TypeSafety` / `StepFR` cleanup

- `TypeSafety.lean` is now clean: the combined ref-location induction closes
  all cases and exposes the public APIs the downstream files needed.
- `StepFR.lean` is now clean: the unused `applyFnTClosure_ok_wfTypeResult`
  wrapper and its proof debt were removed rather than repaired.
- This confirms that the strengthened `wfTypeContext` design is workable
  without any further theorem-interface change.

### 5.7 New finding from the downstream sorry sweep

- The downstream propagation succeeded everywhere it was attempted outside
  `StepFRApp.lean`.
- `lake build` now succeeds with 7 `sorry`-warning declarations, all in
  `StepFRApp.lean`, and no non-`sorry` warnings.
- The remaining `StepFRApp` debt is structurally narrow:
  - repeated closure-body `wfTypeContext` construction
  - repeated join-side `wfTypeContext` transport
- No new semantic blocker was uncovered. The remaining work is local proof
  threading, not a planning-stage design failure.

### 5.8 New finding from Step 2b completion

- The remaining `StepFRApp` proof debt was fully discharged without any further
  change to theorem interfaces or proof architecture.
- `TypeSafety.lean` now exports the helper lemmas the downstream app proof
  needed, including the monotonicity and captured-env bridge lemmas used during
  propagation.
- `lake build` is now clean: 0 `sorry`, 0 warnings.
- This confirms that the strengthened `wfTypeContext` architecture is not only
  viable in principle but fully integrated through the current proof stack.

### 5.9 Why the `wfTypeContext` change is now considered justified

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

### 5.10 Reference points

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
