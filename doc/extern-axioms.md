# Extern Functions: FR Contract Surface on `new-iofree`

## CURRENT STEP

Start Step 4 with the guard-tag-absence axioms.

What remains open now:

- `lake build` succeeds with **0 sorry warnings**
- the remaining proof debt is the 10 extern axioms in `LeanProofs/StepFR.lean`
- Step 3 triage is complete; the next task is executing the first
  high-confidence structural reductions

Required next action:

1. replace these three axioms with their already-proved `_of_tagEnvBounded`
   variants:
   - `applyFnTClosure_extern_ok_guardClosure_tag_absent`
   - `applyPFnTClosure_extern_ok_guardClosure_tag_absent`
   - `typecheckExternVal_guardClosure_pred_implies_tag_absent`
2. thread the needed `tagEnvBounded` premises through the current callers;
   expect this to be an inductive boundedness-threading pass rather than a
   one-line caller rewrite
3. if required by the caller path, thread the companion boundedness hypotheses
   used by `typecheckExpr_preserves_tagEnvBounded`
   (`predTagsBoundedInCtx` and `closureEnvBoundedInCtx`) through the same
   recursive contexts
4. rebuild and confirm the axiom count decreases without reintroducing `sorry`

Critical constraints:

- do **not** reintroduce `sorry`
- do **not** add any new `axiom`
- do **not** change `StepFR`, `StepFR_IH`, `FaultRobustnessSpec`, or the
  top-level FR theorem interface unless the axiom triage exposes a genuine new
  blocker
- prefer proving a proved alternative and switching callers over editing the
  semantic contract surface blindly
- do **not** start with the semantic `QTypRespectsTagMeaning` contracts; those
  are currently classified as likely permanent

Done means:

- the three guard-tag-absence axioms are removed from `StepFR.lean`
- callers use the proved `_of_tagEnvBounded` lemmas instead
- the axiom surface is strictly smaller than it is now

**Current status (2026-04-10, branch `new-iofree`, base commit `f6b3c7f`)**

- `TypeSafety.lean`: 0 `sorry`; downstream helper APIs and monotonicity lemmas
  added
- `StepFR.lean`: 0 `sorry`; dead helper wrappers removed
- `StepFRApp.lean`: 0 `sorry`; Step 2b propagation complete
- `StepFRAssign.lean`, `StepFRIte.lean`, `StepFRNewRef.lean`,
  `StepFRVlet.lean`, and `FaultRobustnessProofs.lean` have been repaired to
  the strengthened `wfTypeContext`
- `lake build` succeeds cleanly
- Step 3 triage is now documented in §2.9
- no new theorem-interface or semantic blocker has appeared; the remaining debt
  is entirely the 10 extern axioms in `LeanProofs/StepFR.lean`

## 1. Problem

This note now tracks the remaining extern-related **axiom surface** on
`new-iofree`, after the `sorry`-elimination work has completed. Its purpose is
to separate principled extern contracts from obligations that should still be
proved in Lean, and to record the plan for reducing the remaining axiom set to
the true contract floor.

The end-state goal is:

- eliminate all `sorry`
- eliminate all non-contract `axiom`
- keep only the extern contracts that are unavoidable in principle
- avoid adding new standalone hypotheses to `StepFR`, `StepFR_IH`,
  `FaultRobustnessSpec`, or the top-level FR theorem interface unless a real
  proof obstruction forces that change

Current blocker:

- the remaining proof debt is the 10 extern axioms in `LeanProofs/StepFR.lean`
- some of these are likely genuine permanent extern contracts
- others look structural and may now be provable with the helper stack built
  during the completed `wfTypeContext` / ref-location work

Operational constraint:

- do not reintroduce `sorry`
- do not add new `axiom`
- do not change theorem interfaces unless the axiom triage exposes a genuine
  new blocker
- prefer replacing an axiom with an existing proved alternative before trying a
  larger refactor

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

### 2.4 Completed foundation no longer on the critical path

The previous `wfTypeContext` strengthening and downstream `sorry` elimination
are complete and validated. They remain important background, but they are no
longer the active plan item. The details are recorded in §5 History.

What matters for the current phase:

- `TypeSafety.lean`, `StepFR.lean`, and `StepFRApp.lean` are clean
- the strengthened `wfTypeContext` architecture propagated successfully through
  the current proof stack
- no further proof-architecture or theorem-interface change appears necessary

### 2.5 Current impact assessment

Recommended current change: reduce the remaining extern axiom surface without
changing the theorem interface unless forced.

Impact on the proof stack:

- **Top-level fault-robustness theorem:** no intended statement change
- **`StepFR` / `StepFR_IH`:** no intended new parameters
- **`FaultRobustnessSpec`:** no intended change

Semantic impact on the language:

- **Soundness:** none intended; this is proof-only cleanup
- **Precision:** none
- **Language scope:** none
- **Operational semantics:** none

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

### 2.9 Per-axiom triage

This section is the source of truth for the remaining 10 axioms. Each entry
records:

- what the axiom is really asserting
- whether it looks structurally provable or fundamentally semantic
- whether it should stay as-is, be replaced, or be split

#### 2.9.1 `applyFnTClosure_extern_ok_wfTagMeaningCtx`

Current role:

- used to show that a successful `FnTClosure.extern` application preserves
  `wfTagMeaningCtx` for the post-context

Deep analysis:

- as stated, this bundles two logically different obligations:
  1. the **result** `QTyp` produced by the extern application respects
     `TagMeaning`
  2. every **effect-written memory cell** introduced by the extern summary also
     respects `TagMeaning`
- the structural shell around those obligations is already present in the code:
  `applyFnTClosure` preserves `tagEnv'` and `regime'` structurally, and the
  shape of the memory updates is explicit in the effects loop
- what is not derivable from structure alone is the semantic interpretation of
  the resolved predicates embedded in the extern summary

Judgment:

- **not a good final axiom in its current bundled form**
- **should be split**

Recommended replacement:

- keep a smaller semantic contract for **effect-predicate interpretation** of
  the effect loop writes
- prove a structural `wfTagMeaningCtx` preservation lemma that uses:
  - the smaller effect-write contract
  - the existing / retained result-side `QTypRespectsTagMeaning` contract

Classification:

- **split required**
- the current bundled axiom should not survive unchanged

#### 2.9.2 `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`

Current role:

- used to conclude that the result `QTyp` of an impure extern application
  respects `TagMeaning`

Deep analysis:

- this is the core semantic question for extern returns: does the return
  predicate describe a meaning already sanctioned by `tm`?
- the typechecker only allocates / resolves tags and packages the summary; it
  does not justify that the extern summary is semantically faithful
- even in the simple-return case, the correctness of the resolved predicate is
  an assumption about the extern summary, not a theorem of the typing
  structure
- nested extern returns are not evidence against keeping this contract: even if
  some closure-shape pieces are structural, the semantic content of the
  embedded extern summary remains opaque

Judgment:

- **fundamental extern contract**

Recommended shape:

- keep as a permanent semantic assumption unless later work isolates a smaller,
  clearer statement for just the simple-return fragment

Classification:

- **likely permanent extern contract**

#### 2.9.3 `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`

Current role:

- pure-closure analogue of the previous axiom

Deep analysis:

- same reasoning as the impure version
- the absence of the effect loop simplifies the structure, but not the core
  semantic opacity of the return summary

Judgment:

- **fundamental extern contract**

Recommended shape:

- keep as a permanent semantic assumption, parallel to the impure version

Classification:

- **likely permanent extern contract**

#### 2.9.4 `applyFnTClosure_extern_ok_lookup_origin`

Current role:

- used in the lookup-origin development to show that trusted output cells
  produced by an impure extern application come from trusted input cells

Deep analysis:

- this is not just a shape lemma about `memEnv`; it is a **provenance**
  statement
- structurally, the effect loop can overwrite referenced locations with
  arbitrary summary-provided poison / predicate pairs
- nothing in the typing code alone says that a clean or active-guarded
  non-function output at location `l` must originate from a pre-existing trusted
  cell at `l`
- that property is exactly the kind of semantic discipline we want from externs:
  they must not conjure trusted data out of nowhere
- the current statement is understandable to downstream proofs, but it mixes:
  - clean-value origin
  - active-guard origin for non-function values

Judgment:

- **semantic extern contract, not structurally provable from current code**

Recommended shape:

- keep it as a semantic provenance contract for now
- optionally split later into:
  - clean-origin
  - guard-origin-for-nonfunctions
  if that makes downstream use clearer

Classification:

- **likely permanent extern contract**

#### 2.9.5 `applyFnTClosure_extern_ok_fresh_loc_not_clean`

Current role:

- used to rule out trusted fresh memory entries created by impure externs when
  the application provenance is tainted

Deep analysis:

- this is also a semantic provenance / trust-discipline statement
- structurally, the effect loop does not propagate `p` or `p1` into stored
  memory cells, so the conclusion cannot come from the current typechecker
  equations alone
- the axiom says that even if the summary could write a fresh cell, that fresh
  cell may not end up trusted under tainted application provenance
- this is not an ordinary bookkeeping fact; it is an intended semantic rule for
  extern behavior

Judgment:

- **semantic extern contract**

Recommended shape:

- keep separate from lookup-origin for now; although they share a common
  “externs must not create trust out of nowhere” theme, this axiom talks about
  the stronger `qtypCleanUnder` notion and is usefully direct at its call sites

Classification:

- **likely permanent extern contract**

#### 2.9.6 `applyFnTClosure_extern_ok_guardClosure_tag_absent`

Current role:

- used to show that a guardClosure tag introduced by an impure extern return is
  absent from `tagEnv'`

Deep analysis:

- there is already a proved alternative:
  `applyFnTClosure_extern_ok_guardClosure_tag_absent_of_tagEnvBounded`
- the remaining missing ingredient is no longer semantic; it is the input
  `tagEnvBounded` fact
- that fact now exists in the proof stack via the completed `TypeSafety`
  development
- the execution cost is not just a local caller swap:
  the main caller path runs through the inductive helper
  `ioFree_guardClosure_pred_implies_tag_absent` in `StepFRAssign.lean`
- switching to the proved alternative will require threading
  `tagEnvBoundedInCtx` through recursive cases, and likely also threading the
  companion boundedness hypotheses used by
  `typecheckExpr_preserves_tagEnvBounded`, namely
  `predTagsBoundedInCtx` and `closureEnvBoundedInCtx`

Judgment:

- **structural and already essentially proved**

Recommended replacement:

- switch callers to the `_of_tagEnvBounded` lemma and delete the axiom
- treat this as a mechanical but non-trivial inductive threading task, not as
  a one-line replacement

Classification:

- **provable now**

#### 2.9.7 `applyPFnTClosure_extern_ok_guardClosure_tag_absent`

Current role:

- pure-closure analogue of the previous axiom

Deep analysis:

- same situation as the impure version
- there is already a proved `_of_tagEnvBounded` lemma
- the same caller-threading caveat applies here: the proof route is clear, but
  the rewiring is likely to pass through recursive helper contexts rather than
  a single direct call-site edit

Judgment:

- **structural and already essentially proved**

Recommended replacement:

- switch callers to the `_of_tagEnvBounded` lemma and delete the axiom
- budget for inductive plumbing rather than treating it as a trivial local edit

Classification:

- **provable now**

#### 2.9.8 `typecheckExternVal_QTypRespectsTagMeaning_axiom`

Current role:

- used at the `externVal` typing site to show that the produced result `QTyp`
  respects `TagMeaning`

Deep analysis:

- this is the value-level analogue of the extern-return `QTypRespectsTagMeaning`
  axioms above
- the structural parts are already separated:
  `typecheckExternVal_preserves_wfTagMeaningCtx` is proved
- the remaining unproved content is exactly the semantic interpretation of the
  resolved extern predicate

Judgment:

- **fundamental extern contract**

Recommended shape:

- keep as a permanent semantic assumption
- it is already relatively focused and understandable; no urgent split is
  needed

Classification:

- **likely permanent extern contract**

#### 2.9.9 `typecheckExternVal_preserves_lookup_origin_axiom`

Current role:

- used in the clean-lookup-origin development for `externVal`

Deep analysis:

- this one is different from the impure extern provenance axioms
- `typecheckExternVal` is structurally very simple: it resolves tags and then
  calls `surfaceSpecToQTyp`
- for non-reference results, `memEnv'` is unchanged
- for `ref int`, `surfaceSpecToQTyp` allocates at `ctx.nextLoc`
- so for an **existing** location `l`, lookup-origin should be structural if we
  know the fresh location is genuinely fresh
- however, the current axiom statement does **not** assume `wfTypeContext ctx`
  or any equivalent freshness premise; with that omission, the theorem is
  stronger than the structural code justifies
- the likely repair is to add `wfTypeContext ctx` or the narrower freshness
  premise `∀ l, ctx.memEnv.contains l → l < ctx.nextLoc`
- this looks low-friction for callers, because the surrounding FR development
  already carries context well-formedness in the relevant places

Judgment:

- **likely provable after a statement adjustment**

Recommended replacement:

- replace the axiom with a proved structural lemma whose hypotheses expose the
  freshness needed for `freshTLoc`, most naturally `wfTypeContext ctx` or an
  equivalent “all existing mem locations are < nextLoc” premise
- then update the caller theorem that currently uses the axiom if needed

Classification:

- **blocked on a small statement / helper adjustment, not on extern semantics**

#### 2.9.10 `typecheckExternVal_guardClosure_pred_implies_tag_absent`

Current role:

- used to show that a guardClosure tag introduced by `externVal` is absent from
  `tagEnv'`

Deep analysis:

- there is already a proved alternative:
  `typecheckExternVal_guardClosure_pred_implies_tag_absent_of_tagEnvBounded`
- as with the closure-application guard-tag axioms, the remaining work is just
  supplying the `tagEnvBounded` premise from the existing proof stack
- again, this should not be mistaken for a purely local swap: the caller path
  may need to thread `tagEnvBoundedInCtx` together with the supporting
  boundedness hypotheses used to prove preservation

Judgment:

- **structural and already essentially proved**

Recommended replacement:

- switch callers to the `_of_tagEnvBounded` lemma and delete the axiom

Classification:

- **provable now**

#### 2.9.11 Summary table

| Axiom | Triage | Recommended action |
|------|--------|--------------------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | split required | split into smaller semantic effect-write contract plus proved structural preservation |
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | likely permanent | keep as semantic extern contract |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | likely permanent | keep as semantic extern contract |
| `applyFnTClosure_extern_ok_lookup_origin` | likely permanent | keep for now; optionally split clean-origin and guard-origin later |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | likely permanent | keep as semantic trust/provenance contract |
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | provable now | switch callers to proved `_of_tagEnvBounded` lemma; expect inductive boundedness-threading |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | provable now | switch callers to proved `_of_tagEnvBounded` lemma; expect inductive boundedness-threading |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | likely permanent | keep as semantic extern contract |
| `typecheckExternVal_preserves_lookup_origin_axiom` | likely provable after statement adjustment | expose freshness precondition, then prove structurally |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | provable now | switch callers to proved `_of_tagEnvBounded` lemma; expect boundedness-threading |

## 3. Approach

The active work is now axiom triage and reduction, not proof-architecture
repair.

Recommended approach:

1. separate the remaining 10 axioms into:
   - genuine semantic extern contracts
   - likely structural obligations now provable with the existing helper stack
   - statements that need one further structural split or helper lemma before
     proof work should begin
2. prefer switching callers to already-proved alternatives before attempting
   deeper refactors
3. only after that triage, choose one small, high-confidence structural target
   and execute it end-to-end

Preferred reduction order:

1. guard-tag-absence axioms
   - they already have `_of_tagEnvBounded` proved variants
   - the remaining work is mostly caller rewiring
2. the `wfTagMeaningCtx` preservation bundle
   - likely best handled by splitting off a smaller semantic contract from the
     structural preservation part
3. the provenance / freshness axioms
   - revisit only after the easy structural replacements are done

Guideline:

- until proved otherwise, treat the three `QTypRespectsTagMeaning` axioms as
  likely permanent contracts
- challenge every other axiom to justify why it cannot be reduced further

## 4. Plan

High-risk-first. This section is forward-looking only.

**Current plan status:** Step 1, Step 2a, Step 2b, and Step 3 are complete.
The current step is Step 4 axiom reduction.

### Step 3. Do per-axiom triage before any axiom-reduction implementation

**Status:** complete

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

**Status:** current

Targets:

1. finish the `tagEnvBounded` replacement route and switch the three
   guard-tag-absence axioms to their proved `_of_tagEnvBounded` variants
2. split `applyFnTClosure_extern_ok_wfTagMeaningCtx` if Step 3 still judges the
   bundled statement too coarse:
   - a smaller effect-predicate interpretation contract
   - proved structural `wfTagMeaningCtx` preservation lemmas
3. prove any remaining provisional axioms that Step 3 classified as
   structurally derivable with the current helper stack
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

### 5.9 Completed Step 2b details moved out of the forward plan

- The former Step 2b execution details are no longer part of §4 Plan.
- The completed app-propagation work is now recorded here, since it no longer
  belongs to the forward-looking action list.
- The important outcome is:
  - `StepFRApp.lean` is clean
  - the ref-location / `wfTypeContext` propagation problem is solved
  - the active plan has shifted entirely to axiom triage and reduction

### 5.10 Step 3 axiom triage outcome

- The remaining 10 axioms were classified into three groups:
  - likely permanent semantic extern contracts
  - provable now with the current helper stack
  - likely provable after a small statement adjustment or split
- The first concrete Step 4 execution target is the three guard-tag-absence
  axioms, because they already have proved `_of_tagEnvBounded` variants.
- The `QTypRespectsTagMeaning` axioms remain the leading candidates for the
  true permanent contract floor.

### 5.11 Why the `wfTypeContext` change is now considered justified

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

### 5.12 Reference points

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
