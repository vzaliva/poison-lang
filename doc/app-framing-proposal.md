# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

Scope of this note:

- in scope: the post-body `agreeOnClean` locations conjunct in the different-body app
  branches
- in scope for dirty-internal app branches: only the locations/framing subproblem inside
  the broader branch `sorry`
- out of scope: other app-proof issues

## 1. Exact Remaining Obligation

The remaining target is the **locations half** of `agreeOnClean`:

```lean
def agreeOnClean ... : Prop :=
  (∀ l qt, ctx.memEnv.lookup l = some qt → qtypCleanUnder R qt →
    agreeLocUnder predSat R μ₁ μ₂ θ₁ θ₂ (l, qt)) ∧
  ...
```

and the relevant location relation is:

```lean
inductive agreeLocUnder ... : (Loc × QTyp) → Prop where
  | agree_values ...
      (hreal1 : θ₁.lookup l = some a₁)
      (hreal2 : θ₂.lookup l = some a₂)
      ...
  | both_unrealized ...
      (hreal1 : θ₁.lookup l = none)
      (hreal2 : θ₂.lookup l = none)
```

So for each clean post-body location, the proof must show **one** of only two things:

- both runs still leave the location unrealized, or
- both runs realize it and the two heap values agree in the required way

There is no third escape hatch.

Because memory stores only integers in this language, the second case is simpler than it
looks:

- once both runs realize the clean location, the remaining value-side obligation is just
  equality of the two realized integers

The proof still has to establish the realization facts first, but there is no richer
heap-value structure hiding here.

## 2. Where This Arises In `stepFR_app`

The framing blocker does **not** arise in every app branch.

There are really two phases in the proof:

- first, `stepFR_app` tries to recover a **shared body** for the two runs
- only if that fails does it switch to two separate single-run body proofs

The shared-body path is available when the callee-side function agreement is strong
enough to say:

- both runs selected the same closure body
- with agreeing captured environments on the clean captured entries

That is the easy case from the framing point of view, because both runs are then traced
through one common body result, and the existing transport lemmas can reuse one common
source member.

The blocker in this note starts only when that shared-body recovery fails.

Concretely, that happens in two situations inside `stepFR_app`:

### A. Dirty-internal function case

Here the callee is still outer-clean enough to enter function agreement, but its
**internal arrow poison is dirty**.

Then FR uses `dirty_internal_arrow` / `dirty_internal_parrow`, which intentionally do
**not** give:

- a common body
- a common binder
- captured-environment agreement

So the proof cannot continue with one common body IH.

### B. Outer-not-clean function case

Here the callee is not even clean enough to enter the strong function-agreement path at
all:

- the proof is in the `¬ qtypCleanUnder result1.qualType` fallback
- for function-typed callees, this is the branch that corresponds to outer poison being
  too dirty to recover shared-body agreement

Again, there is no common body witness.

### Program situations behind those branches

Semantically, both branches cover the same kind of runtime phenomenon:

- the same source callee expression may evaluate to different runtime closures in the two
  runs

That can happen when the function value came from dirty control or other dirty function
selection earlier, for example through a previously merged typing-closure set.

Once the proof is in either fallback family above, it must switch to two separate
single-run body proofs.

That recovers useful unary facts for each run, but at the end we still need to prove
`agreeOnClean` for the joined app result. For locations, that means:

- take a location `l` that is still typed as clean in the final post-body context
- show that the two post-body realization maps and memories still line up on `l`

This is exactly the part that stays open in the narrowed different-body branches.

There are therefore four relevant `sorry` sites behind this discussion:

- two narrowed location-only holes in the outer-not-clean arrow/parrow families
- two broader dirty-internal arrow/parrow branch holes where the same locations issue
  reappears as one sub-obligation, but does not by itself close the full branch

One useful narrowing is that these branches also force the **body typing `pc` to be
poisoned**:

- dirty-internal case: `p = true`, so `join p join p1 pc = true`
- outer-not-clean case: for function-typed callees this is the `p1 = true` family, so
  again `join p join p1 pc = true`

That poisoned-body-`pc` fact is likely important for the proposal below.

## 3. Why Existing Transport Stops Here

The shared-body case already has the right proof shape in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), via
`join_transport_agreeOnClean_from_member`.

That works because both runs can be traced back to one common source member, so for a
clean final location the proof can show either:

- it came from that shared source member, or
- it was unrealized in both runs, using `theta_not_contains_if_not_in_memEnv`

The different-body case loses exactly that common source.

Once the two runs execute different bodies, the narrowed proof is forced into explicit
post-body realization-map cases:

- `none / none`
- `none / some`
- `some / none`
- `some / some`

The `none / none` case is easy. The blocker is the other three.

What is still missing is not a final-result typing fact. It is a **frame fact** about
clean locations across two different body executions:

- can an unrealized clean location become realized in only one run?
- if both runs realize a clean location, must it come from a pre-body clean source?
- if a clean location is realized before the body, can either run overwrite the stored
  integer?

This is also why `wfExtendsMap` is insufficient:

- it preserves existing realizations
- it does not prove `none` stays `none`

So the gap is a real unary clean-location preservation fact, not a missing transport
step.

## 4. Proposal

The simplest missing fact is the same in both implementations:

- reduce each clean post-body location either to a pre-body clean source, or prove that
  the remaining fresh-location cases are impossible in these branches
- then show that each single body execution preserves the relevant clean location well
  enough to rebuild post-body `agreeLocUnder`

The body `pc` is already poisoned in the branches covered by this note, which makes
pre-body inheritance a plausible first target, but not something the proposal should
assume without checking the fresh-allocation cases explicitly.

There are two current implementation strategies.

### Approach 1: narrow helper lemmas prompted by app

Keep `StepFR` unchanged and try to solve the blocker with a small number of helper
lemmas motivated by the app proof, even if one of them ends up living outside
`StepFRApp`.

Informal reading:

- prove that the final clean location obligation can be reduced to a source that both
  runs can reason about locally, and that each body run preserves that source well
  enough for the final binary agreement proof

Required pieces:

1. a static inheritance lemma under poisoned body `pc`
2. a unary preservation lemma for one inherited clean location in one body run
3. a short app-local recombination step that directly rebuilds `agreeLocUnder` from the
   two unary outputs plus the pre-body `agreeLocUnder` fact

Sketch of the static lemma:

```lean
private lemma app_body_clean_loc_inherited_of_poisoned_pc
  (bodyCtx : TypeContext) (body : Expr) (fuel : Nat) (result3 : TypeResult)
  (hpc : bodyCtx.pc = true)
  (htcBody : typecheckExpr .ioFree bodyCtx body fuel = .ok result3)
  (hmono : Regime.monotoneStep bodyCtx.regime result3.regime')
  {l : Loc} {qt_post : QTyp}
  (hlookup_post : result3.memEnv'.lookup l = some qt_post)
  (hclean_post : qtypCleanUnder result3.regime' qt_post) :
  ∃ qt_pre,
    bodyCtx.memEnv.lookup l = some qt_pre ∧
    qtypCleanUnder bodyCtx.regime qt_pre ∧
    qt_post.etyp = qt_pre.etyp ∧
    (qt_post.poison = false → qt_pre.poison = false) := by
  sorry
```

Informal English rendering:

- the intended statement is that a body checked under poisoned `pc` cannot leave behind a
  genuinely new clean location in the final app join
- so any location that is still clean after the body would already have been present and
  clean before the body, with enough type compatibility to transport the final
  agreement proof back to the pre-body witness

Likely proof shape:

- prove this by induction on the body typing derivation, or equivalently on the
  `typecheckExpr` recursion for the body
- in each constructor that can affect memory typing, use the fact that poisoned `pc`
  forces newly created or updated locations to stay dirty
- the first explicit validation case is `newRef`: its stored entry uses
  `⟨ETyp.int, joinPoison pc poison, pred⟩`, so poisoned `pc` forces the poison bit to
  `true`, but does not by itself erase the predicate
- the subtle case is that `qtypCleanUnder` also allows guard-clean locations, so the
  proof must rule out fresh or retagged locations becoming clean in that guarded sense
- `joinMemEnvsStrong` does remove predicates from single-sided fresh locations in the
  final app join, which is helpful, but that still leaves a decisive validation
  question: can two different bodies introduce the same fresh logical location on both
  sides in a way that keeps it clean after the join?
- the only survivors of post-body cleanliness should therefore be locations inherited
  from the input memory typing environment, unless that fresh-on-both-sides case is
  real; if it is real, Lemma A likely needs a third disjunct rather than immediate
  abandonment, because that case lands in the `some / some` branch rather than the
  asymmetric `none / some` blocker

Sketch of the unary preservation target:

```lean
private def PreservesInheritedCleanLocOneRun
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) (l : Loc) : Prop :=
  (θ_in.lookup l = none → θ_out.lookup l = none) ∧
  (∀ a n, θ_in.lookup l = some a → μ_in.lookup a = some n →
    θ_out.lookup l = some a ∧ μ_out.lookup a = some n)
```

Informal English rendering:

- for one run, once a clean location is known to be inherited, the body execution does
  not disturb it
- if the location was unrealized before, it stays unrealized
- if it was realized before, the same logical location still points to the same stored
  integer afterward

Likely proof shape:

- prove this from the existing single-run body proof output rather than by starting a new
  whole-language induction
- do a case split on whether the location was realized before the body
- `theta_not_contains_if_not_in_memEnv` only helps for locations absent from the
  pre-body memory typing environment
- for inherited locations that are present but unrealized, there is a promising route
  through existing infrastructure: `wfTypeContext bodyCtx` puts all pre-body locations
  below `bodyCtx.nextLoc`, `typecheck_nextLoc_mono` shows `nextLoc` only grows, and
  fresh logical allocation starts at that frontier
- that suggests the `none → none` half may be provable without new syntax induction, but
  it still needs one small bridge showing that any newly added `θ` entry corresponds to
  a fresh logical location rather than an old unrealized one
- use the inherited-clean hypothesis plus the single-run postconditions
  (`runtimeInstantiatesCtx`, `wfExtendsMap`, evaluation/result facts, and any location-local
  typing information from Lemma A) to show that this run cannot newly realize or mutate
  that clean location
- the realized-value half is trivial in `parrow` because pure evaluation preserves
  memory, but in `arrow` it becomes a no-write obligation for the concrete realized
  address
- if this starts requiring a fresh syntax induction over all body forms, that is evidence
  to switch to Approach 2 instead

Advantages:

- keeps `StepFR` unchanged
- limits the refactor footprint even if Lemma A itself becomes a shared helper

Decision rule:

- prefer this route only if Lemma A survives the fresh-allocation check and the unary
  preservation lemma stays narrow
- abandon it if Lemma A needs a broader fresh-location disjunction or if Lemma B starts
  duplicating generic step-proof structure

Current assessment:

- with the compatibility data in Lemma A, Approach 1 looks sufficient in principle for
  the final app-local recombination step, but the fresh clean `newRef` / join cases may
  force a broader Lemma A statement
- the `parrow` branch is well supported by existing pure typing and evaluation lemmas,
  so it is a good pilot for validating the shape
- the `none → none` half of Lemma B now looks more tractable than the initial draft
  suggested, because `wfTypeContext` and `nextLoc` monotonicity appear to give most of
  the freshness argument already
- the `arrow` write-preservation half remains the real risk point; that is where Lemma B
  may expand into assignment-style analysis
- the dirty-internal arrow/parrow branches still have broader non-location obligations,
  so solving the framing piece does not by itself close those branch `sorry`s
- if the `arrow` proof starts needing a fresh syntax induction or broad heap-update case
  splits, that is the signal to switch to Approach 2

### Approach 2: strengthen `StepFR`

Package the same unary clean-location preservation fact inside `StepFR` and expose it
through the per-run output used by `StepFR_single_run`.

Informal reading:

- instead of proving app-specific side lemmas, make every `StepFR` result already carry
  the statement that clean output locations are inherited from clean input locations and
  preserved across that step

Core unary property:

```lean
def PreservesInheritedCleanLocsOneRun
  (ctx : TypeContext) (res : TypeResult)
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) : Prop :=
  ∀ l qt_out,
    (ctxAfter ctx res).memEnv.lookup l = some qt_out →
    qtypCleanUnder (ctxAfter ctx res).regime qt_out →
    ∃ qt_in,
      ctx.memEnv.lookup l = some qt_in ∧
      qtypCleanUnder ctx.regime qt_in ∧
      qt_out.etyp = qt_in.etyp ∧
      (qt_out.poison = false → qt_in.poison = false) ∧
      (θ_in.lookup l = none → θ_out.lookup l = none) ∧
      (∀ a n, θ_in.lookup l = some a → μ_in.lookup a = some n →
        θ_out.lookup l = some a ∧ μ_out.lookup a = some n)
```

Informal English rendering:

- after any proved step, if a location is clean in the output typing context, then it
  came from a corresponding clean location in the input typing context
- and the step preserved that location in the only two ways that matter here:
  unrealized stays unrealized, and realized values stay at the same address with the same
  integer contents

Important caveat:

- this packages the same strong inheritance claim as Approach 1
- so it is only a real fallback if that claim is actually true and merely needs to be
  exposed by `StepFR`; if fresh clean allocation is genuinely possible, Approach 2 also
  needs a broader invariant rather than just a relocation of the current one

This approach covers the same substance as Approach 1, but in a unified unary invariant.
`stepFR_app` still needs a small recombination step to turn the two unary outputs into the
final binary `agreeLocUnder` conclusion.

Advantages:

- avoids separate preservation lemmas outside the main step invariant
- may be cleaner if the framing fact is reused broadly

Costs:

- changes `StepFR` and downstream proof interfaces
- broadens the proof refactor beyond `stepFR_app`

Current recommendation:

- try Approach 1 first
- if Lemma A survives but the local unary lemma stops being local, switch to Approach 2
- if Lemma A fails only because of a symmetric fresh-on-both-sides case, restate it with
  an explicit third disjunct before choosing between the two approaches
- if Lemma A fails more fundamentally on fresh-allocation cases, restate the target
  property before choosing between the two approaches


## 5. Action Plan

The remaining blocker is still:

- prove the locations conjunct of `agreeOnClean` after two different body executions

Execution order should discard invalid versions of Approach 1 as early as possible, then
probe the highest-risk proof step on the isolated location holes before touching the
broader dirty-internal branches.

1. Validate Lemma A against fresh-allocation cases before proving anything large.
   The first check is `newRef` under poisoned `pc`, together with the final
   `joinMemEnvsStrong` join. If clean fresh locations can survive in the two-body join,
   the current Lemma A statement is wrong and must be restated before proceeding.
   In the same pass, confirm the existing `wfTypeContext bodyCtx` and `nextLoc`
   monotonicity route for inherited unrealized locations, since that may settle the
   `none → none` half of Lemma B cheaply.
2. If Lemma A survives that check, probe the `arrow` version of Lemma B on the narrowed
   outer-not-clean arrow location hole first.
   This isolates the actual framing issue without the extra obligations carried by the
   dirty-internal full-branch `sorry`.
3. Then discharge the analogous outer-not-clean `parrow` location hole and the short
   recombination step.
   That validates the same pattern on the easier pure branch and gives a clean test of
   whether the helper outputs really match the existing transport shape.
4. Only after the isolated location holes are understood, lift the same machinery into
   the dirty-internal arrow/parrow branches.
   Those branches still need more than the framing fix; in particular, the dirty-internal
   `parrow` branch also carries a non-vacuous `resultAgreesIfClean` obligation.

Exit criterion for Approach 1:

- if Lemma A fails only because of a symmetric fresh-on-both-sides case, restate it with
  an explicit extra disjunct and reassess
- if Lemma A fails more fundamentally on the fresh-allocation check, stop and restate
  the target property before committing to either approach
- if `arrow` Lemma B starts requiring a fresh syntax induction, broad heap-update case
  splits, or generic step-preservation infrastructure, stop and discuss switching to
  Approach 2

Fallback:

- Approach 2 remains the fallback if the inheritance target survives scrutiny but
  Approach 1 does not stay narrow and local; if that happens, update
  [app-proof-plan.md](/home/lord/src/poison-lang/doc/app-proof-plan.md) before
  continuing
