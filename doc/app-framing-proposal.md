# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

It assumes the typing-side fix from [app-typing.proposal](/work/doc/app-typing.proposal) is
accepted, so the old dirty-internal `resultAgreesIfClean` issue is no longer the main
problem.

Scope of this note:

- in scope: the post-body `agreeOnClean` locations conjunct in the different-body app
  branches
- out of scope: the earlier body-IH disconnect and final-result predicate issue

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

One useful narrowing is that these branches also force the **body typing `pc` to be
poisoned**:

- dirty-internal case: `p = true`, so `join p join p1 pc = true`
- outer-not-clean case: for function-typed callees this is the `p1 = true` family, so
  again `join p join p1 pc = true`

That poisoned-body-`pc` fact is likely important for the proposal below.

## 3. Why The Shared-Body Case Works

There is already a successful transport pattern for the shared-member case in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), centered around
`join_transport_agreeOnClean_from_member`.

That pattern works because both runs can be traced back to one common source member.
Then the proof can show:

- the clean final location came from that one source member, or
- it was unrealized in both runs

And if the source member does not contain the location in its memory typing environment,
the proof can use:

```lean
theta_not_contains_if_not_in_memEnv :
  runtimeInstantiatesCtx ctx μ ρ θ →
  ¬ ctx.memEnv.contains l →
  θ.lookup l = none
```

That is enough to close the `both_unrealized` branch in the shared-source situation.

## 4. Why The Different-Body Case Is Hard

In the remaining app branches, the two runs may execute **different bodies**.

That changes the proof shape in one crucial way:

- there is no longer one common source member from which both runs inherit their location
  facts

So the old transport pattern no longer gives what we need.

More concretely, the narrowed proof now reduces the hard part to explicit post-body
realization-map cases:

- `θ₀_body.lookup l = none`, `θ₁_body.lookup l = none`
- `θ₀_body.lookup l = none`, `θ₁_body.lookup l = some _`
- `θ₀_body.lookup l = some _`, `θ₁_body.lookup l = none`
- `θ₀_body.lookup l = some _`, `θ₁_body.lookup l = some _`

The first case is easy:

- `none / none` closes immediately with `agreeLocUnder.both_unrealized`

The real blocker is the other three cases.

## 5. What We Still Do Not Know

The proof currently lacks exactly the facts needed to rule out or handle the nontrivial
lookup cases.

What is missing is not about the final app predicate anymore. It is about **post-body
frame behavior**:

- can a previously unrealized clean location become realized in only one run?
- if both runs realize a clean location, must it come from a pre-existing clean source?
- if a clean location was not written by the body, do the heap contents at its realized
  address stay the same?
- how do we prove those facts when the two runs executed different bodies?

This is why `wfExtendsMap` is not enough:

- it preserves existing realizations
- but it does **not** prove that `none` stays `none`

So it cannot by itself close the asymmetric `none / some` cases.

## 6. Why The Typing Fix Does Not Solve This

The typing fix from [app-typing.proposal](/work/doc/app-typing.proposal) removes one old source
of final-result agreement pressure:

- the final non-function app result no longer stays clean only because of a retained
  guard predicate from an internally dirty callee

But that change says nothing about:

- realization-map growth
- fresh realization of logical locations
- writes to pre-existing clean addresses
- preservation of agreement on clean locations across two different body executions

So the typing fix is orthogonal to this blocker.

It removes the old final-result problem, but the locations conjunct still needs a real
frame argument.

## 7. Why "Allow `some / none` If Poisoned" Is Not A Simple Fix

Probably not.

The reason is that this note is already about locations that satisfy:

- `ctx.memEnv.lookup l = some qt`, and
- `qtypCleanUnder R qt`

So these are exactly the locations that the step theorem is treating as **clean enough
to require agreement**.

There are two important cases:

- if `qt` is simply dirty and **not** clean-under-regime, then `agreeOnClean` does not ask
  for anything about `l` in the first place
- if `qt.poison = true` but `qtypCleanUnder R qt` holds via a guard, then the theorem is
  still deliberately treating `l` as clean enough to require location agreement

So allowing `some / none` just because the underlying `qt.poison` bit is `true` would mean:

- a location may count as clean-under-regime,
- but still be realized in only one run

That is not a local proof trick. It is a semantic weakening of what `agreeOnClean` means.

In the current design, `agreeLocUnder` intentionally has only:

- both realized with agreeing values, or
- both unrealized

There is no asymmetric constructor, and that is consistent with the intended reading:
for a location that still counts as clean, the two runs must line up on whether that
logical location exists and, if it exists, what value it carries.

So:

- allowing `some / none` for truly dirty locations is unnecessary, because those locations
  are already outside `agreeOnClean`
- allowing `some / none` for guard-clean locations would be a broader spec change, not a
  narrow fix for this blocker

That is why the current blocker still points toward a frame lemma, not toward relaxing
`agreeLocUnder`.

## 8. Proposal

The most plausible next step is still a **narrow app/body frame argument**, not a broad
new FR reformulation.

The most useful refinement is to specialize the missing lemmas to the branches where the
**body `pc` is already poisoned**.

Why that might help:

- in exactly the branches discussed in this note, the body is typed under poisoned `pc`
- under poisoned `pc`, the existing typing rules already push direct memory effects
  toward dirty memory typing:
  - `ref e` stores `join pc p { P }`, so with poisoned `pc` the new cell is poisoned
  - assignment updates also join with `pc`, so writes under poisoned `pc` become poisoned
  - assignment through poisoned references already forces `poisoned { no_pred }`

So a location that is still **clean** after such a body probably has a much narrower
explanation:

- it was inherited from the pre-body clean context, not created or retyped as clean by
  the poisoned body

That suggests the missing work may reduce to the following two lemmas.

### A. Static inheritance lemma under poisoned body `pc`

If the body is typed under poisoned `pc` and a location `l` is still clean in the
post-body memory typing environment, then `l` already came from the pre-body clean memory
typing environment.

Informally:

- poisoned-body effects do not create new **clean** locations
- poisoned-body writes do not leave a touched location **clean**

If true, this would immediately rule out many candidate sources of the bad `some / none`
cases.

This looks especially promising on the parrow side, where pure typing already constrains
the post-body memory typing environment more tightly.

A Lean-shaped statement sketch for that lemma could be:

```lean
/-- Sketch only: under a poisoned body `pc`, any post-body clean location must come
from the incoming body memory typing environment, and it was already clean there. -/
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
    qtypCleanUnder bodyCtx.regime qt_pre := by
  sorry
```

If the first implementation pass focuses on the pure `parrow` branch, the same statement
can be instantiated with `body := PExpr.toExpr pbody` and the existing pure-typing bridge
lemmas.

### B. Typed-evaluation preservation lemma for inherited clean locations

This should **not** be phrased as a runtime-only lemma, because "clean" is not a runtime
notion. It is a property of:

- a location's qualified type in the typing context, together with
- `qtypCleanUnder` for the relevant regime

So the second lemma has to combine:

- the pre-body typing context
- the post-body typing result
- the body evaluation result
- and the realization maps / memories produced by that evaluation

The intended shape is:

- assume `l` is inherited from the pre-body context by Lemma A
- assume `l` is clean in the post-body context
- assume the body evaluation and typing evidence produced by the app proof

Then conclude exactly what the locations conjunct needs for that `l`, namely either:

- `θ_body.lookup l = none` on both runs, or
- both runs realize `l` and the realized heap values satisfy `agreeLocUnder`

Informally:

- once Lemma A says that `l` is an inherited clean location, `l` should be treated as
  part of the pre-body clean state that the two runs were already required to agree on
- it should not break agreement on this inherited clean `l`
- so the combined typing-plus-evaluation evidence should force one of the two acceptable
  outcomes for `l`:
  - either both runs still leave `l` unrealized
  - or both runs realize `l`, and because clean memory entries are integer-typed here,
    the realized integers must be exactly equal

This is especially needed on the arrow side, where evaluation may still allocate or write
elsewhere.

A location-local statement sketch for that second lemma could be:

```lean
/-- Sketch only: once `l` is known to be an inherited clean location, the two
single-run body evaluations must preserve enough framing to re-establish the
post-body `agreeLocUnder` obligation for `l`. -/
private lemma app_inherited_clean_loc_agree_after_body
  (predSat : PredSat)
  (preCtx postCtx : TypeContext)
  (μ₀_pre μ₁_pre μ₀_post μ₁_post : Memory)
  (θ₀_pre θ₁_pre θ₀_post θ₁_post : RealizationMap)
  {l : Loc} {qt_pre qt_post : QTyp}
  (hlookup_pre : preCtx.memEnv.lookup l = some qt_pre)
  (hlookup_post : postCtx.memEnv.lookup l = some qt_post)
  (hloc_pre :
    agreeLocUnder predSat preCtx.regime μ₀_pre μ₁_pre θ₀_pre θ₁_pre (l, qt_pre))
  (hclean_pre : qtypCleanUnder preCtx.regime qt_pre)
  (hclean_post : qtypCleanUnder postCtx.regime qt_post)
  (hetyp_post_pre : qt_post.etyp = qt_pre.etyp)
  (hpoison_post_pre : qt_post.poison = false → qt_pre.poison = false)
  (hmono : Regime.monotoneStep preCtx.regime postCtx.regime)
  (hpredCompat₀ :
    ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₀_pre v ↔ qtypPredHolds predSat qt μ₀_post v)
  (hpredCompat₁ :
    ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₁_pre v ↔ qtypPredHolds predSat qt μ₁_post v)
  (hunrealized₀ : θ₀_pre.lookup l = none → θ₀_post.lookup l = none)
  (hunrealized₁ : θ₁_pre.lookup l = none → θ₁_post.lookup l = none)
  (hvalue₀ :
    ∀ a n, θ₀_pre.lookup l = some a → μ₀_pre.lookup a = some n →
      θ₀_post.lookup l = some a ∧ μ₀_post.lookup a = some n)
  (hvalue₁ :
    ∀ a n, θ₁_pre.lookup l = some a → μ₁_pre.lookup a = some n →
      θ₁_post.lookup l = some a ∧ μ₁_post.lookup a = some n) :
  agreeLocUnder predSat postCtx.regime μ₀_post μ₁_post θ₀_post θ₁_post (l, qt_post) := by
  sorry
```

This is deliberately location-local. If it turns out to need much more branch-specific
transport data than this, that is evidence the fix is drifting toward a strengthened
`StepFR` invariant rather than two narrow side lemmas.

So the proposal is not to prove a fully general frame theorem first. It is to try a
strictly narrower path:

1. prove that under poisoned body `pc`, any post-body **clean** location must be inherited
2. prove typed-evaluation preservation only for those inherited clean locations

If both steps work, the location blocker is probably just missing lemmas rather than a
deeper design problem.

### Alternative proposal: strengthen `StepFR` itself

There is also a wider but potentially cleaner option:

- instead of proving Lemma A and Lemma B as standalone facts outside the main step
  invariant, add the needed clean-location preservation fact directly to the `StepFR`
  package

High-level idea:

- make inherited-clean-location preservation a first-class `StepFR` obligation, with the
  usual step-style shape of:
  - an assumption about the incoming state/context
  - and a matching guarantee about the outgoing state/result

One plausible Lean-shaped sketch for the added unary property is:

```lean
/-- Sketch only: unary framing fact for clean output locations that are inherited
from the incoming context. Intended to be carried by `StepFR` for each run. -/
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

A cleaner refactor is **not** to splice two bare copies of that unary fact directly into
the middle of `StepFR`.

Instead, package all per-run postconditions into one unary **edge** judgment, and let
the binary `StepFR` theorem return one instance of that judgment for each run.

To make chaining explicit, the unary judgment should mention both the input and output
configurations. Then the same predicate can expose a "next-step premises" eliminator.

For example:

```lean
inductive StepFRUnaryEdge
  (predSat : PredSat) (tm : TagMeaning)
  (ctx : TypeContext) (res : TypeResult)
  (cf_in : Config) (θ_in : RealizationMap)
  (cf_out : Config) (o : Value) : Prop where
  | intro
      (θ_out : RealizationMap)
      (hθext : wfExtendsMap θ_in θ_out)
      (htyped : valueHasETyp θ_out o res.qualType.etyp)
      (hwfTm : wfTagMeaningCtx tm (ctxAfter ctx res))
      (hwfCtx : wfTypeContext (ctxAfter ctx res))
      (hwfCfg : wfConfig cf_out)
      (hric : runtimeInstantiatesCtx (ctxAfter ctx res) cf_out.memory cf_out.varEnv θ_out)
      (hreg : regimeConsistentWithCtx (ctxAfter ctx res))
      (hcwr :
        consistentWithRegime predSat (ctxAfter ctx res).regime
          (ctxAfter ctx res) cf_out.memory cf_out.varEnv θ_out)
      (hvalc :
        valueConsistentWithRegime predSat (ctxAfter ctx res).regime
          res.qualType cf_out.memory θ_out o)
      (hframe :
        PreservesInheritedCleanLocsOneRun ctx res cf_in.memory cf_out.memory θ_in θ_out) :
      StepFRUnaryEdge predSat tm ctx res cf_in θ_in cf_out o
```

and, crucially, add the explicit chaining view:

```lean
namespace StepFRUnaryEdge

def θ_out
  (h : StepFRUnaryEdge predSat tm ctx res cf_in θ_in cf_out o) : RealizationMap :=
  match h with
  | .intro θ_out .. => θ_out

lemma next_step_premises
  (h : StepFRUnaryEdge predSat tm ctx res cf_in θ_in cf_out o) :
  wfTagMeaningCtx tm (ctxAfter ctx res) ∧
  wfTypeContext (ctxAfter ctx res) ∧
  wfConfig cf_out ∧
  runtimeInstantiatesCtx
    (ctxAfter ctx res) cf_out.memory cf_out.varEnv (θ_out h) ∧
  regimeConsistentWithCtx (ctxAfter ctx res) ∧
  consistentWithRegime predSat (ctxAfter ctx res).regime
    (ctxAfter ctx res) cf_out.memory cf_out.varEnv (θ_out h) := by
  cases h with
  | intro θ_out _ _ hwfTm hwfCtx hwfCfg hric hreg hcwr _ _ =>
      exact ⟨hwfTm, hwfCtx, hwfCfg, hric, hreg, hcwr⟩

end StepFRUnaryEdge
```

Then `StepFR` itself can be refactored to return two unary edges plus the genuinely
binary conclusions:

```lean
def StepFR
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext)
  (e : Expr)
  (res : TypeResult)
  (predSat : PredSat)
  (tm : TagMeaning) : Prop :=
  ...
      terminatesTo mode e ... cf₀ o₀ →
      terminatesTo mode e ... cf₁ o₁ →
      QTypRespectsTagMeaning tm res.qualType ∧
      -- NEW: instead of exposing all unary post-state facts as a flat sequence
      -- of conjuncts, package each run's unary output into one edge witness.
      ∃ out₀ :
          StepFRUnaryEdge predSat tm ctx res
            { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } θ₀ cf₀ o₀,
        ∃ out₁ :
          StepFRUnaryEdge predSat tm ctx res
            { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } θ₁ cf₁ o₁,
          -- UNCHANGED IN SPIRIT: these remain the genuinely binary conclusions.
          -- CHANGED IN FORM: they now consume `θ_out` projected from the unary edges
          -- instead of raw `θ₀'`, `θ₁'` witnesses threaded directly in the tuple.
          agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
            cf₀.memory cf₀.varEnv (StepFRUnaryEdge.θ_out out₀)
            cf₁.memory cf₁.varEnv (StepFRUnaryEdge.θ_out out₁) ∧
          resultAgreesIfClean predSat (ctxAfter ctx res).regime
            cf₀.memory cf₁.memory
            (StepFRUnaryEdge.θ_out out₀) (StepFRUnaryEdge.θ_out out₁)
            res.qualType o₀ o₁
```

Under that refactor, `StepFR_single_run` becomes the natural reuse point for the unary
part:

```lean
lemma StepFR_single_run
  ...
  (ht : terminatesTo mode e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o) :
  QTypRespectsTagMeaning tm res.qualType ∧
  -- NEW: the single-run API now projects the unary edge judgment directly.
  -- This is the intended chaining interface for downstream proofs.
  StepFRUnaryEdge predSat tm ctx res
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } θ cf o := by
  ...
```

Conceptually, the proof would still instantiate the binary theorem with the same run on
both sides, but the **API** exposed to consumers would now be the unary edge judgment. That
is the right reuse direction:

- do **not** try to derive the new unary framing fact from the old `StepFR_single_run`
  after the fact
- instead, strengthen `StepFR` once, and let `StepFR_single_run` project the unary edge

This keeps the framing invariant unary at the level where it naturally lives, avoids
repeating two ad hoc conjuncts throughout the code, and gives `stepFR_app` a clean way to
obtain the same property for each body run by calling the same unary projection twice.

More importantly, the chaining story is now visible in the interface itself:

- `StepFR_single_run` gives a `StepFRUnaryEdge` from one config to the next
- `StepFRUnaryEdge.next_step_premises` extracts exactly the standard premises needed to
  start the next `StepFR` application at `ctxAfter ctx res` and `cf_out`
- the same predicate therefore serves both as the unary summary and as the composition
  boundary between adjacent proof steps

Why this might help:

- each syntax-case proof would carry the same preservation fact together with the rest of
  the `StepFR` pack
- the app case could consume that fact directly instead of proving separate induction
  lemmas on the side
- the strengthened invariant could reuse other data already threaded through `StepFR`,
  such as:
  - `agreeOnClean`
  - `runtimeInstantiatesCtx`
  - `wfExtendsMap`
  - `consistentWithRegime`

Potential advantage:

- avoids having to prove the framing property by a separate large syntax induction that
  duplicates much of the structure already present in the `StepFR` proof

Potential cost:

- this is a wider-scope change
- it would affect the statement of `StepFR` and therefore many downstream lemmas and case
  proofs, not just `stepFR_app`
- it also cuts against the current preference to keep the fix app-local if possible

So this should be treated as an explicit alternative, not the default plan:

- if the two-lemma route stays narrow and local, it is likely preferable
- if the two-lemma route starts turning into a parallel whole-syntax preservation
  development anyway, then strengthening `StepFR` may become the cleaner design

## 9. Practical Reading Of The Open Cases

The remaining open lookup cases can be read informally like this:

- `none / some`:
  explain why one run cannot suddenly realize a location that still counts as clean at
  the end unless the other run can match it
- `some / none`:
  symmetric version of the same problem
- `some / some`:
  explain why the two realized addresses still carry the same integer for that clean
  location after different body executions

So the blocker is not about syntax, closure typing, or final app-result predicates
anymore.

It is now purely about **preserving clean-location agreement across two different body
executions**.

## 10. Bottom Line

Assuming the typing fix from [app-typing.proposal](/work/doc/app-typing.proposal), the remaining
conceptual blocker in `stepFR_app` is:

- prove the locations conjunct of `agreeOnClean` after two different body executions

The shortest plausible route is:

- a narrow static source lemma for clean post-body locations, plus
- a narrow typed-evaluation preservation lemma for inherited clean locations

If that route turns into a demand for whole-language generic preservation cleanup, then
the blocker is larger than this note assumes and should be escalated back to
[app-proof-plan.md](/work/doc/app-proof-plan.md).
