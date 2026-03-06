# Narrow `stepFR_app` Framing / Location Blocker

This note isolates the remaining **locations / framing** blocker in `stepFR_app`.

Status:

- this is a focused blocker memo, not the active planning document
- the active next-step plan now lives in `doc/app-proof-plan.md`
- design history for attempted framing routes lives in `doc/app-proof-history.md`

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

Final recombination is no longer the blocker.

The shared-body case already has the right proof shape in
[`StepFRApp.lean`](/work/LeanProofs/StepFRApp.lean), via
`join_transport_agreeOnClean_from_member`.

That lemma already packages the joined clean-location proof once the branch can supply
either:

- a source-member lookup for the clean final location, or
- final `θ₀.lookup l = none ∧ θ₁.lookup l = none`

In the shared-body case this is easy, because both runs can be traced back to one common
source member, so for a clean final location the proof can show either:

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

So the remaining gap is a real unary clean-location preservation fact, not a missing
final recombination step.

## 4. Proposal

The cleanest next move is to strengthen the unary interface in `StepFR.lean`.

The missing fact is not app-specific. It is a single-run statement:

- given one body execution, use the same post-run realization map `θ'` already returned
  by the unary theorem
- strengthen that unary package with inherited-clean-location preservation facts for that
  same `θ'`

That is exactly the fact the different-body app branches need and do not currently get
from `StepFR_single_run`.

### 4.1. What To Add

Add a small helper predicate in `StepFR.lean`, next to the new theorem that uses it:

```lean
/-- For one run, an inherited clean location is preserved strongly enough for the
later binary `agreeLocUnder` proof. -/
inductive PreservesInheritedCleanLocOneRun
  (μ_in μ_out : Memory) (θ_in θ_out : RealizationMap) (l : Loc) : Prop where
  | both_unrealized
      (h_in : θ_in.lookup l = none)
      (h_out : θ_out.lookup l = none)
  | preserve_value
      (a : Address) (n : Int)
      (h_in : θ_in.lookup l = some a)
      (h_mem_in : μ_in.lookup a = some n)
      (h_out : θ_out.lookup l = some a)
      (h_mem_out : μ_out.lookup a = some n)

/-- The theorem-level wrapper: every inherited clean input location is preserved. -/
inductive PreservesInheritedCleanLocsOneRun
  (ctx : TypeContext)
  (μ_in μ_out : Memory)
  (θ_in θ_out : RealizationMap) : Prop :=
  | intro
      (hpres :
        ∀ l qt,
          ctx.memEnv.lookup l = some qt →
          qtypCleanUnder ctx.regime qt →
          PreservesInheritedCleanLocOneRun μ_in μ_out θ_in θ_out l)
```

Then extend the conclusion of `StepFR_single_run` itself.

The intended change is:

- same single-run hypotheses
- same existential witness `θ'`
- same output package
- one extra conjunct `PreservesInheritedCleanLocsOneRun ... θ θ'`

So the first implementation step should be to strengthen `StepFR_single_run`, not to add
a separate theorem with a new name.

```lean
/-- Sketch only: same theorem as `StepFR_single_run`, but with one extra conjunct in the
existential package. -/
lemma StepFR_single_run
  ...same hypotheses as today... :
  QTypRespectsTagMeaning tm res.qualType ∧
  ∃ θ_out,
    -- Same existential package as `StepFR_single_run` up to this point.
    wfExtendsMap θ θ_out ∧
    valueHasETyp θ_out o res.qualType.etyp ∧
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧
    wfTypeContext (ctxAfter ctx res) ∧
    wfConfig cf ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ_out ∧
    regimeConsistentWithCtx (ctxAfter ctx res) ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime
      (ctxAfter ctx res) cf.memory cf.varEnv θ_out ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime
      res.qualType cf.memory θ_out o ∧
    -- New conjunct: every inherited clean input location is preserved on this same `θ_out`.
    PreservesInheritedCleanLocsOneRun ctx μ cf.memory θ θ_out := by
  sorry
```

The intended reading is:

- the theorem does **not** classify all clean output locations
- it does **not** try to solve the symmetric-fresh case
- it simply strengthens the package already returned by `StepFR_single_run`
- once the app proof is reasoning about a clean location already present in the input
  typing context, this extra conjunct gives the preservation facts needed for that
  location
- the inner inductive handles the per-location case split, while the outer single-
  constructor inductive packages the universal quantification as named evidence

### 4.2. How `stepFR_app` Uses It

The intended use in `stepFR_app` is:

1. In a different-body branch, run the strengthened unary theorem once per body run.
2. Obtain post-run maps `θ₀_body` and `θ₁_body` plus inherited-clean
   preservation facts for each run.
3. For a location `l` that the app proof has already identified as inherited and clean in
   the pre-body context:
   - if pre-body agreement gives `both_unrealized`, use the unary theorem on both runs to
     get `θ₀_body.lookup l = none` and `θ₁_body.lookup l = none`
   - if pre-body agreement gives a realized location, use the unary theorem on both runs
     to show the same address and integer are preserved
4. Feed those facts into the existing final recombination step.

So the theorem plugs exactly into the current gap:

- `stepFR_app` already knows how to finish once it has either a source-member witness or
  final `none / none`
- the strengthened unary theorem is what should produce the final `none / none` fact for
  inherited clean locations in the different-body branches

### 4.3. Proof Ingredients

The most relevant existing ingredients are:

- `theta_not_contains_if_not_in_memEnv` in `StepFR.lean`
- the old-location transport in `stepFR_newRef`
- the final-clean-implies-old-clean assignment argument in `StepFRAssign`
- the pure-body memory / regime bridges used by the `parrow` path

So this proposal is coherent at the module level:

- the definition and theorem live in `StepFR.lean`
- `stepFR_app` consumes them
- the symmetric-fresh case stays local to `StepFRApp.lean`


## 5. Action Plan

The next track should build the strengthened `StepFR_single_run` theorem described above
in `StepFR.lean`, then
return to `stepFR_app` and use it in the different-body branches.

The operational steps live in [app-proof-plan.md](app-proof-plan.md).
