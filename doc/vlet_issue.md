# Issue which makes StepFR_vlet unprovable

## Small Example That Triggers the Block

  Consider:

  let x = y in e2

  Assume (this is the important setup):

  - In the typing context ctx:
      - ctx.varEnv[y] = qtY
      - qtY.pred = Predicate.guardClosure k arg pred_body captured_env (or guardOnly k)
      - ctx.tagEnv does not contain k (so the guard is “unknown” to flow typing)
      - ctx.regime.lookup? k = some b (so the regime does interpret k)
  - In the runtime environment ρ:
      - ρ[y] = v (some runtime value)

  ### What typecheckVlet does (exactly)

  typecheckVlet ctx x e1 e2 fuel (from LeanPoison/Typecheck.lean) does:

  1. result1 ← typecheckExpr ctx e1
  2. varEnv' := ctx.varEnv.update x result1.qualType
  3. ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv', nextLoc := ..., nextTag := ..., regime := result1.regime' }
  4. result2 ← typecheckExpr ctx' e2
  5. Return result2 (with poison := joinPoison ctx.pc p2, predicate = pred2)

  So the new binding x gets exactly the qual-type computed for e1, including its predicate. No extra “provenance” is recorded.

  In our example where e1 = y, typecheckVar sees qtY.pred = guardClosure k ... and since ctx.tagEnv.get? k = none, it returns a type whose predicate is still guardClosure k .... Therefore result1.qualType.pred = guardClosure k ..., and the let adds:

  - ctx'.varEnv[x] = result1.qualType with that same guardClosure tag k.

  ## Where the proof gets stuck (in stepFR_vlet)

  After evaluating e1, runtime extends the environment with the new binding:

  - ρ' = ρ.update x v1 where v1 is the runtime result of e1.

  Now stepFR_vlet needs to re-establish regime consistency (consistentWithRegime ...) for the extended environment. For the new variable x, the obligation (in the hard branch) becomes:

  - you are in the case result1.qualType.pred = Predicate.guardClosure k ...
  - and ctx'.regime.lookup? k = some b

  and you must prove the hconsist field:

  (b = true  → qtypPredHolds predSat result1.qualType μ v1) ∧
  (b = false → ¬ qtypPredHolds predSat result1.qualType μ v1)

  But with guardClosure, qtypPredHolds reduces to:

  - qtypPredHolds predSat result1.qualType μ v1  ≈  predSat k μ v1

  So the proof is forced to show:

  - if R(k)=true then predSat k μ v1, and
  - if R(k)=false then ¬ predSat k μ v1.

  ### Why IH on e1 is “almost” enough, but not directly

  The IH you get from StepFR applied to e1 gives regime-consistency facts for the pre-existing tracked things (vars/locs already in the context after typechecking e1). Concretely, it can tell you:

  - for the old binding y (or an input location l), if its type has guard tag k and R(k)=b, then predSat k μ (that_old_runtime_value) matches b.

  But it does not directly give predSat k μ v1 for the new value v1, unless you can connect v1 to one of those old runtime values.

  In the toy example e1 = y, the missing link is: prove that the evaluation result v1 is actually ρ[y]. With that, you can reuse the IH fact for y to conclude the needed predSat k μ v1.

  In the general stepFR_vlet proof, e1 is arbitrary, and the proof reaches the guardClosure+R.lookup branch without knowing whether e1 was:

  - a variable read (y),
  - a dereference (!r),
  - something more complex that still yields a guarded predicate (because guardClosure can be preserved by typecheckVar/typecheckDeref when the tag is unknown in tagEnv).

  So the proof needs an extra lemma of the form:

  “if typecheckExpr ctx e1 returns a qualType whose predicate is guardClosure k ... and k is interpreted by the regime, then the runtime result v1 is the same as some existing tracked var/loc value that already carries tag k.”

  That “provenance/extraction” fact is exactly what your current admit/sorry is standing in for: producing an ∃ x0 ... or ∃ l0 ... witness whose IH-consistency can be transferred onto the new binding’s v1.

  That’s the blocker: the let introduces a new binder that must be regime-consistent, and in the guardClosure+k∈dom(R) case the proof needs predSat k μ v1, but IH only gives predSat for existing owners of k unless you prove v1 came from one of them.

## Why this is not covered by the Issue #98 fix

`doc/issue-98-proposal.md` fixes regime-aware `if`/`while` by adding a *context-indexed*
premise `consistentWithRegime predSat R ctx μ ρ θ` to `StepFR`.

That premise is strong enough to justify *branch commitment* (because `matchGuard`
returns a tag `k` that comes from some existing owner entry in `ctx.varEnv` or
`ctx.memEnv`, and `consistentWithRegime` constrains those owners).

But in `let x = e1 in e2`, we create a **new owner** `x` whose *tag is copied*
from `e1`'s result type. This is different from the "fresh tag" story:
`x`'s guard tag is not necessarily fresh/internal; it can be an **input/spec tag**
that the regime interprets.

So, unlike `newRef`/`frand`, the `consistentWithRegime` preservation proof for
`vlet` cannot discharge the new binding vacuously via `regimeBounded`.

## Proposed solution: track regime-consistency for returned values

### Intuition

The new binding `x` is populated with the *runtime result* of `e1`:

```
ρ' = ρ.update x v1
```

To show `varsRegime predSat R μ ρ' (x, result1.qualType)` when the predicate is
guarded by a tag `k` in the regime domain, we need the missing fact:

```
R(k) = b  ⇒  (b = true → predSat k μ v1) ∧ (b = false → ¬ predSat k μ v1)
```

This is a **return-value** property. It is not implied by context consistency
alone, because `v1` may be an expression result, not a pre-existing variable or
heap cell lookup that `consistentWithRegime` directly constrains.

### A small, proof-only predicate

Introduce an inductive predicate for a single `(qt, v)` pair:

```lean
inductive valueConsistentWithRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (v : Value) : Prop where
  | noTag :
      qtypGuardTag qt = none →
      valueConsistentWithRegime predSat R qt μ v
  | notInRegime (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = none →
      valueConsistentWithRegime predSat R qt μ v
  | inRegimeTrue (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = some true →
      qtypPredHolds predSat qt μ v →
      valueConsistentWithRegime predSat R qt μ v
  | inRegimeFalse (k : Tag) :
      qtypGuardTag qt = some k →
      R.lookup? k = some false →
      ¬qtypPredHolds predSat qt μ v →
      valueConsistentWithRegime predSat R qt μ v
```

Notes:
- The inductive form is preferred over a definitional function because it enables
  cleaner proof by inversion when extracting `hconsist` facts from IH results.
- This mirrors the `hconsist` component of `varsRegime.withPred_ok` /
  `locsRegime.withPred_ok`, but does **not** require an owner entry in `ctx`.
- For fresh/internal tags (e.g. from `frand`), `regimeBounded R` implies
  `R.lookup? k = none`, so the `notInRegime` constructor applies vacuously.

### Where to use it (minimal surface)

Strengthen the **conclusion** of `StepFR` with per-run return consistency:

```
... →
∃ θ₀' θ₁',
  ...
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf₀.memory o₀ ∧
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf₁.memory o₁ ∧
  resultAgreesIfClean ...
```

Then `stepFR_vlet` can use the IH for `e1` to obtain
`valueConsistentWithRegime ... result1.qualType μ v1`, and plug it directly as
the `hconsist` proof required for the newly-added binding `x`.

This avoids having to prove a brittle "provenance" lemma that recovers an old
owner entry for the returned value.

### Relationship to top-level specs (InputSpec/ObservableSpec)

This is an **internal** step-level strengthening. It does not need to change
the top-level `FaultRobustnessSpec` statement:
- `FaultRobustnessSpec` already constrains initial states via
  `consistentRegimeSpec` (spec-indexed) and uses `observablesEqual` for outputs.
- The new `valueConsistentWithRegime` fact is used only to support intermediate
  reasoning steps that extend the context (notably `vlet`), i.e. it is part of
  the proof infrastructure rather than a user-facing spec condition.

If desired for symmetry, one could define a spec-level analogue for the *final*
return value, but it is not required to repair the `vlet` step proof.

### Proof burden expectations

Most `stepFR_*` cases should discharge `valueConsistentWithRegime` cheaply:
- Many typing rules return `Predicate.noPred` (trivial).
- For guarded results where `R.lookup? k = some b`, the only realistic sources
  of `k` are `var`/`deref`-like cases, where the result value comes directly
  from an owner already covered by `consistentWithRegime`.
- Fresh tags introduced internally are outside the regime domain and are
  vacuous under `regimeBounded` + `regimeConsistentWithCtx`.
