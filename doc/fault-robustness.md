# Fault Robustness (FR) vs Non-Interference (NI)

This note reframes the non-interference statement in terms of the project goal:
fault propagation with predicate-based de-poisoning. The existing NI property is
stronger than needed for that goal and creates proof friction for inductive
chaining.

## Problem with the current NI statement

The current NI definition (see `doc/poison-lang-description.tex`) uses a
critical-input specification `S` and treats all other inputs as unconstrained.
This implies:

- Outputs must be independent of *every* input not in `S`, even if that input is
  trusted and intended to influence the result.
- The proof has to show agreement for observables under arbitrary differences in
  non-critical inputs, which is stronger than "faults do not affect outputs."
- This strength leaks into step-level statements, making the step theorem
  "prescriptive" about arbitrary output specs and complicating chaining/base
  cases.

In short: NI currently enforces a global independence property, while our real
goal is fault-robustness: outputs should be insensitive to *faulty* inputs, but
may depend on trusted inputs.

## Proposed property: Fault Robustness (FR)

We keep the input specification name `S` (as in the current NI statement), but
change how we treat *inputs not listed in* `S`. Instead of allowing them to vary
arbitrarily, we require them to agree across runs. Intuitively, `S` lists the
critical inputs (the ones that may be faulty); everything else in the initial
context is trusted.

Partition initial inputs into:

- `S` (critical inputs): logical locations and variables that may be faulty.
  These are the only inputs allowed to differ across runs when their guard
  regime says they are invalid.
- `T` (trusted contextual inputs): inputs present in the initial typing context
  but not in `S` that are typed clean under `R`. These must agree across runs.
- `U` (unused inputs): not in context; irrelevant.

Guard regimes range only over tags that appear in predicates attached to `S`,
exactly as in the current NI definition.

### FR statement (informal)

For each guard regime `R`, for any two executions that:

- agree on all trusted inputs `T`,
- agree on each critical input in `S` when its guard evaluates to true under `R`,
- may differ on critical inputs whose guard is false under `R`,

the observable outputs (return value if observable, and memory at the locations
listed in `obs`) are equal.

This keeps the same guard/closure machinery, but changes the quantification over
non-faulty inputs from "unconstrained" to "must agree". In the proof, the
initial agree-on-clean relation is derived from the typing context and should
cover at least the trusted inputs `T` (context entries not in `S`) that are
typed clean under `R`.

## Relationship between NI and FR

Let `NI(S, obs)` be the current non-interference property with critical-input
spec `S`. Let `FR(S, obs)` be the new fault-robustness property with critical
inputs `S` and trusted inputs `T` (all context entries not in `S`).

Then:

1. **NI implies FR (same spec).**
   `NI(S, obs)` quantifies over *all* differences in non-critical inputs and
   still requires equal observables. FR quantifies over a *subset* of those
   input pairs (only where non-faulty inputs agree). Therefore:

   `NI(S, obs) => FR(S, obs)`.

2. **FR is strictly weaker.**
   `FR(S, obs)` does not require outputs to be independent of trusted inputs.
   Thus the converse does not hold in general.

3. **FR is NI with a side condition.**
   `FR(S, obs)` is equivalent to `NI(S, obs)` *restricted to runs that agree on
   non-faulty inputs*. This is the intended operational reading.

## Implications for security properties

- FR is a fault-isolation property, not full non-interference.
- Observables may depend on trusted inputs; they must not depend on faulty ones
  unless they have been validated (guard true) or de-poisoned.
- The type system remains conservative: clean means proven reliable; poisoned
  means "may be faulty."

## Step theorem vs top-level property

- **Top-level FR (spec-driven).** The statement is indexed by a fixed critical
  input spec `S` and observable spec `obs`. It quantifies over initial runs that
  conform to `S` under a guard regime `R`, and requires observable agreement.
- **Step theorem (context-driven).** The induction principle should take the
  *typing context* as input and relate it to the context after evaluating the
  expression. This is the right shape for induction over syntax (including
  sequencing and `let`).
- **No `S` in the step theorem.** The step theorem should not mention the
  critical-input spec directly. `S` is fixed in the top-level FR statement, and
  a separate derivation lemma uses `S` to establish the initial step-theorem
  premises.
- **No `obs` in the step theorem.** The observable spec is also top-level only.
  The step theorem maintains a context-derived agreement relation (e.g.
  "agree on all items typed clean under regime `R`"). The same derivation lemma
  uses `obs` (via clean typing) to conclude observable equality.
- **Agreement is context-derived.** In the step theorem, agreement across runs
  should be required only for items that are *typed clean under the current
  regime*. Items typed poisoned may differ. This “agree-on-clean” relation is
  updated as the context evolves.
- **Result agreement for clean outputs.** The step theorem should ensure that
  if the result of a subexpression is typed clean (or de-poisoned) under `R`,
  then the two runs’ result values agree (e.g., via `agreeValueUnder`). This is
  essential for chaining (e.g., `let`/application), where subexpression results
  become inputs to the next step.
- **Base cases simplify.** Base cases no longer need to prove properties for
  arbitrary output specs; they only need to preserve the context evolution and
  maintain agreement for clean-typed observables.

## Top-level, step, and derivation lemmas (sketch)

Intuition: the top-level theorem is hard to prove directly by induction because
it is spec-driven and compares full executions with asymmetric input/output
premises. The step theorem is more generic and context-driven, making it
amenable to structural induction. The derivation (bridge) lemma then states
that, under the standard restrictions on `S`, `obs`, the initial context, and
typing results, the step theorem implies the top-level property.

In the sketch below, `agreeOnTrustedInputs` is a shorthand for agreement on
context entries not in `S` that are typed clean under `R` (variables via
`agreeVarUnder`, locations via `agreeLocUnder`).

```lean
-- Top-level FR: spec-driven, mentions S and obs (shape matches NonInterferenceSpec).
theorem FaultRobustness
  (S : InputSpec) (obs : ObservableSpec) (e : Expr) (ctx : TypeContext) (predSat : PredSat) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime R S →
    inputsConformSpec S μ₁ ρ₁ θ₁ →
    inputsConformSpec S μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →
    runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat R S μ₁ ρ₁ θ₁ →
    consistentRegimeSpec predSat R S μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat R S μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs ctx S R μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
    terminatesTo e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

-- Step theorem: context-driven, does not mention S or obs.
theorem StepFR
  (ctx : TypeContext) (R : Regime) (e : Expr) : Prop :=
  ∀ run0 run1, runsInstantiate ctx R run0 run1 →
    agreeOnClean ctx R run0 run1 → -- includes clean-location agreement
    stepPreservesAgreement ctx R e run0 run1

-- Derivation: StepFR implies top-level FR (under the standard premises).
theorem StepFR_to_FR
  (S : InputSpec) (obs : ObservableSpec) (ctx0 : TypeContext) (e : Expr)
  (R : Regime) (res : TypeResult) (predSat : PredSat) :
  ctxMatchesInputSpec S ctx0 →
  typecheck ctx0 e = .ok res →
  ObsConstraints obs res →
  StepFR ctx0 R e →
  FaultRobustness S obs e ctx0 predSat
```

The proof structure is:
1) Use `S` to derive the initial context agreement required by the step theorem.
2) Use `StepFR` inductively to propagate agreement through syntax.
3) Use `obs` and clean typing to conclude observable equality.

## Summary

Switching from NI to FR aligns the proof with the language goal: fault
propagation with predicate-based de-poisoning. It weakens the global
independence requirement, clarifies the role of the input spec, and removes the
need for overly strong step-level quantification in chaining proofs.

## Additional Considerations

This section covers issues not part of the NI→FR motivation, but still required
to complete the FR formulation.

### Reference values vs heap contents

**Motivation.** Agreement on reference values (addresses) does not imply
agreement on the heap contents they point to. In the Lean model this is
explicit: `agreeValueUnder` for refs only relates addresses via locset
realization, while `agreeLocUnder` is the definition that actually compares heap
cells (see `src/poison-lang/LeanProofs/NonInterference.lean`). Therefore
“agree-on-clean” must track clean *locations* separately from clean *reference
values*.

**Proposal.** In the step theorem, require `agreeLocUnder` for locations typed
clean under the current regime, and do **not** treat a clean ref return (or
`agreeValueUnder` on a ref) as evidence about heap contents. Any rule that needs
heap-content agreement must explicitly use the clean-location agreement
relation. A clean ref to a poisoned location should still dereference to a
poisoned result.

### Allocation and write alignment

When new locations are introduced, agreement can only be required if the two
runs both realize the location and store values that are clean (or de-poisoned)
under the current regime. This is a proof obligation for `ref`, `:=`, and any
rule that updates heap-typing information.

Suggested direction: treat this as evidence for *agreement on clean locations*:
require (1) realization in both runs, and (2) agreement on the stored value
under `R`. Only then can the new location enter the agree-on-clean relation.
In Lean terms, this means you only add `(l, qt)` to the clean-location agreement
when you can build an `agreeLocUnder ... (l, qt)` witness, i.e., proofs of
`θ₁.lookup l = some a₁`, `θ₂.lookup l = some a₂`, `μ₁.lookup a₁ = some n₁`,
`μ₂.lookup a₂ = some n₂`, and `agreeValueUnder ... qt (Value.num n₁)
(Value.num n₂)`. For allocations, these facts come from the post-step
realization maps (via `wfExtendsMap`), and for writes they come from the updated
heap and the agreement proof for the written value. If you cannot construct this
witness, the location must stay out of the clean-agreement set.

### De-poisoning and guard regimes

**Motivation.** De-poisoning is the operational meaning of validation: if a
guard is true under a regime `R`, the value becomes clean and may influence
observables. FR therefore requires that guard-true implies *agreement*, not just
clean typing.

**Proposal.** Any rule that marks a value clean based on `R` must feed directly
into the agreement relation. Concretely, when typing says a value is clean under
`R`, the step theorem should be able to derive an `agreeValueUnder` proof for
that value.
One practical pattern is to apply the step theorem to the subexpression that
computes the value (e.g., in `let x = e1 in e2`, first prove agreement for the
result of `e1`, then use that to add `x` as clean for `e2`). If you cannot derive
`agreeValueUnder`, the value must remain poisoned in the agreement relation, and
observable equality cannot rely on it.

**Caveat.** `agreeValueUnder` currently enforces equality for `poisoned` values
with `no_pred`. As a result, a “faulty” input cannot be modeled by simply
marking it poisoned unless it also carries a guard tag with `R(k) = false`. This
is stronger than necessary but sound; the intended way to allow arbitrary
variation is to attach a guard and let the regime disable it.

### Ghost locations and realisation maps (design check)

**Motivation.** Logical locations in the typing context may be unrealised in a
particular run. Requiring heap-content agreement for such ghost locations is
both unnecessary and unprovable. FR only needs agreement where a location is
actually realised in both runs.

**Proposal.** Make location agreement conditional on realisation. In Lean this
is already captured by `agreeLocUnder`, which includes the `both_unrealized`
case; the step theorem should be willing to discharge ghost locations using
that constructor rather than forcing heap lookups. For locations that must
affect observables (or are otherwise promoted to “clean”), require proof that
both runs realise the location (`θ₁.lookup l = some a₁` and
`θ₂.lookup l = some a₂`) and then use `agreeLocUnder`’s `agree_values` case.
The value-typing relation (`valueHasETyp`) ensures any concrete reference
observed at runtime corresponds to a realised logical location in its locset,
so realisation proofs can be derived when the program actually produces or
dereferences a reference.

What still needs to be checked in FR:

- The new “agree-on-clean” relation must not accidentally quantify over all
  locations in the typing context without guarding on realization. If it does,
  you’ll re-introduce the ghost-location obligation and the issue becomes real
  again.

## Implementation Considerations

- **Trusted inputs vs `ctxMatchesInputSpec`.** The current `ctxMatchesInputSpec`
  forces any context entry not in `S` to be poisoned with `no_pred`, which makes
  the trusted set `T` effectively empty. To realize FR as stated, either relax
  `ctxMatchesInputSpec` (or introduce a variant) to allow clean entries outside
  `S`, or explicitly interpret `T` as empty in the initial context.
- **Agreement on poisoned values.** `agreeValueUnder` enforces equality for
  poisoned values with `no_pred`. This is stronger than “poisoned may differ.”
  Ensure `agreeOnClean` only ranges over items typed clean under `R`; otherwise
  poisoned, predicate-free values might be unintentionally constrained.
