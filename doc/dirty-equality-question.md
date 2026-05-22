# Cross-run agreement on dirty (poisoned) critical inputs

**Status:** confirmed issue — spec-level premise is over-constrained for the faulty-input case.
Not a fundamental flaw in the core type system.

## Problem

The intended semantics for critical-input agreement is:
- **Clean input** (R(k)=true): both runs must hold the same value and satisfy the predicate.
- **Dirty input** (R(k)=false): both runs must fail the predicate, but may otherwise hold *different* values.

The current formalization does not realize the "may differ" half. For a dirty base-typed critical
variable, `agreeOnCriticalInputsUnderRegimeSpec` cannot be satisfied, making `FaultRobustnessSpec`
vacuously true in the faulty world rather than substantively guaranteeing output agreement.

## Analysis

The unsatisfiability chain:

1. **`wfInputSpecVars`** (`FaultRobustness.lean:225`): every dirty critical variable (`qt.poison=true`)
   must carry a guard predicate (`hasGuardTag qt.pred = true`).

2. **`ctxMatchesInputSpec` + `runtimeInstantiatesCtx`** (`FaultRobustness.lean:266`,
   `TypeSafety.lean:1164`): every critical variable is bound in both runtime environments, so
   `agreeVarUnder.both_none` is never applicable.

3. **`agreeValueUnder`** (`FaultRobustness.lean:476`): has constructors for clean equality
   (`clean_eq_nonref_nonarrow`, `withPred_true_eq`) and for dirty *function* values
   (`dirty_internal_arrow/parrow`), but **no constructor for a dirty base or ref value with R(k)=false**.

4. Therefore `agreeVarUnder.agree_values` (the only applicable branch) requires `agreeValueUnder`,
   which is underivable for a bound dirty base value.

5. `agreeOnCriticalInputsUnderRegimeSpec` = `List.Forall agreeVarUnder s.vars.toList` (no
   clean/dirty filter) → **unsatisfiable** when any critical variable is dirty.

6. `FaultRobustnessSpec` takes this as a premise → **vacuously true** for dirty critical inputs.

Note: the step-level invariant `agreeOnClean` is already correctly shaped — it filters by
`qtypCleanUnder R`, so the per-step FR proofs never need agreement on dirty entries. The
overconstraint is only in the top-level spec premise.

**Machine-checked confirmation:** `LeanProofs/DirtyEquality.lean` formally proves the vacuity.
The chain above is verified by four lemmas culminating in
`FaultRobustnessSpec_vacuous_of_dirty_guard_false_int_var`, which derives `FaultRobustnessSpec`
via `False.elim` — the `agreeOnCriticalInputsUnderRegimeSpec` premise is refuted directly from
the other hypotheses. The file compiles with no errors and no `sorry`.

## Suggested fix directions

**Direction A — Add a `withPred_false` constructor to `agreeValueUnder`.**
A new constructor would make agreement trivially satisfiable for dirty inputs while placing no
constraint on the actual runtime values. It should require at minimum `qt.poison = true` (or
`¬ qtypCleanUnder R qt`), not merely `R(k)=false`; without that guard, equality-extraction lemmas
can no longer dismiss the case from `qt.poison = false`. Even with that guard, this broadens a
core relation used throughout the proof stack — all downstream lemmas that derive equality from
`agreeValueUnder` must be audited and updated.

**Direction B — Filter `agreeOnCriticalInputsUnderRegimeSpec` by `qtypCleanUnder R` (preferred).**
Mirror `agreeOnClean`: require `agreeVarUnder` only for critical entries that are clean under R.
Dirty critical entries with `guardClosure` predicates are already handled by `consistentRegimeSpec`
(which enforces "both fail the predicate"); `guardOnly` entries intentionally impose no
predicate-satisfaction condition, so that claim does not extend to them. This keeps `agreeValueUnder`
tight (equality remains extractable without guards) and matches the step-level invariant shape,
minimising proof changes elsewhere. The preferred concrete shape is:

```lean
List.Forall
  (fun entry => qtypCleanUnder R entry.snd →
    agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ entry)
  s.vars.toList
```

and analogously for locations. With this shape the existing bridge to `agreeOnClean` becomes more
direct: the `hclean` hypothesis at the critical-entry branch is already available.
