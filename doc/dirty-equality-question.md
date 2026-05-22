# Cross-run agreement on dirty (poisoned) critical inputs

**Status:** resolved by Direction B. Critical-input agreement is now filtered by
`qtypCleanUnder R`; dirty critical entries no longer make the top-level
fault-robustness premise unsatisfiable.

## Original issue

The intended semantics for critical-input agreement is:

- **Clean input** (`R(k)=true`): both runs must hold agreeing values.
- **Dirty input** (`R(k)=false`): both runs may hold different payload values.

The previous formalization required `agreeVarUnder` and `agreeLocUnder` for every
critical entry in `S`, with no clean/dirty filter. For a dirty base-typed
critical variable under a false guard, `agreeValueUnder` has no constructor that
permits arbitrary payload disagreement. That made
`agreeOnCriticalInputsUnderRegimeSpec` unsatisfiable and made
`FaultRobustnessSpec` vacuous for such faulty-input worlds.

A temporary vacuity witness used to isolate that over-constraint has been
removed because the vacuity theorem is no longer part of the intended codebase
after this fix.

## Resolution

`agreeOnCriticalInputsUnderRegimeSpec` now mirrors the step-level invariant
`agreeOnClean`: it requires agreement only for critical entries that are clean
under the selected guard regime.

```lean
∀ x qt, s.vars.lookup x = some qt → qtypCleanUnder R qt →
  agreeVarUnder predSat R μ₁ ρ₁ μ₂ ρ₂ θ₁ θ₂ (x, qt)
```

and analogously for critical logical locations.

Dirty critical entries with `guardClosure` predicates remain constrained by
`consistentRegimeSpec`, which requires predicate satisfaction to agree with the
regime truth value in each run. Dirty guard-only entries intentionally impose no
predicate-satisfaction condition. In both cases, dirty payloads are not forced
to agree by the top-level critical-input agreement premise.

`agreeValueUnder` remains unchanged; in particular, there is no `withPred_false`
constructor. This preserves the existing equality-extraction lemmas for clean
values and keeps the bridge to the step theorem direct.
