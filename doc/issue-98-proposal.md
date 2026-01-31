## Issue #98: `stepFR_ite` is false under regime-aware `typecheckIf`

Original issue: `https://github.com/vzaliva/poison-lang/issues/98`

This note proposes a proof-level fix: **add a context-indexed, per-run
runtime–regime consistency premise (`consistentWithRegime`)** to `StepFR` and
`FaultRobustnessSpec`. This makes regime-guided branch selection sound with
respect to runtime execution.

---

## Root Cause

`typecheckIf` has a regime-aware "depoisoning" path: when `matchGuard e1 Γ σ`
succeeds with a tag `k` and `R.lookup? k = some b`, the typechecker **commits to
one branch** (then if `b=true`, else if `b=false`) and does not conservatively
join with the other branch.

Runtime evaluation still chooses the branch based on the *actual* boolean result
of the guard. But current `StepFR` hypotheses do not enforce that the guard's
runtime truth agrees with `R(k)`. Therefore, two admissible runs can take
different branches and return different outputs even when the typing result is
clean-under-`R`, contradicting `StepFR`'s "clean results must agree" postcondition.

This is exactly the missing link that `PredSatLaws.match_iff` was intended to
support: it relates `matchGuard` + evaluation of the guard to an abstract
predicate relation `predSat k μ v`, but the current step theorem does not assume
that runtime states satisfy/refute the predicate according to the regime.

### Counterexample (Issue #98) and why it is ruled out
The GitHub issue instantiates a context with `x : int` carrying a `guardClosure`
predicate tagged `k` (e.g. predicate `x > 0`), sets `R.lookup? k = some true`,
but considers runs with `x = 0`. Those runs make the predicate false at runtime,
so they violate the proposed `consistentWithRegime` and are excluded (as
intended).

---

## Proposed Solution: Strengthen Theorem Assumptions

### Intent
Interpret the regime `R` as a restriction on admissible executions: if `R`
assigns a truth value to a guard tag, then runs considered by FR must satisfy
the corresponding runtime predicate truth for that tag.

### Final proposed assumption: `consistentWithRegime`

Add a new assumption to **all FR statements**:
- step-level theorems (`StepFR` and `stepFR_*` lemmas), and
- the top-level FR statement (`FaultRobustnessSpec`),

so that any proof relying on regime-guided branch commitment can assume the
runtime actually respects the regime.

1) **`PredSatLaws predSat`**, so we can relate `matchGuard` + evaluation of the
condition to `predSat`.

2) A new runtime–regime consistency predicate:
`consistentWithRegime predSat R ctx μ ρ θ`.

Key design point: `consistentWithRegime` constrains **only** tags the regime
actually interprets (i.e. tags `k` with `R.lookup? k ≠ none`). For tags where
`R.lookup? k = none`, the implication is vacuously satisfied.

This formulation reuses the existing `locsRegime`/`varsRegime` predicates,
wrapping them in a conditional that fires only when the tag is in `R`'s domain:

```lean
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l qt k, ctx.memEnv.lookup l = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     locsRegime predSat R μ θ (l, qt)) ∧
  (∀ x qt k, ctx.varEnv.lookup x = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     varsRegime predSat R μ ρ (x, qt))
```

Notes:
- This reuses the existing `locsRegime`/`varsRegime` inductive predicates
  without modification.
- The precondition `R.lookup? k ≠ none` ensures we only constrain entries whose
  tags R actually interprets.
- For fresh/internal tags: `regimeBounded R` guarantees `R.lookup? k = none`
  for any `k ≥ R.bound`, so the precondition is false and the implication is
  vacuously satisfied.
- Under `wfRegime R s`, every spec tag has `R.lookup? k = some b`, so spec
  entries are constrained as intended.

### What changes in `FaultRobustnessSpec`
Today, the top-level spec assumes *spec-indexed* regime consistency:
`consistentRegimeSpec predSat R s μ ρ θ` (i.e. `List.Forall ... s.vars.toList` and
`s.locs.toList`).

Under this proposal, we instead assume *context-indexed* runtime–regime
consistency:

```lean
consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
consistentWithRegime predSat ctx.regime ctx μ₂ ρ₂ θ₂ →
```

This is a deliberate strengthening:
- `StepFR` is context-indexed, and `matchGuard` may pick an "owner" entry that is
  present in `ctx` but not listed in the input spec `s`. The step proof needs
  regime consistency for whichever owner entry `matchGuard` identifies.
- With `wfRegime ctx.regime s`, any tag where `ctx.regime.lookup? k = some b`
  is a spec tag, so the new premise still only constrains the regime's intended
  domain. It just enforces it for *all occurrences* of those tags in `ctx`
  (including trusted/unlisted entries), which is exactly what makes regime-aware
  branch commitment sound.

### How this fixes `stepFR_ite`
In the regime-known case:

- `matchGuard e1 Γ σ = .ok (k, deps)` gives a specific tag `k`.
- By construction, `matchGuard` only succeeds when the tag `k` comes from some
  `guardClosure` predicate in the typing environments (`σ` or `Γ`). Together
  with `runtimeInstantiatesCtx`, this yields the "owner" witness required by
  `PredSatLaws.match_iff` (the variable or location whose predicate determines
  the guard), plus the corresponding runtime value `v`.
- If `R.lookup? k = some b`, `consistentWithRegime` forces predicate truth
  for that owner value to match `b`, i.e. it yields `predSat k μ v` when `b=true`
  (and `¬ predSat k μ v` when `b=false`).
- Applying `PredSatLaws.match_iff` to the guard evaluation shows the guard's
  boolean result equals `b` in each run.
- Therefore both runs take the same branch (then if `b=true`, else if `b=false`),
  so the typechecker's branch-commitment result matches runtime behavior, and
  output agreement follows (by IH on the chosen branch + clean agreement conditions).

This removes the counterexample by construction: the "guard is false while
R(k)=true" executions are no longer admissible.

### Expected proof refactor surface
To adopt this fix cleanly, the following proof-layer changes are expected:
- Strengthen `StepFR` (or just `stepFR_ite`/`stepFR_while`) to assume:
  - `PredSatLaws predSat`, and
  - per-run `consistentWithRegime predSat ctx.regime ctx μ ρ θ`.
- Update `FaultRobustnessSpec` to assume (per run) `consistentWithRegime ...`;
  this replaces the current `consistentRegimeSpec` premises and aligns the
  top-level statement with the step theorem's premises.
- Show `consistentWithRegime` is preserved across `ctxAfter`.
- Use `consistentWithRegime` everywhere (step and top-level), and delete
  `consistentRegimeSpec` once no longer referenced.

---

## Proof Considerations

### Fresh tags and preservation

When the context is extended with a new entry (e.g., via `newRef` or `vlet`),
the new entry typically has a fresh tag `k ≥ ctx.nextTag`. To show
`consistentWithRegime` is preserved for this entry:

1. Assume the precondition `R.lookup? k ≠ none`.
2. Use `regimeBounded R` (which gives `R.lookup? k = none` for `k ≥ R.bound`)
   together with `regimeConsistentWithCtx` (which gives `R.bound ≤ ctx.nextTag`)
   to derive `R.lookup? k = none`.
3. Contradiction with step 1.

This discharges the obligation vacuously. The same freshness lemmas are needed
as in any formulation; the conditional structure simply localises where this
reasoning appears.

### Entries with tags in R and memory changes

The more challenging case involves entries whose tags ARE in `R`'s domain.
For these entries, `locsRegime`/`varsRegime` require:

```lean
hconsist : (b = true → qtypPredHolds predSat qt μ v) ∧
           (b = false → ¬qtypPredHolds predSat qt μ v)
```

When memory changes (e.g., via `assign`), this condition must be shown to
persist. This requires reasoning about **predicate satisfaction stability**:
if `qtypPredHolds predSat qt μ v` held before a memory change, does it still
hold after?

Key observations that may simplify this:

1. **Variable bindings are immutable**: Once bound, a variable's value does not
   change. If `matchGuard` identifies a variable as the "owner", its consistency
   is preserved trivially.

2. **Memory locations with tags in R are input spec locations**: Tags in R come
   from the input specification (by `wfRegime R s`). These locations are
   initially poisoned (`poison = true`). Assignment to a poisoned location
   requires prior de-poisoning via an `if` guard check. By the time assignment
   is permitted, the `stepFR_ite` for that guard has already established the
   regime commitment.

3. **Predicates read existing memory**: The `qtypPredHolds` relation depends on
   memory through `predSat`, which evaluates the predicate body. If predicates
   only read memory locations that existed before the change and whose values
   are unchanged, satisfaction is preserved. This "frame property" may need to
   be formalised as a law in `PredSatLaws` if not already implied.

### Potential `PredSatLaws` extension

If predicate satisfaction stability under memory extension is needed, consider
adding:

```lean
structure PredSatLaws (predSat : PredSat) : Prop where
  match_iff : ...  -- existing
  -- Predicate satisfaction is stable under memory extension:
  -- if μ ⊆ μ' (existing values preserved), satisfaction is unchanged
  frame_stable : ∀ k μ μ' v,
    (∀ a n, μ.lookup a = some n → μ'.lookup a = some n) →
    predSat k μ v ↔ predSat k μ' v
```

This formalises that predicates depend only on memory values that exist (not on
newly allocated addresses), which is semantically sound for the Poison language.
