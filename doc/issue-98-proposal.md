## Issue #98: `stepFR_ite` is false under regime-aware `typecheckIf`

Original issue: `https://github.com/vzaliva/poison-lang/issues/98`

This note proposes a proof-level fix: **replace the current spec-indexed regime
consistency premise (`consistentRegimeSpec`) with a context-indexed, per-run
runtime–regime consistency premise (`consistentRuntimeRegime`)**. This makes
regime-guided branch selection sound with respect to runtime execution.

---

## Root Cause

`typecheckIf` has a regime-aware “depoisoning” path: when `matchGuard e1 Γ σ`
succeeds with a tag `k` and `R.lookup? k = some b`, the typechecker **commits to
one branch** (then if `b=true`, else if `b=false`) and does not conservatively
join with the other branch.

Runtime evaluation still chooses the branch based on the *actual* boolean result
of the guard. But current `StepFR` hypotheses do not enforce that the guard’s
runtime truth agrees with `R(k)`. Therefore, two admissible runs can take
different branches and return different outputs even when the typing result is
clean-under-`R`, contradicting `StepFR`’s “clean results must agree” postcondition.

This is exactly the missing link that `PredSatLaws.match_iff` was intended to
support: it relates `matchGuard` + evaluation of the guard to an abstract
predicate relation `predSat k μ v`, but the current step theorem does not assume
that runtime states satisfy/refute the predicate according to the regime.

### Counterexample (Issue #98) and why it is ruled out
The GitHub issue instantiates a context with `x : int` carrying a `guardClosure`
predicate tagged `k` (e.g. predicate `x > 0`), sets `R.lookup? k = some true`,
but considers runs with `x = 0`. Those runs make the predicate false at runtime,
so they violate the proposed `consistentRuntimeRegime` and are excluded (as
intended).

---

## Proposed Solution: Strengthen Theorem Assumptions

### Intent
Interpret the regime `R` as a restriction on admissible executions: if `R`
assigns a truth value to a guard tag, then runs considered by FR must satisfy
the corresponding runtime predicate truth for that tag.

### Final proposed assumption: `consistentRuntimeRegime` (replaces `consistentRegimeSpec`)

Add a new assumption to **all FR statements**:
- step-level theorems (`StepFR` and `stepFR_*` lemmas), and
- the top-level FR statement (`FaultRobustnessSpec`),

so that any proof relying on regime-guided branch commitment can assume the
runtime actually respects the regime.

1) **`PredSatLaws predSat`**, so we can relate `matchGuard` + evaluation of the
condition to `predSat`.

2) A new runtime–regime consistency predicate (name suggestion from issue
discussion):  
`consistentRuntimeRegime predSat R ctx μ ρ θ`.

Key design point: `consistentRuntimeRegime` must only constrain tags the regime
actually interprets (i.e. tags `k` with `R.lookup? k = some b`). For internal
tags where `R.lookup? k = none`, it imposes no constraint.

To make this precise and reusable in proofs, we introduce two *elementwise*
predicates (variable and location) that extend the existing
`varsRegime`/`locsRegime` idea with exactly one extra case:
**unknown regime ⇒ no constraint**. Then `consistentRuntimeRegime` is just a
`List.Forall` over the typing context’s environments.

```lean
inductive varRuntimeRegime (predSat : PredSat) (R : Regime) (μ : Memory) (ρ : VarEnv) :
    (Name × QTyp) → Prop where
  | noPred_ok (entry) (hpred : qtypGuardTag entry.snd = none) :
      varRuntimeRegime predSat R μ ρ entry
  | guardOnly_ok (entry) (k) (hgo : entry.snd.pred = Predicate.guardOnly k) :
      varRuntimeRegime predSat R μ ρ entry
  | guardClosure_unknown (entry) (k arg pred_body var_env)  -- R does not interpret k
      (hclos : entry.snd.pred = Predicate.guardClosure k arg pred_body var_env)
      (hregime : R.lookup? k = none) :
      varRuntimeRegime predSat R μ ρ entry
  | guardClosure_known (entry) (k arg pred_body var_env) (v) (b)  -- R(k)=b
      (hclos : entry.snd.pred = Predicate.guardClosure k arg pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hvar : ρ.lookup entry.fst = some v)
      (hconsist :
        (b = true  → qtypPredHolds predSat entry.snd μ v) ∧
        (b = false → ¬ qtypPredHolds predSat entry.snd μ v)) :
      varRuntimeRegime predSat R μ ρ entry

inductive locRuntimeRegime (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) :
    (Loc × QTyp) → Prop where
  | noPred_ok (entry) (hpred : qtypGuardTag entry.snd = none) :
      locRuntimeRegime predSat R μ θ entry
  | guardOnly_ok (entry) (k) (hgo : entry.snd.pred = Predicate.guardOnly k) :
      locRuntimeRegime predSat R μ θ entry
  | guardClosure_unknown (entry) (k arg pred_body var_env)  -- R does not interpret k
      (hclos : entry.snd.pred = Predicate.guardClosure k arg pred_body var_env)
      (hregime : R.lookup? k = none) :
      locRuntimeRegime predSat R μ θ entry
  | guardClosure_known (entry) (k arg pred_body var_env) (a n) (b)  -- R(k)=b
      (hclos : entry.snd.pred = Predicate.guardClosure k arg pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hreal : θ.lookup entry.fst = some a)
      (hmem : μ.lookup a = some n)
      (hconsist :
        (b = true  → qtypPredHolds predSat entry.snd μ (Value.num n)) ∧
        (b = false → ¬ qtypPredHolds predSat entry.snd μ (Value.num n))) :
      locRuntimeRegime predSat R μ θ entry

inductive consistentRuntimeRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop where
  | intro
      (h_locs : List.Forall (locRuntimeRegime predSat R μ θ) ctx.memEnv.toList)
      (h_vars : List.Forall (varRuntimeRegime predSat R μ ρ) ctx.varEnv.toList) :
      consistentRuntimeRegime predSat R ctx μ ρ θ
```

Notes:
- Under `wfRegime R s`, every spec tag has `R.lookup? k = some b`, so the
  “unknown” constructors never apply to spec entries.
- When `regimeBounded R` holds (already a standard FR premise), any tag
  `k ≥ R.bound` satisfies `R.lookup? k = none`, so fresh/internal tags are
  automatically discharged by the `guardClosure_unknown` constructors. No
  separate “`k ≥ R.bound` case” is required in the definition.

### What changes in `FaultRobustnessSpec`
Today, the top-level spec assumes *spec-indexed* regime consistency:
`consistentRegimeSpec predSat R s μ ρ θ` (i.e. `List.Forall ... s.vars.toList` and
`s.locs.toList`).

Under this proposal, we instead assume *context-indexed* runtime–regime
consistency:

```lean
consistentRuntimeRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁ →
consistentRuntimeRegime predSat ctx.regime ctx μ₂ ρ₂ θ₂ →
```

This is a deliberate strengthening:
- `StepFR` is context-indexed, and `matchGuard` may pick an “owner” entry that is
  present in `ctx` but not listed in the input spec `s`. The step proof needs
  regime consistency for whichever owner entry `matchGuard` identifies.
- With `wfRegime ctx.regime s`, any tag where `ctx.regime.lookup? k = some b`
  is a spec tag, so the new premise still only constrains the regime’s intended
  domain. It just enforces it for *all occurrences* of those tags in `ctx`
  (including trusted/unlisted entries), which is exactly what makes regime-aware
  branch commitment sound.

### How this fixes `stepFR_ite`
In the regime-known case:

- `matchGuard e1 Γ σ = .ok (k, deps)` gives a specific tag `k`.
- By construction, `matchGuard` only succeeds when the tag `k` comes from some
  `guardClosure` predicate in the typing environments (`σ` or `Γ`). Together
  with `runtimeInstantiatesCtx`, this yields the “owner” witness required by
  `PredSatLaws.match_iff` (the variable or location whose predicate determines
  the guard), plus the corresponding runtime value `v`.
- If `R.lookup? k = some b`, `consistentRuntimeRegime` forces predicate truth
  for that owner value to match `b`, i.e. it yields `predSat k μ v` when `b=true`
  (and `¬ predSat k μ v` when `b=false`).
- Applying `PredSatLaws.match_iff` to the guard evaluation shows the guard’s
  boolean result equals `b` in each run.
- Therefore both runs take the same branch (then if `b=true`, else if `b=false`),
  so the typechecker’s branch-commitment result matches runtime behavior, and
  output agreement follows (by IH on the chosen branch + clean agreement conditions).

This removes the counterexample by construction: the “guard is false while
R(k)=true” executions are no longer admissible.

### Expected proof refactor surface
To adopt this fix cleanly, the following proof-layer changes are expected:
- Strengthen `StepFR` (or just `stepFR_ite`/`stepFR_while`) to assume:
  - `PredSatLaws predSat`, and
  - per-run `consistentRuntimeRegime predSat ctx.regime ctx μ ρ θ`.
- Update `FaultRobustnessSpec` to assume (per run) `consistentRuntimeRegime ...`;
  this replaces the current `consistentRegimeSpec` premises and aligns the
  top-level statement with the step theorem’s premises.
- Show `consistentRuntimeRegime` is preserved across `ctxAfter` (new internal
  tags are outside the regime domain under `regimeBounded`).
- Use `consistentRuntimeRegime` everywhere (step and top-level), and delete
  `consistentRegimeSpec` once no longer referenced.
