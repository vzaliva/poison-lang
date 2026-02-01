## Issue #98: `stepFR_ite` is false under regime-aware `typecheckIf`

Original issue: `https://github.com/vzaliva/poison-lang/issues/98`

This note proposes a proof-level fix: **add a context-indexed, per-run
runtime–regime consistency premise (`consistentWithRegime`)** to `StepFR` and
`FaultRobustnessSpec`. This makes regime-guided branch selection sound with
respect to runtime execution. It also proposes a necessary follow-up for
mutation: make regime facts **monotone** by invalidating them during typechecking
when heap writes occur.

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

### Additional issue: regime facts can become stale under mutation
`wfRegime R s` + `consistentWithRegime ... R ...` only justify that `R(k)=b`
matches runtime predicate truth **at the time the tag is validated** (i.e. when
the tag's owning value and its dependencies have not changed since the regime was
seeded).

In an imperative language, that is not automatically preserved:
- guard predicates may depend on heap locations (`Deps`), and
- assignments can update those locations (or other locations the predicate reads).

If a dependency changes, the predicate's truth can flip, and treating `R(k)=b`
as a permanent oracle becomes unsound even if the initial state was consistent.

#### Required follow-up: make the regime mutable and monotone (invalidate to `none`)
To keep regime-aware branch commitment sound in the presence of writes, treat the
regime `R` as a cache of predicate outcomes that can be invalidated:

> When the program writes to a location that may affect a predicate tagged `k`,
> drop the regime entry (`R.lookup? k := none`), forcing later uses to fall back
> to conservative typing.

This is already the intended policy for tag knowledge in `tagEnv` (via
`invalidateTagDeps`). The key difference is that `typecheckIf`/`typecheckWhile`
consult `R` directly, so `R` must be invalidated too (or guarded by the same
invalidity information), otherwise stale `R(k)` can still drive branch commitment.

This change is not just proof-level: **typechecking must be allowed to update
`ctx.regime`**, and the typing rules that write to memory must invalidate it
(similar to how they already invalidate `tagEnv`).

Implementation sketch (high level):
- Extend the typechecker infrastructure so a typing step can return an updated
  regime (e.g. add `regime' : Regime` to `TypeResult` and update `ctxAfter` to
  copy it, or compute the invalidated regime directly in each rule and thread it
  through the context).
- Add an invalidation operation for regimes. The conservative sound choice is:
  **on any heap write, drop all regime entries for tags `< R.bound`** (set them
  to `none`). A more precise dependency-based invalidation is possible, but it
  requires a sound and proven connection between predicate truth and extracted
  dependencies; we are not assuming that here.
- Update all typing rules with heap effects (at least `assign`, and any
  extern/primitive that may write) to apply this regime invalidation in lockstep
  with `invalidateTagDeps` (maybe make it par of it).

Effect on this proposal:
- The definition of `consistentWithRegime` can stay the same.
- **`wfRegime` is an initial-only property.** The current definition requires R
  to be defined for *all* spec tags (`∀ k, k ∈ tags → (R.lookup? k).isSome`).
  After invalidation, some entries become `none`, breaking this conjunct.
  Therefore, `wfRegime R s` holds only for the *initial* seeded regime and is
  not a step invariant.
- **Weaker step invariant: `wfRegimePartial`.** For step proofs, introduce:

  ```lean
  def wfRegimePartial (R : Regime) (s : InputSpec) : Prop :=
    let tags := inputSpecTags s
    (∀ k, k ∈ tags → k < R.bound) ∧           -- spec tags below bound (preserved)
    (∀ k, (R.lookup? k).isSome → k ∈ tags)    -- R only defined for spec tags (preserved)
  ```

  This drops the "R defined for all spec tags" conjunct. Invalidation preserves
  `wfRegimePartial`: setting `R.lookup? k := none` maintains both conjuncts.

- **Proof flow:**
  1. Top-level starts with `wfRegime R₀ s` (initial, full coverage)
  2. `wfRegime` implies `wfRegimePartial` (trivially)
  3. Step proofs assume/preserve `wfRegimePartial` + `Regime.monotoneStep R₀ R`
  4. `consistentWithRegime` only needs `wfRegimePartial` (for the "R only knows
     spec tags" direction) and doesn't require full coverage

- Preservation obligations become more realistic: when a write may break a
  predicate, the corresponding `R(k)` is removed, so subsequent reasoning never
  relies on a possibly-stale regime fact.
- The existing proof lemma `regime_immutability` must be replaced by a
  **monotonicity** lemma, e.g. `regime_monotone`, stating that typechecking can
  only *drop* regime entries (never change a `some b` to `some b'` or introduce a
  new `some`).

Lean sketch:

```lean
def Regime.monotoneStep (R R' : Regime) : Prop :=
  R'.bound = R.bound ∧
  ∀ k b, R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)

-- Replaces `regime_immutability` (which becomes false once typing invalidates `R`).
lemma regime_monotone (ctx : TypeContext) (res : TypeResult) :
  Regime.monotoneStep ctx.regime (ctxAfter ctx res).regime := by
  ...
```

### What changes in `FaultRobustnessSpec` and `StepFR`

**Top-level (`FaultRobustnessSpec`):** The top-level spec *keeps* the existing
spec-indexed regime consistency premise:

```lean
consistentRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ →
consistentRegimeSpec predSat ctx.regime s μ₂ ρ₂ θ₂ →
```

This is user-facing and intuitive: it says the runtime values of spec entries
must match the regime's predicate-truth assignments.

**Step-level (`StepFR`):** The step theorem uses the new context-indexed
predicate:

```lean
consistentWithRegime predSat ctx.regime ctx μ ρ θ →
```

This is what the step proofs actually need: `matchGuard` may pick an "owner"
entry that is present in `ctx` but not listed in the input spec `s`.

**Bridge lemma:** A lemma connects the two formulations at the initial context:

```lean
lemma consistentRegimeSpec_implies_consistentWithRegime
    (h_spec : consistentRegimeSpec predSat R s μ ρ θ)
    (h_match : ctxMatchesInputSpec s ctx)
    (h_wf : wfRegime R s)
    (h_bounded : regimeBounded R) :
    consistentWithRegime predSat R ctx μ ρ θ
```

This works because:
- At program start, `ctxMatchesInputSpec s ctx` ensures spec entries are in `ctx`
- By `wfRegime R s`, tags in R come from spec entries
- Non-spec entries in `ctx` have fresh tags (not in R), so they're vacuously
  handled by `consistentWithRegime`

**Proof flow:**
1. Top-level assumes `consistentRegimeSpec` (intuitive for users)
2. Bridge lemma derives initial `consistentWithRegime`
3. Step proofs assume and preserve `consistentWithRegime` (with regime
   invalidation on writes)
4. Final result follows from the step theorem chain

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
- `FaultRobustnessSpec` keeps its existing `consistentRegimeSpec` premises.
- Add the bridge lemma `consistentRegimeSpec_implies_consistentWithRegime` to
  derive the initial `consistentWithRegime` from `consistentRegimeSpec`.
- Show `consistentWithRegime` is preserved across `ctxAfter`. With mutation,
  this requires allowing typechecking to update `ctx.regime` and proving a
  `regime_monotone` property (regime entries can only be dropped to `none`).
- Update any proof steps that currently use `regime_immutability` to use
  `regime_monotone` instead, and thread the updated regime through `ctxAfter`
  (post-context should use the post-regime, not the pre-regime).

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

The challenging case is heap mutation: after a write, previously-true regime
facts (`R.lookup? k = some b`) may no longer reflect the current predicate truth.

The proposal addresses this by making regime entries *monotone* and invalidating
them on writes. In the conservative variant (invalidate all spec-tag regime
entries on any heap write), `R.lookup? k ≠ none` will be false for all spec tags
after the first heap update. That makes `consistentWithRegime` trivially
preserved after heap writes, and ensures later regime-aware branch commitment is
never driven by stale information.
