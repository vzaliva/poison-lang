# `vlet` scoping: restoring `varEnv` vs. post-`ctx` invariants

This note explains a proof obligation that appears in the fault-robustness step theorem for:

```
Expr.vlet x e1 e2
```

in `LeanProofs/FaultRobustnessProofs.lean` (see the `hcwr₀_final` / `hcwr₁_final` obligations inside `stepFR_vlet`).

## The core mismatch

Operationally (`LeanPoison/BigStep.lean`), `vlet`:

1. evaluates `e1` in the current configuration, producing an intermediate config `cfg₁` and value `v₁`,
2. evaluates `e2` in `cfg₁` but with the runtime environment extended by `x ↦ v₁`,
3. **restores the original runtime environment** (lexical scoping), while **keeping memory changes** from evaluating `e2`.

So the final configuration has:

- `final.varEnv = cfg₁.varEnv` (restored outer environment)
- `final.memory = cfg₃.memory` (post-`e2` memory)

On the typing side (`LeanPoison/Typecheck.lean`), `typecheckVlet`:

1. typechecks `e1`, producing `res1`,
2. typechecks `e2` in a context `ctx'` that extends the typing environment with `x : res1.qualType`,
3. returns `res2` as the final result (its regime/memEnv/tagEnv/next* are threaded from `e2`).

The post-context used by step theorems is `ctxAfter ctxᵢ res`, whose `varEnv` is the *outer* `ctxᵢ.varEnv` (it does not include the let binder), but whose `regime` is the *post-`e2`* regime.

## Why propagate `regime` through `vlet` (even though the binder is scoped)

Although the `vlet` binder does not escape its scope (so the post-context does not keep it in `varEnv`), it is still important that the post-context **does** keep the *post-`e2`* `regime`:

1. **Write-driven invalidation.**
   In the typechecker, heap writes (e.g. `assign`) call `invalidateTagDeps` / `invalidateRegimeDeps` to drop regime entries for tags whose dependency sets intersect the written locset.
   If `e2` performed writes that might affect predicate truth for *outer* variables/locations, keeping the pre-`vlet` regime would be unsound: it could continue to interpret tags whose truth may have changed.

2. **Control-flow joins and other conservative regime refinement.**
   Even without writes, typing can conservatively drop regime information (e.g. by joining regimes across branches), and those “knowledge losses” should persist after the scope exits; otherwise the post-context could claim regime knowledge that is not justified after typing `e2`.

3. **Boundedness / non-leakage of fresh internal tags.**
   The regime has a `bound` that ensures it only interprets input/spec tags; internal fresh tags (generated during typing) are outside the regime domain.
   Propagating the regime through `e2` does not “leak” new internal tags into the regime (they remain out of domain), but *does* correctly reflect that existing interpreted tags might have been invalidated.

Informally: `vlet` restores *names* but must not restore *knowledge* about predicate tags that `e2` may have invalidated.

## Why this shows up as a `consistentWithRegime` problem

The step theorem tracks:

```
consistentWithRegime predSat R ctx μ ρ θ
```

which requires (among other things) `varsRegime` for every variable in `ctx.varEnv` whose guard tag is interpreted by `R`.

For variables with `guardClosure` predicates, `varsRegime` links regime truth to predicate satisfaction:

- if `R(k) = true`, then `qtypPredHolds predSat qt μ v`
- if `R(k) = false`, then `¬ qtypPredHolds predSat qt μ v`

Crucially, `qtypPredHolds` depends on the **current memory** `μ` (through `predSat k μ v`).

At the end of `vlet`, we must show `consistentWithRegime` for:

- the **outer** typing environment (since the binder is out of scope),
- the **restored** runtime `varEnv` (outer),
- the **post-`e2`** memory (inner),
- the **post-`e2`** regime.

This is a “scope exit stitch”: we have to re-establish variable-regime consistency for *outer* variables, but in a potentially-changed heap.

## How shadowing interacts with the scoping stitch

The scoping stitch becomes significantly harder if the let binder **shadows** an existing outer variable name.

If the binder name `x` is already present in the outer typing environment, then the post-context `ctxAfter ctxᵢ res` still contains an entry for `x` (the *outer* one), but:

- `e2` was typed under `ctx'` where `x` refers to the *inner* let-bound type `res1.qualType`, and
- `e2` was evaluated under an environment where `x` refers to the *inner* let-bound runtime value `v₁`,
- while the final configuration restores the *outer* runtime binding for `x`.

So in the shadowing case, IH2 facts for `e2` about `x` are about the *inner* `(type,value)` pair, but the final `consistentWithRegime` obligation for `x` is about the *outer* `(type,value)` pair.

That mismatch forces the proof to “switch back” to pre-`e2` information (e.g. via IH1), and *that* is when memory-transport / predicate-stability issues appear.

If shadowing is forbidden (the planned direction; see `doc/vlet-shadowing.md`), then the binder name `x` does **not** appear in `ctxᵢ.varEnv`, hence also not in `ctxAfter ctxᵢ res`. In that setting:

- the final `consistentWithRegime` obligation ranges only over variables `y ≠ x`, and
- IH2 already provides the required `varsRegime` facts at the **post-`e2` memory** (the one we need), and
- the runtime `varEnv` restoration can be handled by simple lookup-transport lemmas for `y ≠ x`.

In other words: with no shadowing, the scoping stitch can (and should) be discharged using IH2 plus “lookup unaffected by update/restore”, without any need to transport predicate facts across a memory change.

## If shadowing is allowed: where predicate-stability enters

When shadowing is allowed, the `y = x` case in the final `consistentWithRegime` proof can force us to use pre-`e2` regime-consistency facts about the *outer* binding for `x`. Those facts are naturally stated over the **pre-`e2` memory**, while the final obligation is over the **post-`e2` memory**.

To bridge that gap for `guardClosure` predicates, one needs a predicate-stability principle:

```
predSat k μ₁ v ↔ predSat k μ₂ v
```

under hypotheses that `μ₁` and `μ₂` agree on the predicate’s dependency locset `deps(k)`.

The project already includes the intended axiom for this as `PredSatLaws.mem_monotone` in `LeanProofs/FaultRobustness.lean`, but applying it requires a “write footprint” bridge that connects:

- the typechecker’s dependency tracking and invalidation (`extractDepsFromPred`, `invalidateTagDeps`, `invalidateRegimeDeps`), and
- the operational semantics’ actual writes (showing the post-`e2` memory equals the pre-`e2` memory on all locations in `deps(k)` whenever `k` remains interpreted by the post-`e2` regime).

Without such a bridge, keeping a tag `k` interpreted by the regime after `e2` while `e2` actually wrote into `deps(k)` would be a soundness bug (regime would claim stable knowledge about a predicate whose truth could have changed).

## Recommendations

1. **Forbid shadowing (preferred).**
   This removes the problematic “binder name returns” case, and turns the `vlet` scoping stitch into a proof engineering task:
   reuse IH2’s `consistentWithRegime` and transport the runtime lookup facts across `varEnv` restoration for names `y ≠ x`.

2. **Keep propagating `regime` (as today).**
   Even with shadowing forbidden, propagating the post-`e2` regime remains necessary for soundness because invalidations and conservative drops inside `e2` must persist after scope exit.

   If proof simplicity is preferred over precision, a sound (but imprecise) alternative is to **weaken** the regime at `vlet` exit even further (e.g. drop additional entries, or even reset to an “unknown”/empty regime). This makes downstream `consistentWithRegime` obligations easier (fewer interpreted tags), but also reduces the usefulness of regime-based clean-under-R reasoning and agreement guarantees.

3. **Only if shadowing remains allowed: make the write/deps bridge explicit.**
   If shadowing must be supported, then finishing the `vlet` proof likely requires a dedicated lemma family that ties:
   (i) typing-time invalidation of tags based on written locsets, to
   (ii) runtime memory agreement on the dependencies of tags that survive.
   This is more than a local proof detail: it is the central soundness argument that the regime/invalidation mechanism correctly tracks when predicate truth might change due to heap writes.
