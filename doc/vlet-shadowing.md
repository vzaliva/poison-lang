# `vlet` shadowing: why it complicates proofs, and a targeted restriction

This note explains the “shadowing” subcase that arises in `stepFR_vlet` when the let-binder name already exists in the *outer* typing environment.

## What “shadowing” means here

Shadowing occurs when the `vlet` binder name `x` is already present in the outer typing environment:

```
ctxᵢ.varEnv.lookup x = some qt_outer
```

but `typecheckVlet` constructs the inner context for `e2` by updating the typing environment:

```
ctx' = { ctxᵢ with varEnv := ctxᵢ.varEnv.update x res1.qualType, ... }
```

Semantically, `e2` runs with the runtime environment extended by `x ↦ v₁`, but the `vlet` scope exit restores the outer runtime environment, so the final runtime binding for `x` is again the *outer* one.

## Why this is hard for `consistentWithRegime`

At the end of `vlet`, the step theorem needs `consistentWithRegime` for the post-context `ctxAfter ctxᵢ res`. This post-context:

- does **not** include the let-binder (lexical scoping),
- but still includes any *outer* binding for `x` if one existed originally.

Meanwhile, the inductive hypothesis for `e2` (proved under `ctx'`) talks about `x` using:

- the **inner** type `res1.qualType` (from the updated typing environment), and
- the **inner** runtime value (the let-bound value).

So in the shadowing case (`x` already existed), IH2 facts about `x` are about the “inner” `(type,value)` pair, while the final `consistentWithRegime` obligation about `x` is about the “outer” `(type,value)` pair (after environment restoration).

This mismatch is why the `x = binder` branch becomes a special case in proofs: you cannot directly reuse the IH2 `varsRegime` fact for the final state.

## Interaction with the scoping stitch

As discussed in `doc/vlet-scoping.md`, the `vlet` “scope exit stitch” is easiest when the binder name does not appear in the post-context at all.

Shadowing is precisely the situation in which the binder name *does* appear in the post-context (via the outer binding), forcing the proof to reason about an outer `(type,value)` pair in the final state while IH2 reasons about the inner `(type,value)` pair inside `e2`.

If shadowing is forbidden, the binder name is fresh w.r.t. the outer `ctxᵢ.varEnv`, so the post-context does not mention it and the proof can proceed using only IH2 plus “lookup unaffected by update/restore” for all remaining names `y ≠ x`.

## Proposed solution: forbid only “harmful shadowing”

The proof difficulty is not caused by shadowing *per se*; it is caused by shadowing when the *outer* binding for `x` carries a **predicate that the regime interprets**, because then `consistentWithRegime` needs a `varsRegime` fact for that outer binding in the post-state.

In practice, the hard case is:

- `ctx.varEnv.lookup x = some qt_outer`,
- `qt_outer.pred` is a `guardClosure k ...` predicate, and
- `ctx.regime.lookup? k ≠ none` (i.e. `k` is in the interpreted regime domain).

If `qt_outer.pred` is `noPred` or `guardOnly`, then the `varsRegime` obligation is trivial (no predicate-stability needed). If `k` is not interpreted by the regime, the `varsRegime` obligation does not arise at all (it is gated by `R.lookup? k ≠ none`).

So a more surgical restriction is:

> Reject shadowing only when the outer binding for `x` is a `guardClosure` whose tag is interpreted by the current regime.

This preserves a large class of “rebind” idioms while removing the proof-critical corner.

Note: this criterion uses the *current* regime (`ctx.regime`). Since the typechecker’s regime threading is monotone (it can only drop entries, not add them), if a tag is not interpreted now it cannot become interpreted later inside `e2`. So checking against `ctx.regime` is sufficient for ruling out the problematic post-`e2` case.

In particular, this allows common “update via rebinding” patterns like:

```
let x = 1 in
  let x = x + 1 in
    x
```

unless the outer `x` carries an interpreted `guardClosure` predicate (the proof-critical case).

### Soundness intuition

This restriction is sound because:

1. The `varsRegime` obligation is gated by regime interpretation (`R.lookup? k ≠ none`). If the outer binding’s tag is not interpreted, no shadowing-related `varsRegime` proof obligation arises for it in the post-state.
2. Regime threading is monotone (drops only). Therefore, “not interpreted in `ctx.regime`” implies “not interpreted after typing `e1`/`e2`”, so checking the pre-`vlet` regime is a sound over-approximation.
3. For `noPred` and `guardOnly`, the `varsRegime` obligation is trivial and does not require predicate-stability arguments, so shadowing them is benign.

### Known conservatism

This check is deliberately conservative: it rejects based on the *pre-`vlet`* regime.

In principle, `e1`/`e2` could invalidate the tag `k` (via writes to `deps(k)`), so that `k` would not be interpreted in the post-`e2` regime and the problematic post-state obligation would not arise. Under the proposed check, such programs are still rejected.

This is sound but may reject some programs that would be safe; the intent here is to keep the proof story simple and robust.

## Consistency with other binders (function parameters)

`vlet` is not the only construct that introduces a scoped binding:

- function bodies are evaluated under an environment extended with the parameter binding, and then evaluation restores the caller’s `varEnv` (while keeping memory changes).

This is superficially similar to `vlet` (temporary binding + scope exit), but it differs in what the *post-state invariants* range over:

- the post-context after a function call is the caller context (it does not range over the function’s captured environment), and
- the runtime variable environment after a call is restored to the caller environment, not to the closure’s captured environment.

So “parameter name shadows a name in the closure’s captured environment” does not create the same *post-state* mismatch as `vlet` shadowing does (where the post-context mentions the shadowed outer binding by name).

However, parameter shadowing can still make *internal* proofs more awkward (similar to the inner `vlet` reasoning about the newly-bound name). For uniformity, we can either:

- keep the restriction specific to `vlet` (minimum change), or
- adopt the same “harmful shadowing” check for binders that extend an existing typing environment (e.g. reject a function parameter name if it collides with a `guardClosure` predicate in the captured typing environment whose tag is interpreted by the regime).

If the long-term goal is “binder discipline is consistent across the language”, extending the check to function parameters is worth considering, but it is not strictly required to remove the `stepFR_vlet` proof corner.

### Proposed implementation approach

1. **Add a check in the typechecker (`typecheckVlet`)** (important: check the *outer* binding):

   - If `ctx.varEnv.lookup x = none`, proceed (not shadowing).
   - If `ctx.varEnv.lookup x = some qt_outer`, then reject only if `qt_outer.pred` is `guardClosure k ...` and `ctx.regime.lookup? k ≠ none`.

   Implementation sketch (avoid checking the inner binding by accident):

   ```lean
   match ctx.varEnv.lookup x with
   | none => pure ()
   | some qt_outer =>
     match qt_outer.pred with
     | Predicate.guardClosure k _ _ _ =>
         if ctx.regime.lookup? k |>.isSome then
           throw s!"Cannot shadow variable {x}: outer binding has an active guard predicate"
     | _ => pure ()
   ```

2. **Update the formal spec (Ott) with a side condition**:
   - Add a side condition that matches the implementation (e.g. “if `x ∈ dom(σ)` and `σ(x)` has an interpreted `guardClosure`, reject”).

3. **Add/adjust tests**:
   - Add a failure test for the rejected case: shadowing a variable whose outer binding is a `guardClosure` with interpreted tag.
   - Add “allowed” tests to avoid accidental over-restriction:
     - shadowing a `noPred` variable (should pass),
     - shadowing a `guardOnly` variable (should pass),
     - shadowing a `guardClosure` variable whose tag is not interpreted (should pass).

4. **(Optional) surface-level restriction in the parser/front-end**:
   - If desired, reject shadowing earlier during parsing/AST construction, but the typechecker check is sufficient for soundness and proof simplification.

### Expected impact

- Removes the proof-critical corner while allowing benign rebinding patterns.

## Interaction with `PExpr.vlet`

The language also contains a binder form `PExpr.vlet` inside predicate expressions.
This proposal is about *runtime* scoping (`vlet`) and the post-state `consistentWithRegime` obligations that range over the typing context’s `varEnv`.

`PExpr.vlet` is currently used for dependency extraction and predicate bodies; it does not introduce a runtime scope exit that restores a `varEnv` while keeping memory changes, so it does not create the same mismatch.

If predicate expressions later gain a semantics that feeds into `consistentWithRegime` in a similar “scope exit” way, then an analogous shadowing restriction may be needed there too.

## Documentation synchronization

If we enforce a user-visible restriction on shadowing, the user-facing language documentation (e.g. LaTeX description) should be updated to reflect the rule and provide a short rationale (proof/soundness driven).
