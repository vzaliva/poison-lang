# IO Equality Proof Pattern (Lean 4.26+)

## Historical background

### Lean ≤ 4.23
When we needed to inspect an equality between `IO` computations,
```lean
h : beval … = pure …
```
we would simply run
```lean
apply congrFun (a := ()) at h
```
to evaluate both sides at the dummy world `() : Unit`. The resulting equality
```lean
h : beval … () = …
```
still counted as a *function* equality (Lean silently elaborated `IO α` to `Unit → EStateM.Result …`), so we could `simp [EStateM.pure]` and feed `h` straight into induction hypotheses that demanded the original function type.

### Lean 4.24
Lean 4.24's IO elaboration exposed the actual `IO.RealWorld`. The `EStateM` approach still worked, but required explicit world handling.

### Lean 4.26
Lean 4.26 introduced a new IO implementation using `EST` (Error-State Transformer) with `Void` wrapper types:
```lean
IO α = EIO IO.Error α = EST IO.Error IO.RealWorld α = Void IO.RealWorld → EST.Out IO.Error IO.RealWorld α
```

Key changes:
- The world token type is now `Void IO.RealWorld` (an opaque wrapper), not `IO.RealWorld` directly
- The result type is `EST.Out ε σ α` instead of `EStateM.Result ε σ α`
- Bind is now `EST.bind` instead of `EStateM.bind`
- Map is now via `EST.bind` and `EST.pure` (no separate `EStateM.map`)

## Current approach (Lean 4.26+)

### World token type
The `Void σ` type wraps the state type opaquely. To create a witness world for proofs:
```lean
noncomputable def defaultWorld : Void IO.RealWorld :=
  Void.mk (Classical.choice (inferInstance : Nonempty IO.RealWorld))
```

### Result type
Use `EST.Out.ok` and `EST.Out.error` instead of `EStateM.Result.ok` and `EStateM.Result.error`:
```lean
-- Old (Lean ≤ 4.25):
h : beval m config₀ e verbose w₀ = EStateM.Result.ok (.success config₁ v) w₁

-- New (Lean 4.26+):
h : beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁
```

### Unfolding bind chains
Use `EST.bind` instead of `EStateM.bind` in simp calls:
```lean
-- Old:
simp [bind, Bind.bind, EStateM.bind] at h_eq

-- New:
simp [bind, Bind.bind, EST.bind] at h_eq
```

### Handling Functor.map
For expressions using `<$>` (fmap), use `EST.bind` to unfold:
```lean
-- Old:
simp [Functor.map, EStateM.map] at h_eq

-- New:
simp [Functor.map, EST.bind] at h_eq
```

## Indexed equality pattern

The key insight is to use **existential equalities** in induction hypotheses rather than function equalities. This pattern is essential when proving properties about chains of IO operations (e.g., `e1 op e2`).

### The indexed equality form

Instead of requiring function equalities in top-level lemmas and IHs:
```lean
IH : ∀ m < fuel'.succ, ∀ …,
  beval m config₀ e verbose = pure (.success config₁ v) →
  config₀.varEnv = config₁.varEnv
```

We now use existential equalities that explicitly track worlds:
```lean
IH : ∀ m < fuel'.succ, ∀ …,
  (∃ w₀ w₁, beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.varEnv = config₁.varEnv
```

We fix `e`, `fuel`, `verbose`, `config₀`. For any particular `config₁` and `v`, the lemma says:

If there exists some starting world `w₀` and final world `w₁` such that running
`beval` from `config₀` on `e` succeeds with result `(.success config₁ v)`, then
`config₀.varEnv = config₁.varEnv`.

### Why this matters for chained operations

When proving properties about `e1 op e2`, we need to:
1. Evaluate `e1` at world `w₀`, producing result at world `w₁`
2. Evaluate `e2` at world `w₁`, producing result at world `w₂`
3. Combine the results

The existential form allows us to extract these intermediate worlds from the bind chain and construct the existential needed for the IH:

```lean
-- From the bind chain, we have:
h_beval1 : beval fuel' config₀ e1 verbose w₀ = 
           EST.Out.ok (.success config' v') w₁

-- We construct the existential for the IH:
have h_beval1_ex : ∃ w₀' w₁', beval fuel' config₀ e1 verbose w₀' = 
                              EST.Out.ok (.success config' v') w₁' :=
  ⟨w₀, w₁, h_beval1⟩

-- Now we can apply the IH:
exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1_ex
```

### Proof pattern

1. **Extract worlds from the hypothesis.** Use `rcases` to extract `w₀` and `w₁` from the existential:
   ```lean
   rcases h_eval with ⟨w₀, w₁, h_eq⟩
   ```

2. **Unfold and simplify to expose bind chains.** For chained operations, use `simp [bind, Bind.bind, EST.bind]` to expose the intermediate evaluations.

3. **Split on intermediate results.** Use `split` to case-analyse on each step of the bind chain, extracting intermediate worlds and results.

4. **Construct existentials for IHs.** When applying the IH to a sub-expression, construct the existential using the worlds extracted from the bind chain:
   ```lean
   have h_sub_ex : ∃ w₀' w₁', … := ⟨w₀, w₁, h_beval1⟩
   ```

5. **Use injection for constructor reasoning.** After simplifying, use `injection` to extract equalities between constructors (configs, values, worlds).

By using indexed equalities, we can track the world flow through IO operation chains while maintaining compatibility with induction hypotheses.

## Summary of changes from Lean ≤ 4.25 to Lean 4.26+

| Old (≤ 4.25) | New (4.26+) |
|--------------|-------------|
| `IO.RealWorld` as world type | `Void IO.RealWorld` as world type |
| `EStateM.Result.ok` | `EST.Out.ok` |
| `EStateM.Result.error` | `EST.Out.error` |
| `EStateM.bind` | `EST.bind` |
| `EStateM.map` | `EST.bind` (via Functor instance) |
| `EStateM.pure` | `EST.pure` |
