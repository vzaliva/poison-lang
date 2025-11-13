# IO Equality Proof Pattern (Lean 4.24)

## How it used to work (≤ Lean 4.23)
When we needed to inspect an equality between `IO` computations,
```lean
h : LeanPoison.beval … = pure …
```
we would simply run
```lean
apply congrFun (a := ()) at h
```
to evaluate both sides at the dummy world `() : Unit`. The resulting equality
```lean
h : LeanPoison.beval … () = …
```
still counted as a *function* equality (Lean silently elaborated `IO α` to `Unit → EStateM.Result …`), so we could `simp [EStateM.pure]` and feed `h` straight into induction hypotheses that demanded the original function type.

## Why this breaks in Lean 4.24
Lean 4.24’s IO elaboration now exposes the actual `IO.RealWorld`. After we `simp`, every equality already looks like
```lean
LeanPoison.beval … LeanProofs.defaultWorld =
  EStateM.Result.ok … LeanProofs.defaultWorld
```
so we lose the function view. The IHs still expect
`LeanPoison.beval … = EStateM.pure …`, hence the type mismatches.

Concretely, the induction hypothesis for `beval_preserves_varEnv_op` is

```lean
IH :
  ∀ m < fuel'.succ,
    ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      config₀.varEnv = config₁.varEnv
```

It demands the **function** equality `LeanPoison.beval … = …`, not one specialized to a particular world, which is why the `defaultWorld` specialization breaks the call sites.

## New pattern: Indexed equality in induction hypotheses

The key insight is to use **existential equalities** in induction hypotheses rather than function equalities. This pattern is essential when proving properties about chains of IO operations (e.g., `e1 op e2`).

### The indexed equality form

Instead of requiring function equalities in IHs:
```lean
IH : ∀ m < fuel'.succ, ∀ …,
  LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
  config₀.varEnv = config₁.varEnv
```

We now use existential equalities that explicitly track worlds:
```lean
IH : ∀ m < fuel'.succ, ∀ …,
  (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EStateM.Result.ok (.success config₁ v) w₁) →
  config₀.varEnv = config₁.varEnv
```

### Why this matters for chained operations

When proving properties about `e1 op e2`, we need to:
1. Evaluate `e1` at world `w₀`, producing result at world `h_state1`
2. Evaluate `e2` at world `h_state1`, producing result at world `h_state2`
3. Combine the results

The existential form allows us to extract these intermediate worlds from the bind chain and construct the existential needed for the IH:

```lean
-- From the bind chain, we have:
h_beval1 : LeanPoison.beval fuel' config₀ e1 verbose w₀ = 
           EStateM.Result.ok (.success config' v') h_state1

-- We construct the existential for the IH:
have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = 
                              EStateM.Result.ok (.success config' v') w₁' :=
  ⟨w₀, h_state1, h_beval1⟩

-- Now we can apply the IH:
exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1_ex
```

### Proof pattern

1. **Extract worlds from the hypothesis.** Use `rcases` to extract `w₀` and `w₁` from the existential:
   ```lean
   rcases h_eval with ⟨w₀, w₁, h_eq⟩
   ```

2. **Unfold and simplify to expose bind chains.** For chained operations, use `simp [bind, Bind.bind, EStateM.bind]` to expose the intermediate evaluations.

3. **Split on intermediate results.** Use `split` to case-analyse on each step of the bind chain, extracting intermediate worlds and results.

4. **Construct existentials for IHs.** When applying the IH to a sub-expression, construct the existential using the worlds extracted from the bind chain:
   ```lean
   have h_sub_ex : ∃ w₀' w₁', … := ⟨w₀, h_state1, h_beval1⟩
   ```

5. **Use injection for constructor reasoning.** After simplifying, use `injection` to extract equalities between constructors (configs, values, worlds).

By using indexed equalities, we can track the world flow through IO operation chains while maintaining compatibility with induction hypotheses.
