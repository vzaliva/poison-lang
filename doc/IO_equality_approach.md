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

## New pattern
To restore the old flexibility:

1. **Keep the function equality.** Whenever we have `h : LeanPoison.beval … = EStateM.pure …`, retain that untouched so it can feed induction hypotheses.
2. **Introduce a per-world view only when needed.** Use a helper like
   ```lean
   @[simp] theorem evalAtWorld_eq (w : IO.RealWorld)
       {m n : IO α} : m = n → m w = n w := …
   ```
   to derive `h_world : LeanPoison.beval … w = …`.
3. **Do constructor reasoning on `h_world`.** Run `simp`, `split`, and injections on the per-world equality to inspect `EStateM.Result`.
4. **Convert back to `pure` as needed.** Use `simpa [EStateM.pure]` to rewrite between `EStateM.Result.ok … w` and `EStateM.pure … w`.

By keeping both views (`h` for the IH, `h_world` for destructing), we avoid the `x✝` vs `defaultWorld` mismatch and can mechanically replace the old `congrFun (a := ())` tricks throughout the proof scripts.
