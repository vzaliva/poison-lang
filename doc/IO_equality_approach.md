# IO proof patterns (Lean 4.26+)

This note is a practical guide for proving properties about the Poison
interpreter's `IO`-based evaluator in Lean 4.26+.

## Mental model

In Lean 4.26+, `IO` is a deterministic function of a world token:

```lean
IO α = Void IO.RealWorld → EST.Out IO.Error IO.RealWorld α
```

Success cases appear as `EST.Out.ok result nextWorld`. In particular, when
reasoning about `beval`, one typically needs to expose and thread the world
tokens through bind chains.

## Recommended helper definitions

The development provides a fixed witness world and evaluation lemmas in
`LeanProofs/IOHelpers.lean`:

```lean
noncomputable def defaultWorld : Void IO.RealWorld := ...

@[simp] theorem evalAtWorld_eq {α} (w : Void IO.RealWorld) {m n : IO α} :
  m = n → m w = n w := ...

@[simp] theorem evalAtDefault_eq {α} {m n : IO α} :
  m = n → m defaultWorld = n defaultWorld := ...
```

Use `evalAtWorld_eq` to turn an equality of `IO` computations into a concrete
equality at a chosen world token.

## Unfolding bind chains (`do`-notation)

When `simp`ping goals or hypotheses produced by `beval`, the relevant
definitions are:

```lean
simp [bind, Bind.bind, EST.bind] at h
simp [Functor.map, EST.bind, EST.pure] at h
```

After unfolding, use `split` to case-analyse intermediate results and `injection`
to extract equalities from constructor equalities (`.success`, `EST.Out.ok`, etc.).

## World-indexed termination (world threading)

For proofs that must track I/O effects, prefer the explicit world-indexed
termination judgement from `LeanProofs/SemanticsProperties.lean`:

```lean
def terminatesToW (w₀ w₁ : Void IO.RealWorld) (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    beval fuel c₀ e verbose w₀ = EST.Out.ok (.success c₁ out) w₁
```

This form supports world-threading: in sequential constructs, the output world
of the first sub-evaluation becomes the input world of the next.

In two-run developments (notably fault robustness), the internal step theorem is
formulated with a **shared input world** `w` for both runs and proves that the
two runs produce the **same output world**. This “world synchronisation”
invariant is an essential induction invariant for sequencing.

## Bridging from world-free statements

Many public statements use a world-free `terminatesTo` (expressed via equality of
`IO` computations). To work with explicit worlds, evaluate the equality at a
world and simplify `pure`:

```lean
rcases ht with ⟨fuel, verbose, hbeval⟩
have h_at_w := LeanProofs.evalAtWorld_eq w hbeval
-- now simp [pure] at h_at_w yields:
-- beval fuel c₀ e verbose w = EST.Out.ok (.success c₁ out) w
```

From this, one typically derives `terminatesToW w w e c₀ c₁ out`.

## Checklist

- Use `terminatesToW` when the proof must compose I/O effects (world threading).
- Fix a world token (often `defaultWorld`) when turning `IO` equalities into
  concrete equalities.
- Use `simp [EST.bind]` / `split` / `injection` to expose and manipulate bind
  chains.
