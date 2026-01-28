# Issue 95 proposal: regime-aware typing with an explicit regime parameter `R`

The issue: https://github.com/vzaliva/poison-lang/issues/95

## Motivation: typing vs. FR are at different “specificity levels”

The current typechecker is intentionally *flow-insensitive* at `if`: unless it
can exploit predicate structure, it must conservatively consider both branches.

The FR development, however, reasons under a fixed **regime** that (intuitively)
fixes which input faults/validity checks hold. This makes FR reasoning *more
specific* than regime-agnostic typing: in many FR scenarios, the two runs are
intended to be aligned on which branch of a predicate check is taken, but the
typechecker does not (currently) have access to that regime-level information.

This mismatch is especially visible for predicate-based conditionals
(`match_guard`/`if_depoison`): the typing rule is designed to be
validation-friendly (to keep de-poisoning useful), while StepFR-style invariants
require either branch alignment or enough conservatism to avoid post-state
`agreeOnClean` failures.

## Goal

Keep predicate-based de-poisoning useful (avoid “make everything conservative”),
while making the fault-robustness (FR) proof obligations line up with the typing
rules at `if`.

This document focuses on making typing (in the FR setting) **regime-aware** by
threading an explicit, immutable **regime `R`** through the typing judgment.

## Snapshot of current behavior (only what’s relevant)

- The type system already uses **ℒ** for de-poisoning on variable/deref reads.
- `if_depoison` (`match_guard` succeeds) is currently “validation-friendly” but **does not raise branch `pc` by the condition poison** and forgets the tag after the conditional.
- The StepFR-style theorem needs either:
  - **branch alignment** (both runs take the same branch), or
  - **pc poisoning** (so divergent-branch writes become non-clean-under-R, avoiding `agreeOnClean` obligations).

The failure mode in the report is precisely: `if_depoison` enables divergent
branches to write different **clean** values to a **clean-under-R** location.

## Proposal summary

### 1) Extend the typing judgment with an immutable `R`

Idea: make the FR regime *explicit* in typing.

Sketch of new judgment form (Ott-like):

```
pm ; R ; pc ; G ; S ; L |- e : Q -| G' ; L'
```

`R` is a bounded partial map from tags to booleans (as in the Lean FR development):

- `R(k) = some true` / `R(k) = some false` when the regime fixes the outcome for tag `k`,
- `R(k) = none` when the regime leaves `k` unknown/out-of-domain.

Crucially, `R` never changes: it is threaded through premises unchanged.

### 2) Make `if_depoison` consult `R` (not ℒ) when `match_guard` returns a tag

When `match_guard e1 G S = k with LS`, `R(k)` tells us whether FR intends the
check outcome to be fixed (deterministic) or not:

- If `R(k) = some true`: treat the conditional as *regime-deterministic true*.
- If `R(k) = some false`: treat it as *regime-deterministic false*.
- If `R(k) = none`: treat it as unknown (conservative fallback).

In all cases, we still use `match_guard`’s dependency locset `LS` to populate ℒ
entries *inside the branch typing* (so invalidation on writes remains correct).

#### Spec-level sketch: split `if_depoison` by `R(k)`

In `poison-lang-spec/poison-lang.ott` there are multiple `if` rules (special
cases for functions, refs, etc.). For brevity, this proposal sketches only the
*general* `if_depoison` shape; the same idea applies to the other
`if_depoison_*` rules in the obvious way.

We sketch only the *general* `if_depoison` shape below (non-reference result);
the same idea applies to `if_depoison_ref`, `if_depoison_fn`, `if_depoison_pfn`
in the obvious way.

1) **Unknown regime value: fall back to conservatism (`R(k)=none`).**

Key change vs. today: if the regime does not fix `k`, we must assume the two FR
runs *may* diverge on the guard, so we poison the branch `pc` with the guard’s
poison (like `if_std`).

Ott-like sketch:

```
match_guard e1 G S = k with LS
R(k) = none
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L
pm   ; R ; join pc p1 ; G ; S ; L[k |-> true  using LS] |- e2 : T :> p2 { P2 } -| G2 ; L2
pm   ; R ; join pc p1 ; G ; S ; L[k |-> false using LS] |- e3 : T :> p3 { P3 } -| G3 ; L3
----------------------------------  :: if_depoison_R_unknown
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3
    : T :> join pc join p1 join p2 p3 { no_pred }
    -| JoinG G2 G3 ; JoinL L2 L3
```

Notes:

- The conclusion uses `JoinL L2 L3` (not the pre-conditional `L`) so that
  dependency invalidations caused by writes inside either branch can’t be lost.
- This is intentionally “as conservative as `if_std`” when `R` does not tell us
  that the check outcome is aligned.

2) **Regime-deterministic true (`R(k)=some true`): both branches check, but only `then` is “effective”.**

Ott-like sketch:

```
match_guard e1 G S = k with LS
R(k) = some true
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L
pm   ; R ; pc ; G ; S ; L[k |-> true  using LS] |- e2 : T :> p2 { P2 } -| G2 ; L2
pm   ; R ; pc ; G ; S ; L[k |-> false using LS] |- e3 : T :> p3 { P3 } -| G3 ; L3
----------------------------------  :: if_depoison_R_true
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3
    : T :> join pc p2 { no_pred }
    -| G2 ; L2
```

3) **Regime-deterministic false (`R(k)=some false`): symmetric, `else` is “effective”.**

Ott-like sketch:

```
match_guard e1 G S = k with LS
R(k) = some false
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L
pm   ; R ; pc ; G ; S ; L[k |-> true  using LS] |- e2 : T :> p2 { P2 } -| G2 ; L2
pm   ; R ; pc ; G ; S ; L[k |-> false using LS] |- e3 : T :> p3 { P3 } -| G3 ; L3
----------------------------------  :: if_depoison_R_false
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3
    : T :> join pc p3 { no_pred }
    -| G3 ; L3
```

## Justification and notes

### Unknown regime values: accept conservatism

The “unknown” case above (`R(k)=none`) is the explicit conservatism knob:
poison branch `pc` by the guard poison and join results, just like `if_std`.

This is the knob that avoids the report’s counterexample *without* discarding
the regime-aware path-sensitive benefit for deterministic cases.

### How `deps` combine with tag truth values in ℒ

ℒ entries carry both a boolean and a dependency locset:

- `L[k |-> b using LS]` records “tag `k` currently has value `b` and depends on `LS`”.
- `invalidate_deps` removes any `k` whose stored `LS` intersects a written locset.

This proposal gets the needed `LS` directly from the guard structure:

- `match_guard e1 G S = k with LS` already computes a conservative dependency locset `LS`.
- Each `if_depoison_R_*` rule updates the *branch-local* ℒ as `L[k |-> true using LS]` / `L[k |-> false using LS]`.
- In the regime-deterministic cases, only the branch consistent with `R(k)=some b` is “effective” and thus the output ℒ carries the matching `k : b using LS`.

### Guard-only tags

Today `match_guard` ignores `guardOnly` predicates, so branch pruning via `match_guard` will only target `guardClosure` tags (which have bodies and thus meaningful deps).

That’s good: it avoids the “no deps / no semantics” corner.

### Interpretation of the regime `R`

Assumption for this proposal: `R(k)=some b` means the outcome of the matched
guard check is fixed to `b` (branch-aligned) in the executions we relate by FR.
When `R(k)=none`, the regime does not constrain that check.

## Why this should address the original issue #95

If `match_guard` returns a tag `k` and the regime fixes it (`R(k)=some b`):

- the typing rule selects a single “effective” branch (no `JoinG` / no “join both branches”),
- so we avoid the “two runs take different branches but both write clean” situation *at the typing level* (assuming the proof bridge below).

If `R(k)=none`, we revert to conservatism (poison branch `pc` by guard poison
and join), so the report’s counterexample is blocked even without branch
alignment.

The remaining hard requirement is the proof bridge below to justify that pruning
corresponds to the actually-taken branch under the FR quantification.

## Key concerns & what must be resolved for the proposal to be sound

### A) How do we justify branch alignment from `R`?

To safely use `R(k)=some b` to select a single “effective” branch, the proof
must justify that in the runs being related, the runtime condition `e1`
*actually evaluates to* `b` (and thus both runs take the same branch).

At present, the abstraction boundary is:

- runtime semantics evaluates the condition `e1` to `Value.bool b`;
- proof-side `PredSat` is abstract and is only required to satisfy `match_sound` in one direction (roughly “`e1` evaluates to true ⇒ `PredSat k` holds on the underlying value”), not a biconditional.

So, as things stand, **`R(k)=some b` does not force `e1` to evaluate to `b`**.
That’s exactly why branch divergence is possible in the report.

### Proposed fix: strengthen `PredSatLaws.match_sound` to a bidirectional law

We propose to resolve the above by strengthening the one-direction “soundness”
law to a bidirectional connection **for `match_guard`-recognized conditions**.

Diff-style summary (informal):

```diff
- match_sound: matchGuard condition Γ σ = .ok (k, deps)
-           → terminatesTo mode condition cfg (Value.bool true)
-           → owningValue(Γ, σ, μ, ρ, θ, k, v)
-           → predSat k μ v
+ match_iff:   matchGuard condition Γ σ = .ok (k, deps)
+           → terminatesTo mode condition cfg (Value.bool b)
+           → owningValue(Γ, σ, μ, ρ, θ, k, v)
+           → (b = true ↔ predSat k μ v)
```

Intended strengthening (Lean-ish sketch; re-uses the same “owning value” side
condition currently present in `match_sound`):

```
-- If match_guard recognizes the condition as tag k, then the condition’s
-- boolean result matches predSat on the owning value.
match_iff :
  ∀ (mode : LeanPoison.EvalMode) (condition : Expr) (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
    (k : Tag) (deps : Deps)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (addr : Address) (pm : Bool) (cfg : Config)
    (v : Value) (b : Bool),
    matchGuard condition Γ σ = .ok (k, deps) →
    terminatesTo mode condition { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm } cfg (Value.bool b) →
    ( (∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧
          qtypGuardTag qt = some k ∧
          ρ.lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (t : ETyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref t ls ∧
          l0 ∈ ls ∧
          Γ.lookup l0 = some memQt ∧
          qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) →
    (b = true ↔ predSat k μ v)
```

Key points:

- This strictly generalizes the current direction: taking `b=true` gives
  “evaluation to true ⇒ `predSat` holds”.
- We only relate `predSat` to the condition’s boolean result **when the
  condition terminates** (which is the relevant case when the enclosing `if`
  terminates).

Why this resolves branch alignment under the existing FR premises:

- FR already assumes `consistentRegimeSpec predSat R s μ ρ θ` on the initial
  state(s), which (for spec guard-closure tags) gives:
  - `R(k)=some true → predSat k μ v`, and
  - `R(k)=some false → ¬ predSat k μ v`,
  for the corresponding owning value `v`.
- If `match_guard` recognizes the runtime condition as tag `k`, then `match_iff`
  implies that any terminating evaluation to `Value.bool b` satisfies
  `(b=true ↔ predSat k μ v)`.
- Combining the two yields that the only possible terminating boolean result is
  exactly the one prescribed by `R(k)`, i.e. branch alignment becomes a
  consequence rather than an extra premise.
