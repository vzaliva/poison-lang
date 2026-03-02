# Problem: Closure Member-Matching in Same-Config Agreement

## 1. Conceptual Background

Fault-robustness (FR) is a semantic property ensuring that poison (data corruption) propagates
conservatively: two runs that agree on critical inputs must produce observationally equivalent
outputs.  The agreement is mediated by a *regime* — a map from guard tags to booleans that
encodes which faults were injected.

### Agreement and closures

The core agreement relation `agreeValueUnder` says: if a value's qualified type is *clean*
(not poisoned), the two runs must produce equal values.  For closures, "equal" is deeper than
structural equality — two closures agree when they have the same body, the same captured typing
environment `σcap`, and their captured runtime environments agree element-by-element (via the
mutually-inductive `agreeCapturedEnv`).

### Why FR must look inside closures

Closures carry captured runtime environments.  A closure can "hide" a poisoned value in its
captured env, and that value can later escape when the closure is applied.  To prevent this,
FR tracks regime consistency *deeply*: the invariant `closureCapturedVarsRegime` recursively
checks that every value inside a closure's captured env satisfies the regime, and
`agreeCapturedEnv` checks that the captured values from two runs agree.

### The "same-config" case

The reflexive case — a single run agrees with itself — is not trivial for closures.  When
proving `agreeValueUnder predSat R μ μ θ θ qt v v` for a closure `v = Value.closure x body env`,
the proof must:

1. Identify a captured typing environment `σcap` (a member of the type's closure list `tcls`).
2. Show `agreeCapturedEnv ... σcap env env` — the captured runtime env agrees with itself
   under `σcap`.
3. Provide regime evidence (`MemberVarsRegimeEvidence`, `MemberCvcrEvidence`) for `(σcap, env)`.

These obligations require **both typing information and regime information** for the **same**
`σcap` member.  This is where the problem lies.

## 2. The Problem

### Two independent sources, two independent members

For a closure value `v = Value.closure x body env` typed at `ETyp.arrow st1 st2 p tcls`:

- **Typing source** (`valueHasETyp`): inverting the typing judgement gives some member
  `tenv` with `FnTClosure.regular x body tenv ∈ tcls`, plus:
  - `henv`: each variable in `tenv` has a correctly-typed value in `env`
  - `hcover`: `env` has values for all variables in `tenv`

- **Regime source** (`closureCapturedVarsRegime`, from `consistentWithRegime`): inverting
  the deep regime property gives some member `σcap_deep` with
  `FnTClosure.regular x body σcap_deep ∈ tcls`, plus:
  - `capturedVarsRegimeProperty`: regime evidence for `(σcap_deep, env)`
  - Deep recursion: regime evidence for all values captured under `σcap_deep`

**The problem**: `tenv` and `σcap_deep` are independently existential — they are both members
of `tcls` but nothing guarantees they are the same member.  This matters because:
- `agreeCapturedEnv ... σcap env env` needs `valueHasETyp` sub-proofs for `σcap`'s variables
  → available only for `tenv`
- `MemberVarsRegimeEvidence ... σcap env` needs regime evidence for `σcap`'s variables
  → available only for `σcap_deep`

If `tenv ≠ σcap_deep`, neither member alone provides everything needed.

### Why `tcls` can have multiple members with the same `(x, body)`

The type checker creates closures with singleton closure lists:
```
typecheckFn ctx x st1 body st2 =
  let σcap := VarTypeEnv.toCaptured ctx.varEnv
  ...arrow st1 st2 ctx.pc [FnTClosure.regular x body σcap]
```

After an if-then-else where both branches create `fn a => body`, the joined type has
`tcls = [FnTClosure.regular a body σ_then, FnTClosure.regular a body σ_else]`.  If the
branches have different variable scopes (e.g. one introduces a local binding), `σ_then ≠ σ_else`
even though `a` and `body` are identical.

**Concrete counterexample** (for the old lemma `closure_same_config_tenv_env` which claimed
`σcap = toCaptured ctx.varEnv ∧ env = ρ`):

```
let x = 1;
let g = fn a => a;  // σcap = toCaptured({x:int}) = [(x,int)]
                     // env captures ρ = {x↦1}
let y = 2;
// Now ctx.varEnv = {x:int, y:int},  ρ = {x↦1, y↦2}
// g's type still has σcap = [(x,int)]
// toCaptured(ctx.varEnv) = [(x,int), (y,int)]  ← different!
// g's runtime env is {x↦1}, but ρ = {x↦1, y↦2}  ← different!
```

A second counterexample shows multiple members:
```
let f = if (b) {
  let y = 1;
  fn a => a          // σcap₁ = [(x,int), (y,int)]
} else {
  fn a => a          // σcap₂ = [(x,int)]
};
// After join: tcls = [regular a a σcap₁, regular a a σcap₂]
// Same (a, body=a), different σcap
```

### Impact

The lemma `closure_same_config_tenv_env` (TypeSafety.lean) is false.  Its mirror
`peClosure_same_config_tenv_env` is also false.  These were used to bridge typing and
regime evidence in `agreeValueUnder_same` (FaultRobustnessProofs.lean).  Without them,
the closure and peClosure cases of `agreeValueUnder_same` have no proof, which blocks
`agreeOnClean_same_config` → `stepFR_app`.

## 3. Relationship to Historical Sigma Mismatch

This problem is a **new manifestation of the same root cause** documented in
`doc/app-proof-history.md` (Root Cause Analysis, Approaches 1–7, and Path D).

The history describes the "sigma mismatch": inverting the existential in
`deepValueQTypProperty.closure` yields an unpredictable `σcap'`.  The history encountered
this at **transport** sites — moving evidence across `joinETyps` widening.  Path D solved
transport by **pre-computing** member evidence at lambda sites (where `tcls` is a singleton
and `σcap` is unambiguous) and **storing** it directly in `agreeValueUnder.clean_internal_arrow`,
so that use sites read stored evidence without inverting `closureCapturedVarsRegime`.

Our problem is the same root cause at the **construction** site: `agreeValueUnder_same` must
build a fresh `agreeValueUnder` proof from scratch.  There is no prior `agreeValueUnder` to
read from, so we must invert `closureCapturedVarsRegime` (or `consistentWithRegime`),
re-exposing the sigma mismatch.

**Historical approaches considered and rejected:**
- Approach 6 (full universal `deepValueQTypProperty`) — rejected as "precision killer"
- Approach 5 (hybrid existential+universal) — reduces to the same hard case
- Approach 4 (shift sigma mismatch to caller) — doesn't eliminate it
- Singleton uniqueness — only works for singletons; breaks after any join
- Weaken `clean_internal_arrow` to carry two separate `σcap` values — changes the heavily
  pattern-matched `agreeValueUnder` inductive; unclear if transport lemmas survive
- Path D (direct member evidence) — solved transport, not construction

## 4. Solution: Bundle Typing + Regime Evidence

Strengthen the third conjunct of `consistentWithRegime` (and `valueConsistentWithRegime`)
so that the `deepValueQTypProperty` existential member carries **both** regime evidence and
typing evidence (`henv` + `hcover` from `valueHasETyp`).  This is achieved by using a
stronger predicate `P` that conjoins `capturedVarsRegimeProperty` with typing conditions.

This leaves `deepValueQTypProperty` unchanged (it's parameterized by abstract `P`) and
doesn't touch the `agreeValueUnder` inductive.  It extends Path D's proven philosophy of
synchronizing on a specific member early and carrying evidence directly — Path D did this
for `agreeValueUnder` at lambda sites; this approach does it for `consistentWithRegime` /
`valueConsistentWithRegime` at every step.

Step theorems already prove both regime and typing properties; the main cost is ensuring the
same member is used for both.

### Proposed code changes

**Step 1 — new definitions** (RegimeConsistency.lean, after `capturedVarsRegimeProperty`):

```lean
-- NEW: "σcap matches ρcap under θ" — typing evidence for captured variables
def capturedVarsTypingProperty (θ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  List.Nodup (σcap.map Prod.fst) ∧
  (∀ y qt, σcap.lookup y = some qt → ∃ v, ρcap.lookup y = some v) ∧
  (∀ y qt v, σcap.lookup y = some qt →
    ρcap.lookup y = some v → valueHasETyp θ v qt.etyp)

-- NEW: bundle regime + typing for the same σcap member chosen by deepValueQTypProperty
def capturedVarsRegimeAndTypingProperty (predSat : PredSat) (R : Regime)
    (μ : Memory) (θ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
  capturedVarsTypingProperty θ σcap ρcap

-- NEW: strengthened wrapper — carries both regime and typing evidence
inductive closureCapturedVarsRegimeAndTyping (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | intro :
      deepValueQTypProperty (capturedVarsRegimeAndTypingProperty predSat R μ θ) qt v →
      closureCapturedVarsRegimeAndTyping predSat R qt μ θ v
```

**Step 2 — generic forgetful map** (RegimeConsistency.lean, after `deepValueQTypProperty`):

```lean
-- NEW: if P implies Q pointwise, then deepValueQTypProperty P implies deepValueQTypProperty Q
lemma deepValueQTypProperty_mono
    (h : ∀ σ ρ, P σ ρ → Q σ ρ) :
    deepValueQTypProperty P qt v → deepValueQTypProperty Q qt v
```

This gives backward compatibility: any code that only needs `closureCapturedVarsRegime`
can recover it via `deepValueQTypProperty_mono` (dropping the typing conjunct).

**Step 3 — modify `consistentWithRegime`** (RegimeConsistency.lean):

```lean
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  -- conjuncts 1, 2 unchanged
  ...
  (∀ x qt v, ctx.varEnv.lookup x = some qt →
     ρ.lookup x = some v →
     closureCapturedVarsRegimeAndTyping predSat R qt μ θ v)  -- ← CHANGED (was closureCapturedVarsRegime)
```

**Step 4 — modify `valueConsistentWithRegime`** (FaultRobustness.lean):

```lean
inductive valueConsistentWithRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap)            -- ← CHANGED: added θ
    (v : Value) : Prop where
  | noTag :
      qtypGuardTag qt = none →
      closureCapturedVarsRegimeAndTyping predSat R qt μ θ v → -- ← CHANGED
      valueConsistentWithRegime predSat R qt μ θ v
  -- (all other constructors: same change in last argument)
  ...
```

This is necessary because `consistentWithRegime_closure_body_start` obtains
`closureCapturedVarsRegime` for the argument value `vArg` by extracting it from
`valueConsistentWithRegime` (via `valueConsistentWithRegime_closureCapturedVarsRegime`).
If the extraction only gives plain `closureCapturedVarsRegime` but the body context
needs the bundle, the member-matching problem resurfaces at the construction site.
Making `valueConsistentWithRegime` carry the bundle avoids this.

**Step 5 — strengthen `trustedVarsClosureRegimeInit`** (FaultRobustness.lean:692):

```lean
inductive trustedVarsClosureRegimeInit
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)             -- ← CHANGED: added θ
    : Prop where
  | intro :
      (∀ x qt v, ctx.varEnv.lookup x = some qt →
        ¬ s.vars.hasKey x → ρ.lookup x = some v →
        closureCapturedVarsRegimeAndTyping predSat R qt μ θ v)  -- ← CHANGED
      → trustedVarsClosureRegimeInit predSat R s ctx μ ρ θ
```

### How this solves the member-matching problem

When `agreeValueUnder_same` inverts `closureCapturedVarsRegimeAndTyping` on a closure
`v = Value.closure x body env`, the `deepValueQTypProperty.closure` case yields a **single**
`σcap` with:

- `FnTClosure.regular x body σcap ∈ tcls`
- `capturedVarsRegimeProperty predSat R μ σcap env` → derives `MemberVarsRegimeEvidence`
- `∀ y qt v, σcap.lookup y = some qt → env.lookup y = some v → valueHasETyp θ v qt.etyp`
  → provides `htyp1`, `htyp2` for `agreeCapturedEnv.cons_clean`
- `∀ y qt, σcap.lookup y = some qt → ∃ v, env.lookup y = some v`
  → provides `hlookup1`, `hlookup2` for `agreeCapturedEnv`
- Deep recursion → derives `MemberCvcrEvidence` (via `deepValueQTypProperty_mono` to
  extract the regime part) and recursive `agreeValueUnder_same` via IH

All from the **same** `σcap`.  No member-matching needed.

### Why `valueConsistentWithRegime` must also be strengthened

If only `consistentWithRegime` is strengthened (option 1), the app body context construction
(`consistentWithRegime_closure_body_start`) still needs the bundle for the argument value
`vArg`.  Currently, `h_arg_cvcr` is derived from `valueConsistentWithRegime` via
`valueConsistentWithRegime_closureCapturedVarsRegime`.  If `valueConsistentWithRegime` only
carries plain `closureCapturedVarsRegime`, we'd need to reconstruct the bundle by combining
it with the separate `valueHasETyp` from the `StepFR` IH — which re-exposes the
member-matching problem (two independent existentials for the same value).

Making `valueConsistentWithRegime` carry the bundle (option 2) avoids this: the bundle
flows from the IH through `valueConsistentWithRegime`, through extraction, into
`consistentWithRegime_closure_body_start`, without ever needing to re-combine independent
existentials.

### Why construction is feasible

The bundle survives all standard transformations applied in step theorems:

- **Closure creation** (`typecheckFn`): `tcls` is a singleton — only one member, bundle
  is trivially constructed from `runtimeInstantiatesCtx` + existing regime evidence.
- **Joins** (`joinETyps`): original member persists in merged `tcls` via
  `mergeFnTClosures`; the evidence references the original member, not `tcls`.
- **Regime monotonicity** (`Regime.monotoneStep`): the typing part
  (`capturedVarsTypingProperty`) is regime-independent; the regime part uses
  `closureCapturedVarsRegime_monotone`.
- **Memory transport** (`transport_μ`): the typing part is memory-independent; the regime
  part uses `closureCapturedVarsRegime_transport_μ`.
- **Map extension** (`wfExtendsMap θ θ'`): `valueHasETyp` is monotone in `θ` (lookup
  extension preserves all constructors); the regime part doesn't mention `θ`.
- **Non-closure results** (int, bool, unit, string, loc): `deepValueQTypProperty.nonClosure`
  applies — no member needed, bundle is vacuously satisfied.

## 5. Affected Lemmas

### Definitions changed

| Definition | File | Change |
|---|---|---|
| `consistentWithRegime` | RegimeConsistency.lean | Conjunct 3 → `closureCapturedVarsRegimeAndTyping` |
| `valueConsistentWithRegime` | FaultRobustness.lean | Add `θ` param; all constructors → `...AndTyping` |
| `trustedVarsClosureRegimeInit` | FaultRobustness.lean | Add `θ` param; body → `...AndTyping` |

### New definitions

| Definition | File | Purpose |
|---|---|---|
| `capturedVarsTypingProperty` | RegimeConsistency.lean | Typing evidence (`Nodup` + `hcover` + `henv`) |
| `capturedVarsRegimeAndTypingProperty` | RegimeConsistency.lean | Conjunction of regime + typing |
| `closureCapturedVarsRegimeAndTyping` | RegimeConsistency.lean | Wrapper using `deepValueQTypProperty` |
| `deepValueQTypProperty_mono` | RegimeConsistency.lean | Generic `P → Q` forgetful map |

### Lemmas deleted (false)

| Lemma | File |
|---|---|
| `closure_same_config_tenv_env` | TypeSafety.lean |
| `peClosure_same_config_tenv_env` | TypeSafety.lean |

### Lemmas rewritten

| Lemma | File | Change |
|---|---|---|
| `agreeValueUnder_same` | FaultRobustnessProofs.lean | Closure/peClosure cases invert bundle |
| `agreeCapturedEnv_same_toCaptured` | FaultRobustnessProofs.lean | Likely replaced by direct version |

### Lemmas requiring signature/body updates (ripple from definition changes)

| Lemma / site | File | Nature of change |
|---|---|---|
| `consistentRegimeSpec_implies_consistentWithRegime` | FaultRobustnessProofs.lean | Build bundled conjunct 3 |
| `consistentWithRegime_closure_body_start` | FaultRobustnessProofs.lean | Accept/pass bundled `h_arg_cvcr` |
| `consistentWithRegime_monotone` | FaultRobustnessProofs.lean | Use `...AndTyping_monotone` |
| `valueConsistentWithRegime_closureCapturedVarsRegime` | FaultRobustnessProofs.lean | Extraction via `deepValueQTypProperty_mono` |
| `closureCapturedVarsRegime_monotone` | FaultRobustnessProofs.lean | Mirror for `...AndTyping` version |
| `closureCapturedVarsRegime_transport_μ` | FaultRobustnessProofs.lean | Mirror for `...AndTyping` version |
| `closureCapturedVarsRegime_transport_etyp` | FaultRobustnessProofs.lean | Mirror for `...AndTyping` (used in pred/poison normalization ~line 18740) |
| `closureCapturedVarsRegime_transport_pred` | FaultRobustnessProofs.lean | Mirror for `...AndTyping` (same normalization paths) |
| *(new)* `closureCapturedVarsRegimeAndTyping_transport_θ` | FaultRobustnessProofs.lean | Transport across `wfExtendsMap θ θ'` (uses `valueHasETyp_extends`) |
| `memberVarsRegimeEvidence_of_toCaptured` | FaultRobustnessProofs.lean | May need updating |
| `memberCvcrEvidence_of_toCaptured` | FaultRobustnessProofs.lean | May need updating |
| `join_transport_consistentWithRegime` | FaultRobustnessProofs.lean | Pass bundle through monotonicity |
| `joinTypeResults_transport_consistentWithRegime_from_member` | FaultRobustnessProofs.lean | Pass bundle through member transport |
| Step theorems (`stepFR_*`) | FaultRobustnessProofs.lean | Produce bundled `valueConsistentWithRegime` |
| `FaultRobustnessSpec` / `FaultRobustnessSpec_ioFree` | FaultRobustnessProofs.lean | Pass strengthened `trustedVarsClosureRegimeInit` |
