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

Closures carry captured runtime environments that may contain poisoned values.
When the closure is applied, these captured values participate in computation
and can affect the result. FR must therefore track regime consistency *deeply*:
the invariant `closureCapturedVarsRegime` recursively checks that every value
inside a closure's captured env satisfies the regime, and `agreeCapturedEnv`
checks that the captured values from two runs agree.

### The "same-config" case

The reflexive case — a single run agrees with itself — is not trivial for closures.  When
proving `agreeValueUnder predSat R μ μ θ θ qt v v` (where `R` is a regime) for a closure
`v = Value.closure x body env` whose qualified type `qt` has underlying type
`ETyp.arrow st1 st2 p tcls`, the proof must:

1. Find a member `FnTClosure.regular x body σcap ∈ tcls` — a captured *typing* environment
   `σcap` (mapping variables to qualified types) that matches the closure's binder and body.
2. Show `agreeCapturedEnv ... σcap env env` — the captured *runtime* environment `env`
   (mapping variables to values) agrees with itself under `σcap`.
3. Provide regime evidence (`MemberVarsRegimeEvidence`, `MemberCvcrEvidence`) for the pair
   `(σcap, env)`.

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

### Dependency diagram (before)

```
agreeValueUnder_same (closure case)
│
│  needs: agreeCapturedEnv ... σcap env env
│           ├─ typing evidence for σcap's variables
│           └─ regime evidence for σcap's variables
│
├── Source 1: valueHasETyp ──────────────────────────┐
│   └─ inverts typing judgement                      │
│      └─ yields tenv ∈ tcls                         │
│           ├─ henv  (typing for tenv's vars)        │ independent
│           └─ hcover (coverage for tenv's vars)     │ existentials
│                                                    │
├── Source 2: consistentWithRegime (conjunct 3) ─────┘
│   └─ closureCapturedVarsRegime
│      └─ inverts deepValueQTypProperty
│         └─ yields σcap_deep ∈ tcls
│              ├─ capturedVarsRegimeProperty (σcap_deep, env)
│              └─ deep recursion (σcap_deep, env)
│
╔══════════════════════════════════════════════════════╗
║  tenv and σcap_deep are independently existential.   ║
║  No guarantee tenv = σcap_deep.                      ║
║                                                      ║
║  - typing evidence covers tenv's variables only      ║
║  - regime evidence covers σcap_deep's variables only ║
║  - agreeCapturedEnv needs BOTH for ONE σcap          ║
║  ─────────────────────────────────────────────────── ║
║  Cannot pick σcap = tenv (missing regime evidence)   ║
║  Cannot pick σcap = σcap_deep (missing typing)       ║
╚══════════════════════════════════════════════════════╝
```

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

## 4. Solution: Strengthen `closureCapturedVarsRegime` in Place

Strengthen `closureCapturedVarsRegime` so that its `deepValueQTypProperty` predicate `P`
conjoins `capturedVarsRegimeProperty` with typing conditions.  This makes every
`closureCapturedVarsRegime` proof carry **both** regime evidence and typing evidence
(`henv` + `hcover` from `valueHasETyp`) for the **same** existential `σcap` member.

This leaves `deepValueQTypProperty` unchanged (it's parameterized by abstract `P`) and
doesn't touch the `agreeValueUnder` inductive.  It extends Path D's proven philosophy of
synchronizing on a specific member early and carrying evidence directly — Path D did this
for `agreeValueUnder` at lambda sites; this approach does it for `closureCapturedVarsRegime`
at every step.

Step theorems already prove both regime and typing properties; the main cost is ensuring the
same member is used for both.

### Proposed code changes

**Step 1 — new helper definitions** (RegimeConsistency.lean):

```lean
-- NEW: "σcap matches ρcap under θ" — typing evidence for captured variables
def capturedVarsTypingProperty (θ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  List.Nodup (σcap.map Prod.fst) ∧
  (∀ y qt, σcap.lookup y = some qt → ∃ v, ρcap.lookup y = some v) ∧
  (∀ y qt v, σcap.lookup y = some qt →
    ρcap.lookup y = some v → valueHasETyp θ v qt.etyp)
```

The `Nodup` requirement is always satisfiable: every `FnTClosure`/`PFnTClosure` member's
`σcap` is produced by `VarTypeEnv.toCaptured`, which calls `ExtTreeMap.toList` on a
sorted tree map — keys are unique by construction.

The monotonicity lemma already exists as `deepValueQTypProperty_monotone_P` (private, in
FaultRobustnessProofs.lean).  It should be moved to RegimeConsistency.lean and made
non-private:

```lean
-- MOVED from FaultRobustnessProofs.lean; made non-private
lemma deepValueQTypProperty_mono
    (h : ∀ σ ρ, P σ ρ → Q σ ρ) :
    deepValueQTypProperty P qt v → deepValueQTypProperty Q qt v
```

This provides backward compatibility: any site that only needs the regime part can
project it out via `deepValueQTypProperty_mono (fun _ _ h => h.1)`.

**Step 2 — strengthen `closureCapturedVarsRegime`** (RegimeConsistency.lean):

```lean
-- CHANGED: added θ; P strengthened from regime-only to regime ∧ typing
inductive closureCapturedVarsRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | intro :
      deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
        capturedVarsTypingProperty θ σcap ρcap) qt v →
      closureCapturedVarsRegime predSat R qt μ θ v
```

**Step 3 — thread `θ` through consumers** (signature changes only):

`consistentWithRegime` already has `θ` — it just threads it to `closureCapturedVarsRegime`:

```lean
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  -- conjuncts 1, 2 unchanged
  ...
  (∀ x qt v, ctx.varEnv.lookup x = some qt →
     ρ.lookup x = some v →
     closureCapturedVarsRegime predSat R qt μ θ v)  -- ← now receives θ
```

`valueConsistentWithRegime` and `trustedVarsClosureRegimeInit` gain `θ` and pass it
through to `closureCapturedVarsRegime`:

```lean
-- CHANGED: added θ parameter, threaded to closureCapturedVarsRegime
inductive valueConsistentWithRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | noTag :
      qtypGuardTag qt = none →
      closureCapturedVarsRegime predSat R qt μ θ v →
      valueConsistentWithRegime predSat R qt μ θ v
  -- (all other constructors: same pattern)
  ...

-- CHANGED: added θ parameter
inductive trustedVarsClosureRegimeInit
    (predSat : PredSat) (R : Regime) (s : InputSpec) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop where
  | intro :
      (∀ x qt v, ctx.varEnv.lookup x = some qt →
        ¬ s.vars.hasKey x → ρ.lookup x = some v →
        closureCapturedVarsRegime predSat R qt μ θ v) →
      trustedVarsClosureRegimeInit predSat R s ctx μ ρ θ
```

`valueConsistentWithRegime` must carry the strengthened `closureCapturedVarsRegime`
(not just the old regime-only version) because `consistentWithRegime_closure_body_start`
extracts it for the argument value `vArg` via
`valueConsistentWithRegime_closureCapturedVarsRegime`.  If extraction only gave the
regime part, the member-matching problem would resurface when building the body context.

### Dependency diagram (after)

```
agreeValueUnder_same (closure case)
│
│  needs: agreeCapturedEnv ... σcap env env
│           ├─ typing evidence for σcap's variables
│           └─ regime evidence for σcap's variables
│
└── Single source: consistentWithRegime (conjunct 3)
    └─ closureCapturedVarsRegime               [STRENGTHENED]
       └─ inverts deepValueQTypProperty
          └─ yields ONE σcap ∈ tcls
               │
               ├─ capturedVarsRegimeProperty (σcap, env)  ─── regime  ✓
               │    └─ derives MemberVarsRegimeEvidence
               │
               ├─ capturedVarsTypingProperty (σcap, env)  ─── typing  ✓
               │    ├─ henv  (valueHasETyp for σcap's vars)
               │    └─ hcover (coverage for σcap's vars)
               │
               └─ deep recursion (σcap, env)
                    └─ derives MemberCvcrEvidence
                       (via deepValueQTypProperty_mono,
                        projecting regime conjunct)

╔══════════════════════════════════════════════════════╗
║  Single σcap carries both typing and regime evidence ║
║  → agreeCapturedEnv gets everything it needs         ║
║  → no member-matching required                       ║
╚══════════════════════════════════════════════════════╝
```

#### Backward compatibility

Sites that only need the regime part project it out locally:

```
closureCapturedVarsRegime (strengthened, P = regime ∧ typing)
│
├── (full P) ─── agreeValueUnder_same         [uses both conjuncts]
│
└── deepValueQTypProperty_mono (h := fun _ _ ⟨r, _⟩ => r)
    └── deepValueQTypProperty regime-only     [for existing consumers]
```

No parallel definition hierarchy — one `closureCapturedVarsRegime`, one invariant.

### How this solves the member-matching problem

`agreeValueUnder_same` must gain `closureCapturedVarsRegime` as an explicit hypothesis
(currently it has none — the proof relied on the false `closure_same_config_tenv_env`):

```lean
private lemma agreeValueUnder_same
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap)
  (qt : QTyp) (v : Value)
  (hclean : qtypCleanUnder R qt)
  (htyp : valueHasETyp θ v qt.etyp)
  (hcvcr : closureCapturedVarsRegime predSat R qt μ θ v) :  -- ← NEW
  agreeValueUnder predSat R μ μ θ θ qt v v
```

The caller (`agreeOnClean_same_config`) extracts `hcvcr` from `consistentWithRegime`'s
conjunct 3, which now stores the strengthened `closureCapturedVarsRegime`.

When `agreeValueUnder_same` inverts `hcvcr` on a closure `v = Value.closure x body env`,
the `deepValueQTypProperty.closure` case yields a **single** `σcap` with:

- `FnTClosure.regular x body σcap ∈ tcls`
- `capturedVarsRegimeProperty predSat R μ σcap env` → derives `MemberVarsRegimeEvidence`
- `capturedVarsTypingProperty θ σcap env`:
  - `∀ y qt v, σcap.lookup y = some qt → env.lookup y = some v → valueHasETyp θ v qt.etyp`
    → provides `htyp1`, `htyp2` for `agreeCapturedEnv.cons_clean`
  - `∀ y qt, σcap.lookup y = some qt → ∃ v, env.lookup y = some v`
    → provides `hlookup1`, `hlookup2` for `agreeCapturedEnv`
- Deep recursion: for each captured `(y, qt_y, v_y)` in `(σcap, env)`:
  - `closureCapturedVarsRegime predSat R qt_y μ θ v_y` — sub-evidence for the recursive call
  - `valueHasETyp θ v_y qt_y.etyp` — from `capturedVarsTypingProperty`
  - → recursive `agreeValueUnder_same` call with these as inputs

All from the **same** `σcap`.  No member-matching needed.

### Resolving the mutual recursion (agreeCapturedEnv_same_toCaptured sorry)

Adding `closureCapturedVarsRegime` as input resolves a second problem: the existing
`agreeCapturedEnv_same_toCaptured` is admitted (sorry) to break mutual recursion with
`agreeValueUnder_same`.

With the new signature, the recursion follows the **structure of the
`closureCapturedVarsRegime` evidence tree** rather than cycling between two lemmas:

```
agreeValueUnder_same (hcvcr : closureCapturedVarsRegime qt v)
│
├── non-closure: trivial (deepValueQTypProperty.nonClosure)
│
└── closure v = Value.closure x body env:
    invert hcvcr → σcap, P(σcap, env), sub-evidence for each captured v_y
    │
    └── build agreeCapturedEnv ... σcap env env by iterating σcap:
        for each (y, qt_y) ∈ σcap with env.lookup y = v_y:
        │
        └── agreeValueUnder_same                  [structural recursion]
              (hcvcr := sub-evidence for v_y)     [strictly smaller sub-tree]
              (htyp := from capturedVarsTypingProperty)
```

This is well-founded structural induction on the `deepValueQTypProperty` tree.
No separate `agreeCapturedEnv_same_toCaptured` lemma is needed — the captured env
agreement is built inline, and each recursive call receives a strictly smaller sub-tree
of the input evidence.  The `ctx` and `ρ` parameters also drop from the signature (they
were only needed to connect to `consistentWithRegime`; now the evidence is self-contained).

### Why the strengthened invariant survives all transformations

The two conjuncts of `P = regime ∧ typing` have complementary stability properties —
between them, every standard transformation preserves both:

| Transformation | Regime conjunct | Typing conjunct |
|---|---|---|
| Regime monotonicity (`Regime.monotoneStep`) | Uses existing `_monotone` | Regime-independent — preserved for free |
| Memory transport (`transport_μ`) | Uses existing `_transport_μ` | Memory-independent — preserved for free |
| Map extension (`wfExtendsMap θ θ'`) | θ-independent — preserved for free | `valueHasETyp` is monotone in θ |
| Joins (`joinETyps`) | Original member persists in merged `tcls` | Same member, same evidence |
| Closure creation (`typecheckFn`) | Singleton `tcls` — trivial | From `runtimeInstantiatesCtx` |
| Non-closure values | `deepValueQTypProperty.nonClosure` — vacuous | Same — vacuous |

## 5. Affected Lemmas

### Definitions changed

| Definition | File | Change |
|---|---|---|
| `closureCapturedVarsRegime` | RegimeConsistency.lean | Add `θ` param; strengthen `P` to `regime ∧ typing` |
| `MemberCvcrEvidence` | FaultRobustness.lean | Add `θ` param (uses `closureCapturedVarsRegime`) |
| `consistentWithRegime` | RegimeConsistency.lean | Thread `θ` to `closureCapturedVarsRegime` (already has `θ`) |
| `valueConsistentWithRegime` | FaultRobustness.lean | Add `θ` param (flows to `closureCapturedVarsRegime`) |
| `trustedVarsClosureRegimeInit` | FaultRobustness.lean | Add `θ` param (flows to `closureCapturedVarsRegime`) |
| `agreeValueUnder` | FaultRobustness.lean | `clean_internal_arrow`/`clean_internal_parrow` constructors: `MemberCvcrEvidence` gains `θ` (`θ₁`/`θ₂` already in scope) |

### New definitions

| Definition | File | Purpose |
|---|---|---|
| `capturedVarsTypingProperty` | RegimeConsistency.lean | Typing evidence (`Nodup` + `hcover` + `henv`) |

### Moved definitions

| Definition | From | To | Change |
|---|---|---|---|
| `deepValueQTypProperty_monotone_P` | FaultRobustnessProofs.lean (private) | RegimeConsistency.lean (public) | Renamed `deepValueQTypProperty_mono` |

### Lemmas deleted (false)

| Lemma | File |
|---|---|
| `closure_same_config_tenv_env` | TypeSafety.lean |
| `peClosure_same_config_tenv_env` | TypeSafety.lean |

### Lemmas deleted (subsumed)

| Lemma | File | Reason |
|---|---|---|
| `agreeCapturedEnv_same_toCaptured` | FaultRobustnessProofs.lean | Was sorry; subsumed by structural recursion within `agreeValueUnder_same` |

### Lemmas rewritten

| Lemma | File | Change |
|---|---|---|
| `agreeValueUnder_same` | FaultRobustnessProofs.lean | Add `hcvcr` hypothesis; drop `ctx`/`ρ` params; structural recursion on evidence tree (see §4) |
| `agreeOnClean_same_config` | FaultRobustnessProofs.lean | Extract `closureCapturedVarsRegime` from `consistentWithRegime` and pass to `agreeValueUnder_same` |

### Lemmas requiring signature/body updates (ripple from definition changes)

**Signature-only updates** (thread `θ` into `closureCapturedVarsRegime` / `valueConsistentWithRegime` / `MemberCvcrEvidence`):

| Lemma / site | File |
|---|---|
| `valueConsistentWithRegime_closureCapturedVarsRegime` | FaultRobustnessProofs.lean |
| `consistentRegimeSpec_implies_consistentWithRegime` | FaultRobustnessProofs.lean |
| `consistentWithRegime_closure_body_start` | FaultRobustnessProofs.lean |
| `memberCvcrEvidence_of_toCaptured` | FaultRobustnessProofs.lean |
| `FaultRobustnessSpec` / `FaultRobustnessSpec_ioFree` | FaultRobustnessProofs.lean |
| All `agreeValueUnder` pattern matches | FaultRobustnessProofs.lean |

**Transport/monotonicity lemmas** (update to preserve both conjuncts):

| Lemma | File | Nature of change |
|---|---|---|
| `closureCapturedVarsRegime_monotone` | FaultRobustnessProofs.lean | Preserve typing conjunct (regime-independent, trivial) |
| `closureCapturedVarsRegime_transport_μ` | FaultRobustnessProofs.lean | Preserve typing conjunct (memory-independent, trivial) |
| `closureCapturedVarsRegime_transport_etyp` | FaultRobustnessProofs.lean | Preserve typing conjunct |
| `closureCapturedVarsRegime_transport_pred` | FaultRobustnessProofs.lean | Preserve typing conjunct |
| *(new)* `closureCapturedVarsRegime_transport_θ` | FaultRobustnessProofs.lean | New: transport across `wfExtendsMap θ θ'` (uses `valueHasETyp_extends`) |
| `consistentWithRegime_monotone` | FaultRobustnessProofs.lean | Flows from `closureCapturedVarsRegime_monotone` |
| `join_transport_consistentWithRegime` | FaultRobustnessProofs.lean | Flows from transport lemmas |
| `joinTypeResults_transport_consistentWithRegime_from_member` | FaultRobustnessProofs.lean | Flows from transport lemmas |

**Step theorems** (`stepFR_*`):

| Category | Lemmas | Change |
|---|---|---|
| Inherit from IH | `stepFR_seq`, `stepFR_vlet`, `stepFR_assign`, `stepFR_kwhile` | Thread `θ'` (already in scope) |
| Non-closure results | `stepFR_literal`, `stepFR_op`, `stepFR_unaryop`, `stepFR_newRef`, `stepFR_ite_*` | `deepValueQTypProperty.nonClosure` makes both conjuncts vacuous |
| Closure creation | `stepFR_fn`, `stepFR_pfn` | Singleton `tcls` — build typing conjunct from `runtimeInstantiatesCtx` |
| Value extraction | `stepFR_var`, `stepFR_deref` | Extract strengthened `closureCapturedVarsRegime` from `consistentWithRegime` |
| **Beneficiary** | `stepFR_app` | Goes from *stuck* to *provable* |
