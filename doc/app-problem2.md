# Body StepFR IH Evidence Blocker

Analysis of the main remaining blocker for `stepFR_app` completion.

## Current Status (2026-03-05)

**Original blocker**: StepFR IH requires two runs evaluating the SAME expression, but the
dirty-outer path (`p1=true`) may have different closure bodies.

**Resolution status**: The per-run approach (`StepFR_single_run` + membership transport)
works for all per-run obligations.  Cross-run `agreeOnClean` **variables conjuncts** are
now fully proved for both arrow and parrow `¬qtypCleanUnder` paths.  The remaining
concentrated blocker is **cross-run `agreeOnClean` locations conjuncts** — 2 narrowed sorry
sites (arrow line 26124, parrow line 28720).

Additionally, 4 preservation lemma sorrys (`wfTagMeaningCtx` / `QTypRespectsTagMeaning`
for FnTClosure and PFnTClosure) and 2 dirty-internal sorrys remain.

### Sorry inventory (stepFR_app dependency chain only)

| # | Line | Location | Status |
|---|------|----------|--------|
| 1 | 17673 | `applyFnTClosure_ok_wfTagMeaningCtx` | Needs `typecheckExpr_preserves_wfTagMeaningCtx` |
| 2 | 17745 | `applyFnTClosure_ok_QTypRespectsTagMeaning` | Needs `typecheckExpr_preserves_QTypRespectsTagMeaning` |
| 3 | 18391 | `applyPFnTClosure_ok_wfTagMeaningCtx` | Mirror of #1 |
| 4 | 18460 | `applyPFnTClosure_ok_QTypRespectsTagMeaning` | Mirror of #2 |
| 5 | 25426 | arrow dirty-internal pack (¬internalPoisonClean) | Needs per-run body IH |
| 6 | 26124 | arrow `agreeOnClean` **locations only** | Variables proved; locations sorry |
| 7 | 27981 | parrow dirty-internal | Needs per-run body IH |
| 8 | 28720 | parrow `agreeOnClean` **locations only** | Variables proved; locations sorry |

### Completed

1. **`StepFR_single_run`** — proved ✓
2. **Parrow clean shared path** — proved ✓
3. **Parrow ¬qtypCleanUnder full 15-element StepFR tuple** — proved ✓
4. **`regimeConsistentWithCtx` preservation (app case)** — proved ✓
   (circular dependency resolved by inlining with `IH'` from strong induction)
5. **Arrow dirty-internal structure** — investigated; confirmed NOT contradictory ✓
6. **Various transport/membership lemmas** for join infrastructure ✓
7. **Arrow `agreeOnClean` variables conjunct** (¬qtypCleanUnder path) — proved ✓
   Uses `cleanUnder_of_monotone` + `agreeValueUnder_clean_extends` + `agreeValueUnder_clean_monotoneRegime`
8. **Parrow `agreeOnClean` variables conjunct** (¬qtypCleanUnder path) — proved ✓
   Mirror of arrow; accounts for `subst heq_cfg₀ heq_cfg₁` consuming config equalities
9. **Made `joinTypeResults_regime_monotone`, `applyFnTClosure_regime_mono`,
   `applyPFnTClosure_regime_mono` public** in TypeSafety.lean ✓

### Key technique: agreeOnClean variables conjunct proof

The variables conjunct for `agreeOnClean` at `ctxAfter ctxᵢ res` (joined result) uses a
two-step transport:

1. **Regime monotonicity chain**: Establish `Regime.monotoneStep result1.regime' res.regime'`
   via `List.mapM_Except_preserves_property` (each `applyFnTClosure`/`applyPFnTClosure` result
   is monotone) + `joinTypeResults_regime_monotone`.

2. **Backward transport**: For clean variables in the joined result:
   - `cleanUnder_of_monotone h_mono_res` → clean at `result1.regime'`
   - `ctxAfter ctxᵢ res` has `varEnv = ctxᵢ.varEnv` (unchanged by body)
   - Pre-call `hagree1.2` gives `agreeVarUnder` at pre-call regime
   - `agreeValueUnder_clean_extends` transports through θ extension (memory/θ change)
   - `agreeValueUnder_clean_monotoneRegime` transports through regime change

## 1. Background: How Function Application Works

### Ott spec rules

The Poison type system handles function application with **closure alternatives**.  A function
type carries a list of typed closures:

```
ST1 -> ST2 # p tclosures tcls          (arrow / impure)
ST1 -> ST2 # p tpclosures ptcls        (parrow / pure)
```

The list `tcls` arises because the typechecker doesn't know which branch created the closure
(e.g., `if cond then (fun x -> e1) else (fun x -> e2)` yields two alternatives).

**Multi-closure rules**: The typechecker evaluates each closure's body, then **joins** the
post-call contexts conservatively: `JoinGStrong` (memory) drops single-sided predicates,
`JoinL` (tags) keeps only entries that agree, `JoinR` (regime) keeps only entries that agree.

### The three cases in the FR proof

| Case | `p1` | `internalPoisonClean` | Both runs pick same closure? | Status |
|------|------|-----------------------|-----------------------------|--------|
| Clean | false | true | Yes | **DONE ✓** |
| Dirty internal | false | false | **Not guaranteed** | Sorry #5 |
| Dirty outer | true | n/a | **No** | Sorrys #6, #8 (narrowed) |

**KEY FINDING**: `p` (internal poison in ETyp.arrow/parrow) ≠ `p1` (external poison in QTyp).
`qtypCleanUnder.guard` requires `isFunctionType=false`, so only `qtypCleanUnder.clean` applies
→ `p1=false`.  But `¬internalPoisonClean` means `p=true` (different variable!).  Both
dirty-internal sorrys genuinely need per-run body IH infrastructure.

**CORRECTION (2026-03-05)**: The dirty-internal case does NOT have shared closure info.
`agreeValueUnder.dirty_internal_arrow` only requires `valueHasETyp` for both values — it
does NOT guarantee `body₀ = body₁`. So the dirty-internal case may have different closures,
same as the dirty-outer case. Both need per-run body IH via `StepFR_single_run`.

The difference: dirty-internal has `p1=false` so `resultAgreesIfClean` for the result type
may be non-vacuous (guard-clean results possible). Dirty-outer has `p1=true` and
`res.qualType.poison=true, pred=noPred` so `resultAgreesIfClean` is vacuous.

For dirty-internal, `res.qualType.poison = true` because `joinPoison p1 (joinPoison p ...)
= joinPoison false (joinPoison true ...) = true`. So `resultAgreesIfClean` is non-vacuous
only via guard (needs guard tag in result predicate + `R[k] = some true`). The
`dirty_internal_arrow` constructor of `agreeValueUnder` can handle this since the result
type should NOT be a function type.

## 2. Problem Statement

The `StepFR` proof obligation requires **two runs evaluating the SAME expression**.  The IH
from the fuel induction gives `StepFR` for sub-expressions at smaller fuel.

In the **clean** path, both runs share the same closure (from `agreeValueUnder.clean_internal_arrow`).
StepFR IH applies directly.

In the **dirty internal** and **dirty outer** paths, the two runs may pick **different**
closure alternatives.  Since StepFR IH requires both runs to evaluate the same expression,
it cannot be applied when the body expressions differ. Both paths need per-run
`StepFR_single_run`.

## 3. Approach: Single-Run Corollary + Membership Transport

### Step 1: `StepFR_single_run` — DONE ✓

Proved as a corollary of `StepFR` via self-agreement using `agreeOnClean_same_config`.
Gives 9-element output tuple (θ', valueHasETyp, runtimeInstantiatesCtx,
consistentWithRegime, valueConsistentWithRegime, wfTagMeaningCtx, wfTypeContext,
regimeConsistentWithCtx, wfConfig).

### Step 2: Per-run body evidence via member chain — DONE ✓

For each run independently:
1. `valueHasETyp.closure` → FnTClosure membership
2. `applyFnTClosure_regular_inv_of_mapM_mem` → body typing extraction
3. Construct body context + establish prerequisites
4. Apply `StepFR_single_run` → post-body evidence
5. `applyFnTClosure_ok_of_mem_mapM` → TypeResult membership

### Step 3: Transport per-run evidence to joined result — DONE for most obligations ✓

| Obligation | Transport lemma | Status |
|-----------|----------------|--------|
| `valueHasETyp` | `joinTypeResults_transport_valueHasETyp_from_member` | Done ✓ |
| `consistentWithRegime` | `joinTypeResults_transport_consistentWithRegime_from_member` | Done ✓ |
| `valueConsistentWithRegime` | `joinTypeResults_transport_valueConsistentWithRegime_from_member` | Done ✓ |
| `runtimeInstantiatesCtx` | Composite (memEnv containment + varEnv extension) | Done ✓ |
| `wfConfig` | Direct from body IH | Done ✓ |
| `agreeOnClean` (variables) | Via regime monotonicity chain + backward transport | **Done ✓** |
| `agreeOnClean` (locations) | Needs guard-clean entry analysis | **BLOCKED** (Step 5) |

### Step 4: Cross-run `agreeOnClean` locations conjunct — THE REMAINING BLOCKER

#### Arrow and parrow `¬qtypCleanUnder` paths (p1 = true) — sorrys #6, #8

The variables conjuncts are now fully proved. The **locations conjuncts** remain.

For each guard-clean location `l` in `res.memEnv'`, we need to show either:
- `agreeLocUnder.agree_values`: both θs realize `l`, and the values agree
- `agreeLocUnder.both_unrealized`: neither θ realizes `l`

**Investigation results** (from agent analysis):
- Guard-clean entries CAN exist in `res.memEnv'` when `p1=true` — NOT vacuously true
- Pre-existing entries that all alternatives leave intact survive with their guard predicates
- Fresh realized locations need cross-run body IH (genuine blocker for different bodies)
- For pre-existing locations: body execution can still modify runtime values at addresses

**Approach options**:
1. Show guard-clean locations in the join trace back to unmodified pre-existing entries
   where pre-call agreement carries over
2. For fresh locations: show they are unrealized in both θs (since body allocated them
   after θ₀_body/θ₁_body were established)

#### Dirty-internal (¬internalPoisonClean, p1=false) — sorrys #5, #7

Same structure as dirty-outer: both may have different closures. Need per-run body IH via
`StepFR_single_run`. Additionally, `resultAgreesIfClean` for the result type is non-vacuous
(unlike dirty-outer where it's vacuous via `dirty_noPred_arrow`).

The dirty-internal sorry at line 25426 currently uses `θ₀1, θ₁1` (pre-body maps) as
witnesses. Needs restructuring to use `θ₀_body, θ₁_body` (post-body maps from
`StepFR_single_run`).

## 4. Preservation Lemmas (sorrys #1-4)

Four preservation lemmas with sorry:

| Lemma | Line | Goal |
|-------|------|------|
| `applyFnTClosure_ok_wfTagMeaningCtx` | 17673 | `wfTagMeaningCtx tm (ctxAfter ctx r)` |
| `applyFnTClosure_ok_QTypRespectsTagMeaning` | 17745 | `QTypRespectsTagMeaning tm r.qualType` |
| `applyPFnTClosure_ok_wfTagMeaningCtx` | 18391 | same, PFnT version |
| `applyPFnTClosure_ok_QTypRespectsTagMeaning` | 18460 | same, PFnT version |

### RESOLVED: `regimeConsistentWithCtx` preservation

The `applyFnTClosure_ok_regimeConsistentWithCtx` and PFnTClosure mirrors are **fully proved**.
The circular dependency in `typecheckExpr_preserves_regimeConsistentWithCtx_main` was resolved
by inlining helper logic using `IH'` from strong induction.

### Remaining: `wfTagMeaningCtx` and `QTypRespectsTagMeaning`

These need general `typecheckExpr_preserves_*` theorems (~500 lines each, fuel induction over
all expression forms).  The same circular dependency approach (inline with `IH'`) applies.

`StepFR_single_run` **cannot** be used for non-executed closure alternatives (no
`terminatesTo` witness).  Previously tried and rejected (deleted in 02e7fcb).

### Paths forward

1. **Purely static proofs** (typechecker fuel induction): Follow the pattern of
   `typecheckExpr_preserves_wfTypeResult` and `typecheckExpr_preserves_regimeConsistentWithCtx`.

2. **Refine-block restructuring**: `join_transport_wfTagMeaningCtx` only needs the first
   member.  If the executed member happens to be the first, `StepFR_single_run` suffices.

## 5. Summary

| Step | Status | Remaining effort |
|------|--------|-----------------|
| `StepFR_single_run` | **DONE ✓** | — |
| Per-run body evidence | **DONE ✓** | — |
| Transport to joined result | **DONE ✓** (except agreeOnClean locations) | — |
| `agreeOnClean` variables conjuncts | **DONE ✓** (both arrow and parrow) | — |
| `agreeOnClean` locations conjuncts | 2 narrowed sorrys | 100–300 lines |
| Dirty-internal per-run body IH | 2 sorrys (arrow + parrow) | 200–400 lines |
| Preservation lemmas (#1-4) | Not started | 100–500 lines (static induction) |
| **Total remaining** | 8 sorrys in stepFR_app chain | **~400–1200 lines** |

## 6. Implementation Order

1. **Dirty-internal per-run body IH** (sorrys #5, #7) — restructure to use `StepFR_single_run`
   with `θ₀_body, θ₁_body` witnesses. Similar to `¬qtypCleanUnder` path but `resultAgreesIfClean`
   needs `dirty_internal_arrow`/`dirty_internal_parrow` constructor.
2. **`agreeOnClean` locations conjuncts** (sorrys #6, #8) — analyze guard-clean entry
   preservation through joins, prove locations trace back to pre-call state.
3. **`typecheckExpr_preserves_wfTagMeaningCtx`** — static fuel induction (~500 lines).
4. **`typecheckExpr_preserves_QTypRespectsTagMeaning`** — similar.
