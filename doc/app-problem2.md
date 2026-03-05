# Body StepFR IH Evidence Blocker

Analysis of the remaining blockers for `stepFR_app` completion.

**Scope**: Only `stepFR_app` and its direct dependency chain.  Excludes `stepFR_ite_*`,
`stepFR_kwhile`, and their preservation sub-cases — those are separate concerns.

## Current Status (2026-03-05)

**Original blocker**: StepFR IH requires two runs evaluating the SAME expression, but the
dirty-outer path (`p1=true`) may have different closure bodies.

**Resolution status**: The per-run approach (`StepFR_single_run` + membership transport)
works for all per-run obligations.  Cross-run `agreeOnClean` **variables conjuncts** are
now fully proved for both arrow and parrow `¬qtypCleanUnder` paths.  The remaining
concentrated blocker is **cross-run `agreeOnClean` locations conjuncts** — 2 narrowed sorry
sites (arrow line ~26646, parrow line ~29242).

Additionally, preservation lemma infrastructure is partially built:
`typecheckExpr_preserves_wfTagMeaningCtx` has a partial fuel induction proof (trivial cases,
chain cases, and ite proved; vlet/newRef/assign/app remain as sorry within the app dependency
chain).  `typecheckExpr_preserves_QTypRespectsTagMeaning` remains as a full sorry.

### App-chain sorry inventory

| # | Line | Location | Blocker |
|---|------|----------|---------|
| 1 | 17961 | `wfTagMeaningCtx` vlet (hwf_mid) | Needs combined induction with QTypRespectsTagMeaning |
| 2 | 17975 | `wfTagMeaningCtx` newRef | Needs QTypRespectsTagMeaning for stored pred |
| 3 | 17977 | `wfTagMeaningCtx` assign | Needs structure extension + QTypRespectsTagMeaning |
| 4 | 18044 | `wfTagMeaningCtx` app | Deep (closure body context well-formedness) |
| 5 | 18061 | `QTypRespectsTagMeaning` | Full sorry (~500 lines, fuel induction) |
| 6 | 25948 | arrow dirty-internal | Per-run body IH restructuring |
| 7 | 26646 | arrow `agreeOnClean` locations | Guard-clean entry analysis |
| 8 | 28503 | parrow dirty-internal | Mirror of #6 |
| 9 | 29242 | parrow `agreeOnClean` locations | Mirror of #7 |

Note: sorrys #1-5 feed into `applyFnTClosure_ok_wfTagMeaningCtx` /
`applyFnTClosure_ok_QTypRespectsTagMeaning` and their PFnTClosure mirrors (4 sorry lemmas
total that depend on the fuel induction being complete for the relevant cases).

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
10. **`applyFnTClosure_ok_regimeConsistentWithCtx`** and PFnTClosure mirror — proved ✓
11. **`typecheckExpr_preserves_wfTagMeaningCtx` partial proof** — proved ✓
    Fuel induction covering: num, bool, unit, str, var (all pred variants), fn, pfn,
    extern* (impossible), rand/frand/print* (impossible), unaryop, deref, op, seq,
    ite (all 4 modes).  Uses `EnvRespectsTagMeaning_joinMemEnvsStrong'` for join cases,
    `EnvRespectsTagMeaning_mix` for vlet final transport.

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
| Dirty internal | false | false | **Not guaranteed** | Sorry #6 |
| Dirty outer | true | n/a | **No** | Sorrys #7, #9 (narrowed) |

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

#### Arrow and parrow `¬qtypCleanUnder` paths (p1 = true) — sorrys #7, #9

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

#### Dirty-internal (¬internalPoisonClean, p1=false) — sorrys #6, #8

Same structure as dirty-outer: both may have different closures. Need per-run body IH via
`StepFR_single_run`. Additionally, `resultAgreesIfClean` for the result type is non-vacuous
(unlike dirty-outer where it's vacuous via `dirty_noPred_arrow`).

The dirty-internal sorry currently uses `θ₀1, θ₁1` (pre-body maps) as witnesses. Needs
restructuring to use `θ₀_body, θ₁_body` (post-body maps from `StepFR_single_run`).

## 4. Preservation Lemmas (app dependency chain)

### RESOLVED: `regimeConsistentWithCtx` preservation

The `applyFnTClosure_ok_regimeConsistentWithCtx` and PFnTClosure mirrors are **fully proved**.
The circular dependency in `typecheckExpr_preserves_regimeConsistentWithCtx_main` was resolved
by inlining helper logic using `IH'` from strong induction.

### IN PROGRESS: `wfTagMeaningCtx` and `QTypRespectsTagMeaning`

`typecheckExpr_preserves_wfTagMeaningCtx_main` is partially proved via fuel induction
(~200 lines). Completed expression cases: num, bool, unit, str, var, fn, pfn, extern*, rand,
frand, print*, unaryop, deref, op, seq, ite (all 4 modes). Remaining sub-sorrys in the app
dependency chain: **vlet, newRef, assign, app** (sorrys #1-4 above).

**Mutual dependency discovered**: `wfTagMeaningCtx` and `QTypRespectsTagMeaning` have a
circular dependency through the `vlet` case:
- `wfTagMeaningCtx` for the extended context needs `QTypRespectsTagMeaning` for the new binding
- `QTypRespectsTagMeaning` for seq/vlet results needs `wfTagMeaningCtx` for intermediate contexts

**Resolution approach**: Combine both into a single strong induction returning
`wfTagMeaningCtx ∧ QTypRespectsTagMeaning`. This mirrors the approach used for
`regimeConsistentWithCtx`.

**Current sub-sorrys in `_main`** (app-relevant):

| Sub-sorry | Blocker | Effort |
|-----------|---------|--------|
| vlet (hwf_mid) | QTypRespectsTagMeaning for result1.qualType | Combined induction |
| newRef | QTypRespectsTagMeaning for stored pred | Combined induction |
| assign | Structure lemma extension + QTypRespectsTagMeaning | Combined induction + ~50 lines |
| app | Closure body context well-formedness | Deep (uses IH' on body) |

**`StepFR_single_run` cannot be used** for non-executed closure alternatives (no
`terminatesTo` witness). Previously tried and rejected (deleted in 02e7fcb).

### Paths forward

1. **Combined fuel induction** for `wfTagMeaningCtx ∧ QTypRespectsTagMeaning`: Would
   resolve vlet, newRef, assign (3 sub-sorrys). Estimated ~100-200 additional lines on
   top of existing proof.

2. **App case via IH'**: The body is typechecked at smaller fuel, so IH' applies. The
   challenge is establishing `wfTagMeaningCtx tm bodyCtx` for the closure body context
   (captured vars + argument). This requires knowing captured vars' guard descs are in `tm`.

## 5. Summary

| Step | Status | Remaining effort |
|------|--------|-----------------|
| `StepFR_single_run` | **DONE ✓** | — |
| Per-run body evidence | **DONE ✓** | — |
| Transport to joined result | **DONE ✓** (except agreeOnClean locations) | — |
| `agreeOnClean` variables conjuncts | **DONE ✓** (both arrow and parrow) | — |
| `agreeOnClean` locations conjuncts | 2 narrowed sorrys (#7, #9) | 100–300 lines |
| Dirty-internal per-run body IH | 2 sorrys (#6, #8) | 200–400 lines |
| `wfTagMeaningCtx` partial proof | **DONE ✓** (4 app-chain sub-sorrys remain: #1-4) | — |
| Combined `wfTagMeaningCtx ∧ QTypRespects` | Not started (resolves #1-3, #5) | 100–200 lines |
| `wfTagMeaningCtx` app sub-case | sorry #4 | 100–200 lines |
| **Total remaining in app chain** | 9 sorrys | **~500–1100 lines** |

## 6. Implementation Order (recommended)

1. **Combined `wfTagMeaningCtx ∧ QTypRespectsTagMeaning` induction** — resolves sorrys
   #1-3 (vlet, newRef, assign sub-cases) and #5 (full QTypRespectsTagMeaning sorry).
   Estimated ~100-200 lines of restructuring.

2. **App case in `_main`** via IH' on closure body — resolves sorry #4.
   Requires establishing `wfTagMeaningCtx tm bodyCtx` from closure captured vars evidence.
   Estimated ~100-200 lines.

3. **Dirty-internal per-run body IH** (sorrys #6, #8) — restructure to use
   `StepFR_single_run` with `θ₀_body, θ₁_body` witnesses.

4. **`agreeOnClean` locations conjuncts** (sorrys #7, #9) — analyze guard-clean entry
   preservation through joins, prove locations trace back to pre-call state.

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

### Key technique: wfTagMeaningCtx preservation (ite case)

The ite case for `typecheckExpr_preserves_wfTagMeaningCtx` splits into 4 modes:

- **Modes 1/2** (single branch): `res.memEnv' = resBranch.memEnv'` — direct from IH on the
  active branch. `wfTagMeaningCtx` only depends on `varEnv` and `memEnv`; since `tagEnv`
  changes don't affect it, the branch context has `wfTagMeaningCtx = hwf`.

- **Modes 3/4** (join): `res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv'` — uses
  `EnvRespectsTagMeaning_joinMemEnvsStrong'` which only needs the LEFT side's evidence.
  For mode 4, IH on e1 provides `wfTagMeaningCtx` for the intermediate context
  (same varEnv, updated memEnv).
