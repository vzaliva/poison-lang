# Body StepFR IH Evidence Blocker

Analysis of the main remaining blocker for `stepFR_app` completion.

## Problem Statement

The `StepFR` proof obligation (via `TypeSystemEnforcesFaultRobustness_step_spec`) requires
**two runs evaluating the SAME expression** with possibly different starting configs.  The IH
from the fuel induction gives us `StepFR` for all sub-expressions at smaller fuel.

In the **arrow clean path** (shared closure), both runs evaluate the same body expression from
the same closure member.  The StepFR IH applies directly to `(body, body)` with `(cf₀, cf₁)`,
giving all required obligations.

In the **fallback paths** (¬ `qtypCleanUnder`, ¬ `internalPoisonClean`) and the **parrow
body-dependent path**, the two outer runs may pick **different** closure alternatives at
runtime.  Since StepFR IH requires both runs to evaluate the **same** expression, it cannot be
applied directly when the body expressions differ.

## Affected Obligations

### Arrow ¬ `internalPoisonClean` fallback (line ~24544)

One sorry wrapping a 10-element pack.  The `dirty_internal_arrow` constructor of
`agreeValueUnder` only needs `valueHasETyp` for both runs (plus `¬ internalPoisonClean` and
`isArrow`, which are in scope).  So the pack's `resultAgreesIfClean` can be closed by
`dirty_internal_arrow`, **if** we can provide `valueHasETyp θ₀' o₀ etyp` and
`valueHasETyp θ₁' o₁ etyp`.

The remaining 9 pack fields (runtimeInstantiatesCtx ×2, consistentWithRegime ×2, agreeOnClean,
valueConsistentWithRegime ×2, wfTagMeaningCtx, wfTypeContext) also need body evaluation
evidence.

### Arrow ¬ `qtypCleanUnder` fallback (lines ~24578–24586)

9 sorrys.  Available facts: `p1 = true`, `res.poison = true`, `res.pred = noPred`.

| # | Obligation | Notes |
|---|-----------|-------|
| 1-2 | `valueHasETyp θ₀1 o₀ / θ₁1 o₁` | Needs body IH; θ₀1 is pre-body |
| 3-4 | `runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀ / cf₁` | Needs body evaluation evidence |
| 5-6 | `consistentWithRegime … cf₀ / cf₁` | Deep closure invariant |
| 7 | `agreeOnClean` | Cross-run agreement |
| 8-9 | `valueConsistentWithRegime … cf₀ o₀ / cf₁ o₁` | Deep closure invariant |

Note: `resultAgreesIfClean` is already proved vacuously via
`resultAgreesIfClean_of_poison_noPred`.

### Parrow refine block (lines ~25216–25249) + body IH paths (lines ~25317, 25319)

9 sorrys in refine block (same structure as arrow fallback: valueHasETyp ×2,
runtimeInstantiatesCtx ×2, consistentWithRegime ×2, agreeOnClean,
valueConsistentWithRegime ×2) plus 2 sorrys for the parrow clean/dirty split.

The parrow clean path (line 25317) is the analog of the arrow clean path — both runs share the
same body.  The dirty path (line 25319) is the analog of `dirty_internal_parrow`.

## Root Cause Analysis

All these sorrys share one root cause: **we need per-run post-body evidence, but the StepFR IH
only provides post-body evidence for a _pair_ of runs evaluating the _same_ expression**.

The fallback paths handle cases where the two outer runs may select different closure members.
Even though the _joined_ typing result is available, linking it to the individual runs' post-body
states requires evidence from body evaluation — evidence that StepFR IH can only provide when
both runs use the same body.

## Proposed Approaches

### Approach A: Self-Agree (apply StepFR IH to same body, same config)

**Core idea**: For each run independently, apply StepFR IH to `(body_i, body_i)` — the same
body expression with `cf₀ = cf₁ = cf_i_start` (same starting config for both "runs").

Since evaluation is deterministic (fuel-based, same fuel), both "runs" produce the same output.
StepFR IH returns all single-run invariants: `θ_body_i`, `valueHasETyp`, `runtimeInstantiatesCtx`,
`consistentWithRegime`, `valueConsistentWithRegime`.

**What this gives**: All single-run obligations (items 1–6, 8–9 in the table above) for each
run independently.

**What this does NOT give**: Cross-run `agreeOnClean` (item 7), because the self-agree StepFR IH
only gives agreement between the same run and itself — not between two different runs.

**Prerequisites**:
1. For each run, extract its specific closure member from the runtime evidence (`terminatesTo`
   for the app expression decomposes into: function evaluation → argument evaluation → body
   evaluation for a specific closure member).
2. Extract the typechecking result for that specific member via `applyFnTClosure_regular_inv`
   (or parrow equivalent).
3. Build the StepFR IH preconditions for the body: `wfTagMeaningCtx` for body context
   (`wfTagMeaningCtx_closure_body`), `runtimeInstantiatesCtx` for body start, etc.
4. Apply StepFR IH to get member-level post-body evidence.
5. Transport member-level evidence to joined result via existing `joinTypeResults_transport_*`
   lemmas.

**Complexity**: Medium.  The plumbing for steps 1–3 already exists in the arrow clean path;
the difference is just using each run's own member instead of the shared one.

### Approach B: Poisoned-PC argument for `agreeOnClean`

**Core idea**: In the ¬ `qtypCleanUnder` fallback, `p1 = true` (function result is poisoned),
which means the body's program-counter poison (`pc`) is true.  Under `pc = true`, the
typechecker marks **all** new variables and locations as poisoned (their QTyp has `poison = true`
or they are tagged dirty in the regime).

Therefore, no **new** clean entries appear in the post-body `ctxAfter ctx res`.  All clean
entries in `ctxAfter ctxᵢ res` must already have been present (and clean) in the pre-body
context `ctxᵢ`.  Pre-body `agreeOnClean` is already available, so post-body `agreeOnClean`
follows.

**Formal argument sketch**:
1. Show that `joinTypeResults` preserves "no new clean entries" when all member results come
   from pc=true body evaluations.
2. More precisely: for any `(l, qt)` in `(ctxAfter ctxᵢ res).memEnv` with `qtypCleanUnder`
   holding, either `(l, qt') ∈ ctxᵢ.memEnv` (and the agreement follows from pre-body
   `agreeOnClean`), or `qt` is dirty (contradiction with `qtypCleanUnder`).
3. Similarly for varEnv entries.

**Risk**: The argument depends on showing that `joinTypeResults` of pc=true evaluations doesn't
create clean entries.  This requires understanding how `normalizeAppResultByProvenance` interacts
with `joinTypeResults`, and how the typechecker's body result interacts with the closure context.
The `normalizeAppResultByProvenance` sets `poison := true, pred := noPred` when `p1 = true`,
but this only affects the **result qualType**, not the **memEnv** entries.  The memEnv entries
come from `typecheckExpr body ...` which runs with poisoned `pc` — the typechecker propagates
`pc` into all new allocations and assignments, so new memEnv entries should indeed be dirty.

**Complexity**: Medium–High.  Needs a new lemma about typechecker pc-propagation into memEnv
entries.  But this is a purely static (typechecker-level) property, similar to
`typecheckExpr_preserves_wfTypeResult`.

### Approach C: Single-Run Preservation theorem

**Core idea**: Extract the single-run part of `StepFR` as a separate theorem proved by fuel
induction, parallel to `StepFR` but simpler (no agreement obligations).

```
def SingleRunPreservation (mode ctx e res predSat tm) : Prop :=
  PredSatLaws predSat tm →
  wfTagMeaningCtx tm ctx →
  ∀ μ ρ θ cf o,
    wfRealizationMap θ → wfTypeContext ctx →
    runtimeInstantiatesCtx ctx μ ρ θ →
    regimeConsistentWithCtx ctx → regimeBounded ctx.regime →
    consistentWithRegime predSat ctx.regime ctx μ ρ θ →
    wfConfig ⟨μ, ρ, a, pm⟩ →
    terminatesTo mode e ⟨μ, ρ, a, pm⟩ cf o →
    ∃ θ', wfExtendsMap θ θ' ∧
      valueHasETyp θ' o res.qualType.etyp ∧
      runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
      consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ' o ∧
      wfConfig cf
```

This is strictly weaker than `StepFR` (it follows from `StepFR` by setting both runs to the
same config).  But proving it from scratch by fuel induction might be simpler than full `StepFR`,
since it avoids all agreement reasoning.

**Advantage over Approach A**: Avoids the overhead of "self-agree" (which requires providing
`agreeOnClean` for a single config with itself — trivially true, but still requires plumbing
through all the constructors).

**Disadvantage**: Duplicates the entire `StepFR` fuel induction (~25K lines in
FaultRobustnessProofs.lean), just with simpler conclusions.

**Variant**: Derive `SingleRunPreservation` from `StepFR` as a corollary rather than proving
independently.  This only requires showing the self-agree preconditions hold
(`agreeOnClean` with itself is trivially true by reflexivity).

### Approach D: Derive from StepFR via self-agree corollary

**Core idea**: The cleanest approach.  Prove a lemma:

```lean
lemma StepFR_single_run
  (hStepFR : StepFR mode ctx e res predSat tm)
  (hPredSat : PredSatLaws predSat tm) (hTm : wfTagMeaningCtx tm ctx)
  (hwf_θ : wfRealizationMap θ) (hwf_ctx : wfTypeContext ctx)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (hreg : regimeConsistentWithCtx ctx) (hbound : regimeBounded ctx.regime)
  (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (hwf_cf : wfConfig ⟨μ, ρ, a, pm⟩)
  (hterm : terminatesTo mode e ⟨μ, ρ, a, pm⟩ cf o) :
  ∃ θ', wfExtendsMap θ θ' ∧ … :=
```

**Proof**: Apply `hStepFR` with `μ₀ = μ₁ = μ`, `ρ₀ = ρ₁ = ρ`, `θ₀ = θ₁ = θ`,
`cf₀ = cf₁ = cf`, `o₀ = o₁ = o`, and `hterm₀ = hterm₁ = hterm`.

The only non-trivial precondition is `agreeOnClean predSat R ctx μ ρ θ μ ρ θ` (self-agreement).
This should be provable by:
- For locations: `agreeLocUnder` with the same memory and θ → same lookup → values agree trivially
- For variables: `agreeVarUnder` with the same env and θ → same variable → values agree trivially

Specifically, need `agreeOnClean_self`:
```lean
lemma agreeOnClean_self (predSat R ctx μ ρ θ)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ) :
  agreeOnClean predSat R ctx μ ρ θ μ ρ θ
```

This should follow from `agreeValueUnder_same` (already proved!) and the structure of
`agreeOnClean` (which requires `agreeLocUnder` / `agreeVarUnder` for clean entries).

**Complexity**: Low–Medium.  Main work is proving `agreeOnClean_self` and then `StepFR_single_run`
is straightforward.  Then the fallback paths use `StepFR_single_run` per-run + Approach B for
cross-run agreeOnClean.

## Recommended Strategy

**Approach D + B** (recommended):

1. **Prove `agreeOnClean_self`** — show any config agrees with itself on clean entries.
   Uses `agreeValueUnder_same` (already proved) for the value-level agreement, plus
   `agreeLocUnder` / `agreeVarUnder` reflexivity.

2. **Prove `StepFR_single_run`** — corollary of `StepFR` via self-agree.  Instantiate both
   runs as the same config, use `agreeOnClean_self` for the self-agreement precondition.
   This gives us per-run post-body evidence.

3. **Apply `StepFR_single_run`** in the fallback paths — for each run independently, extract
   the body typechecking result via `applyFnTClosure_regular_inv` / `applyPFnTClosure_regular_inv`,
   apply `StepFR_single_run` to get post-body `θ_body_i`, `valueHasETyp`, etc.

4. **Transport member-level evidence to joined result** — use existing
   `joinTypeResults_transport_*` lemmas.

5. **Prove cross-run `agreeOnClean` for fallback paths** — use Approach B (pc-based argument)
   for ¬ `qtypCleanUnder`.  For ¬ `internalPoisonClean` (where `qtypCleanUnder` DOES hold),
   the body is shared (same body expression for both runs), so the existing arrow clean path
   logic applies.

**Note on ¬ `internalPoisonClean`**: Re-examining line 24543: this branch has `qtypCleanUnder`
holding (it's the ELSE of the ¬ `qtypCleanUnder` case) but `¬ internalPoisonClean`.  The
`dirty_internal_arrow` constructor of `agreeValueUnder` only needs `valueHasETyp`.  The rest
of the pack (runtimeInstantiatesCtx, consistentWithRegime, agreeOnClean) should come from
the **shared body** path (since `qtypCleanUnder` holds ↔ `p1 = false` ↔ the existing
clean-path sync logic applies).  The only thing different from the clean path is the
`resultAgreesIfClean` construction, which uses `dirty_internal_arrow` instead of the full
clean constructor.

## Effort Estimate

| Step | Lines (est.) | Risk |
|------|-------------|------|
| `agreeOnClean_self` | 50–100 | Low (structural; `agreeValueUnder_same` exists) |
| `StepFR_single_run` | 20–40 | Low (direct corollary) |
| Plumbing per-run body IH in fallback paths | 100–200 per path | Medium (mechanical but verbose) |
| PC-based `agreeOnClean` transport (Approach B) | 100–200 | Medium–High (new typechecker lemma) |
| Total | ~400–700 | Medium |

## Alternative: Restructure ¬ `internalPoisonClean` to reuse shared body

If the ¬ `internalPoisonClean` branch (line 24544) can be restructured to reuse the shared-body
evidence from the clean path (since `qtypCleanUnder` holds in this branch), only the
runtimeInstantiatesCtx / consistentWithRegime / agreeOnClean for the **joined** context need
new work — and these can come from the shared body IH + join transport (same as clean path).

This would reduce the problem to:
1. ¬ `internalPoisonClean` branch: restructure to use shared-body evidence → close by
   `dirty_internal_arrow` for `resultAgreesIfClean`, rest from shared body IH.
2. ¬ `qtypCleanUnder` fallback: `StepFR_single_run` per-run + Approach B for cross-run
   `agreeOnClean` + `resultAgreesIfClean` already proved vacuously.
3. Parrow: mirror.
