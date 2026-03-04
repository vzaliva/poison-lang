# Body StepFR IH Evidence Blocker

Analysis of the main remaining blocker for `stepFR_app` completion.

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

**Singleton rules** (`app_fn_singleton`, `app_fn_singleton_arrow`, `app_fn_singleton_parrow`):
When `tcls` has one element `(x, e, S1)`, the typechecker evaluates the body `e` once and uses
the result directly.

**Multi-closure rules** (`app_fn_cons_arrow`, `app_fn_cons`, `app_fn_cons_ref`):
When `tcls = (x, e, S1), tcls'`, the typechecker:
1. Evaluates the head closure's body → result `T' :> p' {P'} -| G' ; L' ; R'`
2. Recursively handles the tail → result `T'' :> p'' {P''} -| G'' ; L'' ; R''`
3. **Joins** the post-call contexts: `JoinGStrong G' G''`, `JoinL L' L''`, `JoinR R' R''`
4. Joins the result types (poison, predicate, etyp) conservatively

The join is conservative: `JoinGStrong` (memory) drops single-sided predicates, `JoinL`
(tags) keeps only entries that agree in both, `JoinR` (regime) keeps only entries that agree.

### The three cases in the FR proof

The `stepFR_app` proof cases on cleanliness of the function result:

| Case | `p1` | `internalPoisonClean` | Both runs pick same closure? |
|------|------|-----------------------|-----------------------------|
| Clean | false | true | Yes — clean values agree across runs |
| Dirty internal | false | false | Yes — p1 still clean, values agree |
| Dirty outer | true | n/a | **No** — poisoned values need not agree |

**Clean path** (done): Both runs share the same closure.  StepFR IH applies to `(body, body)`
with `(cf₀, cf₁)` directly.  Corresponds to `clean_internal_arrow` / `clean_internal_parrow`
constructors of `agreeValueUnder`.

**Dirty internal** (¬ `internalPoisonClean`): Both runs still share the same closure (p1 is
clean).  Shared body IH gives all context invariants.  Only `resultAgreesIfClean` differs:
uses `dirty_internal_arrow` constructor (needs only `valueHasETyp`, not full deep agreement).

**Dirty outer** (¬ `qtypCleanUnder`, i.e., `p1 = true`): Runs may pick different closures.
The result is unconditionally poisoned (Ott: result poison includes `join p1 ...`; when
`p1 = true`, everything is tainted).  `resultAgreesIfClean` is vacuously true.  But the
**post-call context invariants** still need evidence from body evaluation.

## 2. Problem Statement

The `StepFR` proof obligation requires **two runs evaluating the SAME expression**.  The IH
from the fuel induction gives `StepFR` for sub-expressions at smaller fuel.

In the **clean** and **dirty internal** paths, both runs share the same body — StepFR IH
applies directly.

In the **dirty outer** path (`p1 = true`), the two runs may pick **different** closure
alternatives.  Since StepFR IH requires both runs to evaluate the same expression, it cannot
be applied when the body expressions differ.

## 3. Affected Obligations

### Arrow ¬ `internalPoisonClean` fallback (line ~24544)

One sorry wrapping a 10-element pack.  `qtypCleanUnder` holds (p1 = false), so the shared-body
sync logic from the clean path applies.  The `dirty_internal_arrow` constructor of
`agreeValueUnder` only needs `valueHasETyp` for both runs.

Most of the pack should reuse the shared body IH from the clean path; only
`resultAgreesIfClean` differs (uses `dirty_internal_arrow` instead of `clean_internal_arrow`).

### Arrow ¬ `qtypCleanUnder` fallback (lines ~24578–24586)

9 sorrys.  Available facts: `p1 = true`, `res.poison = true`, `res.pred = noPred`.

| # | Obligation | Notes |
|---|-----------|-------|
| 1-2 | `valueHasETyp θ₀1 o₀ / θ₁1 o₁` | Per-run; needs body evaluation evidence |
| 3-4 | `runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀ / cf₁` | Per-run; body evaluation evidence |
| 5-6 | `consistentWithRegime … cf₀ / cf₁` | Per-run; deep closure invariant |
| 7 | `agreeOnClean` | Cross-run; needs special handling |
| 8-9 | `valueConsistentWithRegime … cf₀ o₀ / cf₁ o₁` | Per-run; deep closure invariant |

`resultAgreesIfClean` already proved vacuously via `resultAgreesIfClean_of_poison_noPred`.

### Parrow refine block (lines ~25216–25249) + body IH paths (lines ~25317, 25319)

Same structure as arrow.  9 sorrys in refine block + 2 at clean/dirty split.

## 4. Key Insight: Membership-Based Transport

The `joinTypeResults_transport_*_from_member` lemmas are **membership-based**, not
position-based:

```
joinTypeResults_transport_valueHasETyp_from_member:
  src ∈ results → valueHasETyp θ v src.qualType.etyp → valueHasETyp θ' v res.qualType.etyp

joinTypeResults_transport_consistentWithRegime_from_member:
  src ∈ results → consistentWithRegime ... src ... → consistentWithRegime ... res ...
```

They say: **if a property holds for ANY member's result, it holds for the joined result**.
No ordering or commutativity assumptions needed.

This means:
- Run₀ picks closure_i → evaluates body_i → gets per-member evidence for member_i's TypeResult
- Run₁ picks closure_j → evaluates body_j → gets per-member evidence for member_j's TypeResult
- Transport run₀'s evidence: member_i ∈ results → joined result inherits the property
- Transport run₁'s evidence: member_j ∈ results → joined result inherits the property

Both runs arrive at the **same** joined type context, each transporting from their own member.
The join does not need to be order-independent; we only need the member ∈ results witness.

## 5. Why The Result Is Trivial (p1 = true)

When `p1 = true`, the Ott rules give result poison `join pc (join p1 ...) = true` and the
`AppPred` gate kills the predicate to `noPred`.  So `resultAgreesIfClean` is vacuously true
(a poisoned result with no predicate is never "clean under" any regime).

This is already proved: `resultAgreesIfClean_of_poison_noPred`.

**We do not need to reason about closure alternatives for the result value at all.**

## 6. Why The Post-Call Context Is Not Trivial

Although the result is trivially handled, the post-call **type context** (`ctxAfter ctxᵢ res`)
still matters.  It describes:
- Memory types (`memEnv'`) — which locations exist and their types
- Tag environment (`tagEnv'`) — which regime tags are alive
- Regime (`regime'`) — which entries are clean vs dirty

The FR proof must show the post-call runtime state is consistent with this context.  This
requires evidence from body evaluation (the body has side effects: allocates memory, modifies
references).

## 7. Recommended Approach: Single-Run Corollary + Membership Transport

### Step 1: `StepFR_single_run` (~20–40 lines)

Corollary of `StepFR` via self-agreement.  (Previously introduced in dba4db3, removed in
ec05def during refactor cleanup — not a soundness rejection.  The rejected pattern was using
StepFR to prove *static* typechecker facts for non-executed closures, which lacks
`terminatesTo` witnesses; see `app-proof-history.md`.  Here we use it **only for executed
closure bodies** where `terminatesTo` is available from app inversion.)

Use the **existing** `agreeOnClean_same_config` (FaultRobustnessProofs.lean:870) which
provides self-agreement with the correct premises (`runtimeInstantiatesCtx` +
`consistentWithRegime`):

```lean
private lemma agreeOnClean_same_config
  (predSat : PredSat) (R : Regime) (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (hcwr : consistentWithRegime predSat R ctx μ ρ θ)
  (_hR : R = ctx.regime) :
  agreeOnClean predSat R ctx μ ρ θ μ ρ θ
```

`agreeOnClean` requires runtime lookups for typed variables and realized locations, so
`runtimeInstantiatesCtx` is essential — `consistentWithRegime` alone is insufficient.

`StepFR_single_run` instantiates `StepFR` with `μ₀ = μ₁ = μ`, `θ₀ = θ₁ = θ`,
`cf₀ = cf₁ = cf`, `o₀ = o₁ = o`, feeding `agreeOnClean_same_config` for the
self-agreement precondition:

```lean
lemma StepFR_single_run
  (hStepFR : StepFR mode ctx e res predSat tm)
  (hPSL : PredSatLaws predSat tm)
  (hTm : wfTagMeaningCtx tm ctx)
  (hwfθ : wfRealizationMap θ) (hwfCtx : wfTypeContext ctx)
  (hric : runtimeInstantiatesCtx ctx μ ρ θ)
  (htagR : regimeConsistentWithCtx ctx) (hRbound : regimeBounded ctx.regime)
  (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
  (hwfCf : wfConfig cf) (hpm : cf.pureMode = pm)
  (hcfMem : cf.memory = μ) (hcfVar : cf.varEnv = ρ)
  (hterm : terminatesTo mode e cf cf' o) :
  ∃ θ', wfExtendsMap θ θ' ∧
    valueHasETyp θ' o res.qualType.etyp ∧
    runtimeInstantiatesCtx (ctxAfter ctx res) cf'.memory cf'.varEnv θ' ∧
    consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
      cf'.memory cf'.varEnv θ' ∧
    valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf'.memory θ' o ∧
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧ wfTypeContext (ctxAfter ctx res) ∧
    regimeConsistentWithCtx (ctxAfter ctx res) ∧ wfConfig cf'
```

### Step 2: Per-run body evidence via member chain

For each run independently, the member-evidence chain is:

1. **Runtime → FnTClosure membership**: `valueHasETyp.closure` gives
   `htcl : FnTClosure.regular x body tenv ∈ tcls` (the runtime closure belongs to the
   type-level closure list).

2. **FnTClosure membership → body typing**: `applyFnTClosure_regular_inv_of_mapM_mem`
   (FaultRobustnessProofs.lean:16597) takes `htcl` + `hmap` (the mapM success) and extracts:
   - `first_i : TypeResult` (the applyFnTClosure result for this specific closure)
   - `result3_i : TypeResult` (the body's typechecking result)
   - Body typecheck success: `typecheckExpr .ioFree bodyCtx_i body fuelBody = .ok result3_i`
   - The relationship `first_i = { result3_i with qualType := ... }` (memEnv/tagEnv/regime
     are shared between first_i and result3_i)

3. **Body typing → StepFR_single_run prerequisites**: Construct `bodyCtx_i` (body context
   with captured env + argument), establish `runtimeInstantiatesCtx bodyCtx_i ...`,
   `consistentWithRegime ... bodyCtx_i ...`, etc.  (Same construction as the clean path,
   lines 24524–24540.)

4. **Apply `StepFR_single_run`**: Get post-body evidence for this specific member:
   `θ_body`, `valueHasETyp θ_body o res3.qualType.etyp`,
   `runtimeInstantiatesCtx (ctxAfter bodyCtx_i result3_i) ...`,
   `consistentWithRegime ...`, etc.

5. **FnTClosure membership → TypeResult membership**: The mapM processes each FnTClosure
   in `tcls` to produce a TypeResult in `first :: rest`.  The direction needed here is
   input→output: given `htcl : FnTClosure.regular x body tenv ∈ tcls`, obtain
   `first_i ∈ first :: rest`.  Use `applyFnTClosure_ok_of_mem_mapM` /
   `list_mapM_ok_mem_input_exists_output` for this direction.
   (Note: `list_mapM_ok_mem_output_exists_input` goes the other direction — output→input —
   and is used elsewhere in the proof at line 24556.)

### Step 3: Transport per-run evidence to joined result

For each per-run obligation, transport from the member's TypeResult to the joined result:

| Obligation | Transport lemma | Notes |
|-----------|----------------|-------|
| `valueHasETyp` | `joinTypeResults_transport_valueHasETyp_from_member` | Member-generic; takes `src ∈ first :: rest` |
| `consistentWithRegime` | `joinTypeResults_transport_consistentWithRegime_from_member` | Member-generic |
| `valueConsistentWithRegime` | `joinTypeResults_transport_valueConsistentWithRegime_from_member` | Member-generic |
| `runtimeInstantiatesCtx` | Composite (see below) | Needs special handling |
| `wfConfig` | Direct from body IH | No transport needed |

**`runtimeInstantiatesCtx` transport** requires special handling because
`join_transport_runtimeInstantiatesCtx` (FaultRobustnessProofs.lean:16209) is
**left-biased** (takes first member's evidence).  However, the proof strategy is the same as
the clean path (lines 24274–24284), and is member-generic:

1. Get `runtimeInstantiatesCtx (ctxAfter bodyCtx_i result3_i) cf.memory (env.update x v) θ_body`
   from the body IH.
2. Since `first_i.memEnv' = result3_i.memEnv'` (from `applyFnTClosure_regular_inv`),
   and `ctxAfter ctxᵢ first_i` differs from `ctxAfter bodyCtx_i result3_i` only in `varEnv`,
   the memEnv part of runtimeInstantiatesCtx transfers directly.
3. Use `joinTypeResults_mem_contains_of_member` (FaultRobustnessProofs.lean:22516) to get
   `∀ l, first_i.memEnv'.contains l → res.memEnv'.contains l`.
4. **MemEnv conjunct**: for `(l,a) ∈ θ_body`, `l ∈ first_i.memEnv'` (from body IH) →
   `l ∈ res.memEnv'` (from containment).  Memory lookup `μ.lookup a` passes through.
5. **VarEnv conjunct**: `ctxAfter ctxᵢ res` has `varEnv = ctxᵢ.varEnv` (unchanged by
   `ctxAfter`).  Pre-call `runtimeInstantiatesCtx ctxᵢ ...` gives values for all vars in
   `ctxᵢ.varEnv`.  Values in the caller's VarEnv are unchanged by the body.
   `valueHasETyp` must hold under `θ_body` (which extends `θ`); this follows from
   `valueHasETyp_extends` monotonicity (on `extendsMap`).

### Step 4: Cross-run `agreeOnClean`

#### Case: ¬ `internalPoisonClean` (p1 = false)

Both runs share the same closure (p1 is clean, so values agree).  The shared body StepFR IH
gives cross-run `agreeOnClean` directly, same as the clean path.  Then transport via
`join_transport_agreeOnClean_from_member` (FaultRobustnessProofs.lean:18397).

#### Case: ¬ `qtypCleanUnder` (p1 = true) — the concentrated blocker

The two runs execute different closure bodies, so no shared body IH exists for cross-run
agreement.  This is the **make-or-break piece** of the entire approach.

We use `join_transport_agreeOnClean_from_member`, whose key premise is:

```lean
h_mem_from_src_or_unrealized :
  ∀ l qt,
    (ctxAfter ctx res).memEnv.lookup l = some qt →
    qtypCleanUnder (ctxAfter ctx res).regime qt →
    ((∃ qt_src, (ctxAfter ctx src).memEnv.lookup l = some qt_src ∧
                qtypCleanUnder (ctxAfter ctx src).regime qt_src ∧
                qt.etyp = qt_src.etyp ∧
                (qt.poison = false → qt_src.poison = false))
    ∨ (θ₀.lookup l = none ∧ θ₁.lookup l = none))
```

This says: for each guard-clean location in the joined result, either (a) it traces back to a
guard-clean entry in the source member, or (b) it is unrealized in both θs.

**Why the naive "no new clean entries" claim is too strong:**

The `qtypCleanUnder` predicate has a guard constructor (FaultRobustness.lean:403):
```lean
| guard (k : Tag) (htag : qtypGuardTag qt = some k) (hregime : R.lookup? k = some true)
    (hnotfun : qt.etyp.isFunctionType = false) : qtypCleanUnder R qt
```
This is independent of `qt.poison`.  A pre-existing guard tag `k` with `R[k] = true` can make
an entry guard-clean even when `qt.poison = true`, provided the entry is non-function-typed.

Under poisoned PC (`pc_body = joinPoison p (joinPoison true ctx.pc) = true`):
- All memory writes have `storedPoison = joinPoison ctx.pc ... = true`.
- New tags created by mode 3 `ite` under `pc_body = true` get regime value
  `¬pc_body = false`, so they do NOT activate the guard constructor.
- But pre-existing guard tags with `R[k] = true` CAN still activate the guard constructor
  on entries that have `poison = true` but carry the right predicate.

**Precise analysis of which entries can be guard-clean in `ctxAfter ctxᵢ res`:**

Locations in `res.memEnv'` fall into categories relative to each closure alternative:

1. **Single-sided entries** (present in one alternative, absent in another):
   `joinMemEnvsStrong` drops predicates to `noPred` on single-sided entries.
   Since `qtypGuardTag ⟨..., noPred⟩ = none`, the guard constructor fails.
   Combined with `poison = true` (from poisoned PC), the clean constructor also fails.
   → **Not guard-clean. No agreeOnClean obligation.** ✓

2. **Both-sided entries from pre-existing locations** (present in `result1.memEnv'` before
   the body):  Both alternatives start from the same memEnv, so these are both-sided.
   The joined entry has `joinPoison p₁ p₂` and `joinPredicates pred₁ pred₂`.
   Under poisoned PC, both `p₁` and `p₂` are true, so joined poison = true.
   The guard survives only if both alternatives preserve the same guard tag.

   For these, we need the `h_mem_from_src_or_unrealized` disjunction.
   Take `src` = one specific member (say the first, since join transport provides the
   relationship).  The pre-existing location existed in `src.memEnv'` with a guard-clean
   entry (since the starting memEnv was shared and the guard was preserved by both
   alternatives).  The first branch of the disjunction applies:
   `qt_src` exists, is guard-clean, and etyp/poison are compatible.

   Then `h_src` (agreeOnClean for the source member) provides the agreement evidence.
   We must obtain this `h_src` from the per-run body evidence.  Three sub-approaches:

   **(A) Via pre-call agreeOnClean + body-preserves-agreement argument:**
   If the body's only effect on these pre-existing locations is to taint poison
   (not change the stored value's address), then the pre-call agreement on the
   underlying value carries over.  But different bodies may write different values
   to the same location, breaking this.

   **(B) Via StepFR_single_run → self-agreeOnClean + transport:**
   `StepFR_single_run` for run₀'s closure gives `agreeOnClean_same_config` for the
   source member's context (self-agreement: μ₀ ρ₀ θ₀' agrees with μ₀ ρ₀ θ₀').
   But we need CROSS-run agreement (μ₀ vs μ₁), not self-agreement.

   **(C) "Unrealized" escape for new entries:**
   For locations that are NEW in the body result (not in the pre-call memEnv):
   run₀ executed closure_i and θ₀' maps these new locations, but run₁ executed
   closure_j which may not have created the same locations.  If l is new in both
   alternatives (same logical location ID from both bodies), both θ₀' and θ₁'
   map it (both runs allocated it).  If new in only one, it's single-sided (case 1).

3. **Both-sided entries from new locations** (both alternatives happen to allocate the same
   logical location): Both bodies start from the same `nextLoc`, so their first allocation
   gets the same ID.  Under poisoned PC, the stored poison is true.
   The guard depends on the expression being stored — different bodies store different
   expressions, so different guards.  `joinPredicates` of different guards typically
   yields `noPred`.  → **Usually not guard-clean.** But not guaranteed in general.

**Risk assessment**: The single-sided case (case 1) is handled.  Pre-existing guard-clean
entries (case 2) are the main concern.  New both-sided entries (case 3) are rare and
usually not guard-clean.  If investigation shows no guard-clean entries survive the join
when `p1 = true`, then `h_mem_from_src_or_unrealized` is vacuously true and the entire
`agreeOnClean` obligation collapses to trivial.  If they DO survive, a new nontrivial
lemma tying "survives-as-clean-in-join" to "was pre-existing + effectively not modified"
will be needed, requiring real proof-design iteration.

**Required investigation** (to be done first — see §11):
1. Check whether `joinRegimes` (= `joinRegimeMaps`) invalidates guard tags that differ between
   alternatives.  If `R[k] = true` in one alternative and `R[k] = false` in another, the
   joined regime might set `R[k] = false`, killing the guard.
2. Check whether any pre-existing guard-clean location can actually remain guard-clean after
   being modified by the body under poisoned PC, given that the body's assignment may change
   the predicate (via `joinPredicates` in weak updates).
3. If investigation shows that no guard-clean entries survive the join in the poisoned-PC case,
   then `h_mem_from_src_or_unrealized` is vacuously true and the entire `agreeOnClean`
   obligation is trivial — **the best outcome**.

**Fallback (if guard-clean entries DO survive):**
Prove a direct `agreeOnClean_poisonedPC_from_precall` lemma:
```
-- When pc_body = true, locations that are guard-clean in ctxAfter were already
-- guard-clean in the pre-body context, and both runs agree on pre-existing
-- locations because they agree on the pre-call context.
```
This would need: (a) a static lemma relating post-body guard-clean entries to pre-body entries,
and (b) a bridge from pre-call agreeOnClean to post-call agreeOnClean for entries whose
underlying values didn't change across the body execution.  Back to needing cross-run
reasoning about different bodies.

## 8. Preservation Lemmas (Step 4 from plan)

The six preservation lemmas with sorry (`applyFnTClosure_ok_wfTagMeaningCtx`, etc.) are
**not eliminated** by `StepFR_single_run`.  They serve a different purpose.

### What `StepFR_single_run` provides

`StepFR_single_run` gives `wfTagMeaningCtx`, `wfTypeContext`, `regimeConsistentWithCtx` for
the **executed member's** body context.  This is sufficient for:
- Per-run evidence transport (valueHasETyp, consistentWithRegime, etc.)
- Evidence about the specific closure alternative that each run executes

### What still needs the preservation lemmas

The join transport lemmas have these biases:

| Join transport lemma | Needs evidence from |
|---------------------|-------------------|
| `join_transport_wfTagMeaningCtx` | **First member only** (left-biased) |
| `join_transport_wfTypeContext` | First member + `wfTypeResult` for ALL rest members |
| `join_transport_regimeConsistentWithCtx` | **First member only** + structural properties |

These are consumed in the arrow/parrow refine blocks to establish well-formedness of the
joined context.  They are **independent of which closure the runtime executes** — they need
evidence about the typechecker's output for specific members (especially the first).

The `mapM_applyFnTClosure_forall_*` wrapper lemmas (FaultRobustnessProofs.lean:16900+) lift
per-closure evidence to `∀ r ∈ results, P r` and are fully implemented — but they delegate
to the sorry preservation lemmas internally.

### Paths forward

**Important constraint**: `StepFR_single_run` **cannot** be used to discharge preservation
lemmas for non-executed closure alternatives.  It requires a `terminatesTo` witness, which
only exists for the closure the runtime actually executed.  Attempting to use StepFR for
non-executed closures was previously tried (via `StepFR_implies_wfTypeResult`) and explicitly
rejected (deleted in 02e7fcb) as a dead end — see `app-proof-history.md`.

The preservation lemmas must therefore be proved by one of:

1. **Purely static proofs** (typechecker fuel induction, no runtime witnesses):
   The 3 preservation properties (wfTagMeaningCtx, regimeConsistentWithCtx,
   QTypRespectsTagMeaning) may be provable by structural induction on the typechecker's
   processing of each body, following the pattern of `typecheckExpr_preserves_wfTypeResult`
   which succeeded via this route.

2. **Refine-block restructuring** to reduce the all-member burden:
   `join_transport_wfTagMeaningCtx` only needs the first member.  If the executed member
   happens to be the first, `StepFR_single_run` evidence suffices for that property.
   For the general case, at minimum the first-member preservation lemma must be proved
   statically.

**Expected effort**: Moderate.  Not conceptually blocked, but may require static fuel
induction or refine-block restructuring.

## 9. Summary of Cases

| Case | Per-run evidence | Cross-run `agreeOnClean` | `resultAgreesIfClean` |
|------|-----------------|-------------------------|----------------------|
| Clean | Shared body StepFR IH | Shared body StepFR IH | `clean_internal_arrow` |
| Dirty internal | Shared body StepFR IH | Shared body StepFR IH | `dirty_internal_arrow` (valueHasETyp only) |
| Dirty outer | `StepFR_single_run` per-run + member transport | `join_transport_agreeOnClean_from_member` (see §7.4) | Vacuous (`poison=true, pred=noPred`) |

## 10. Effort Estimate

| Step | Lines (est.) | Risk |
|------|-------------|------|
| Poisoned-PC `agreeOnClean` investigation | 0 (analysis only) | **Critical** (determines overall feasibility) |
| Poisoned-PC `agreeOnClean` proof | 0–300 | **High** if guard-clean survives; trivial if vacuous |
| `StepFR_single_run` | 20–40 | Low |
| Restructure ¬ `internalPoisonClean` to reuse shared body | 50–100 | Low |
| Per-run body IH plumbing in ¬ `qtypCleanUnder` | 100–200 per path | Medium (mechanical but verbose) |
| runtimeInstantiatesCtx member transport | 30–50 | Low (follows clean-path pattern) |
| Preservation lemma investigation / resolution | 50–200 | Medium |
| **Total** | **~350–900** | **Medium–High** |

## 11. Implementation Order

Ordered high-risk-first to detect blockers early:

1. **Investigate guard-clean entries under poisoned PC** (§7.4 investigation items 1–3) —
   this is the **critical path**.  Determine whether `qtypCleanUnder` entries survive in
   `ctxAfter ctxᵢ res` when `p1 = true` by checking `joinRegimes` behavior, weak-update
   predicate propagation under `pc_body = true`, and `joinPredicates` of guards across
   alternatives.  If no entries survive: the entire `agreeOnClean` obligation is vacuous
   and overall feasibility is confirmed.  If entries survive: assess whether the fallback
   (`agreeOnClean_poisonedPC_from_precall`) is tractable before proceeding.
2. **`StepFR_single_run`** — uses existing `agreeOnClean_same_config`; unblocks all
   fallback paths
3. **¬ `internalPoisonClean` branch** — restructure to reuse shared body evidence from clean
   path; only `resultAgreesIfClean` differs (use `dirty_internal_arrow`)
4. **Per-run body IH plumbing in ¬ `qtypCleanUnder`** — `StepFR_single_run` per-run +
   member transport for per-run obligations (valueHasETyp, runtimeInstantiatesCtx,
   consistentWithRegime, valueConsistentWithRegime)
5. **Cross-run `agreeOnClean` for ¬ `qtypCleanUnder`** — based on investigation from step 1
6. **Preservation lemmas** — investigate static provability; fill or eliminate
7. **Parrow** — mirror of arrow (same approach, `PFnTClosure` variants)
