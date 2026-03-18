# Mode-3 Proof Lessons: What We Learned

This document summarizes all lessons from the `issue-128-rebase-invariant` branch
(106 commits, ~10,700 lines added) attempting to prove the mode-3 `if` case of the
fault-robustness theorem. The work is being abandoned; this document captures
everything needed for a fresh attempt starting from `main`.

---

## 1. The Core Problem

### 1.1. What mode-3 does

Mode-3 is the `R(k) = none` case of `typecheckIf` (Typecheck.lean:~1653).
When `matchGuard e1` succeeds with `(k, deps)` but the outer regime has no
entry for `k`, the typechecker:

1. Types e1 under `pureCtx := true` (condition is pure)
2. Types the true branch e2 under `tagEnv[k] := (true, deps)` and
   `regime.map[k] := true`
3. Types the false branch e3 under `tagEnv[k] := (false, deps)` and
   `regime.map[k] := false`
4. Joins results conservatively: `joinMemEnvsStrong`, `joinTagEnvs`,
   `joinRegimes`, `joinETyps`, poison = `join pc (join p1 (join p2 p3))`,
   predicate = `noPred`

The regime inserts **do NOT bump `regime.bound`**, so `Regime.lookup? k`
(Typecheck.lean:154) returns `none` when `k ≥ regime.bound`:

```lean
def lookup? (R : Regime) (k : Tag) : Option Bool :=
  if k < R.bound then R.map.get? k else none
```

This means the regime insert is only visible when `k < regime.bound`.

### 1.2. Why the existing proof breaks

The mode-3 sorry is **not just missing work** — the theorem is false under the
current invariant. The counterexample:

```text
if (x == x) then y else 0
```

with:
- `x` clean, `y` dirty
- both carrying `guardClosure k "a" (a == a) []` (same tag `k`)
- outer regime: `R.lookup? k = none`

`matchGuard` succeeds on `x == x`, mode-3 types the true branch under
`R[k |-> true]`, reading `y` becomes clean because `y` shares tag `k`.
But at runtime `y` can differ between two runs, violating `resultAgreesIfClean`.

The invariant gap: mode-3 de-poisons **by tag**, not by matched owner.
`typecheckVar` (Typecheck.lean:729) treats `guardOnly k` and
`guardClosure k d` in the same match arm — both de-poison when
`tagEnv[k] = (true, _)`. So the typechecker implicitly needs a **transfer
principle**: if `matchGuard` proves the predicate for one owner with tag `k`,
then **every** other carrier cleaned by tag `k` is semantically compatible.

No such transfer principle exists in `main`.

### 1.3. The two sorrys in main

**StepFRIte.lean:3502** — single-run variant (`stepFRSingleRun_ite_mode3_maskedReg`)
  proving `StepFRSingleRunFinalCleanPcTrueMaskedRegParam` with masked regime.

**StepFRIte.lean:3560** — two-run variant (`stepFR_ite_mode3`)
  proving `StepFR` (the full two-run fault-robustness comparison).

Both sorrys are at the end of the lemma, after:
- Inverting ite evaluation via `terminatesTo_ite_inv'` for both runs
- Applying the IH to e1 (getting post-e1 realization maps, agreement, etc.)

What remains: handle the four combinations of branch selection
(`b₀ ∈ {true,false}`, `b₁ ∈ {true,false}`) and prove agreement on the
joined output.

---

## 2. Root Causes (Why This Is Hard)

### 2.1. Missing runtime coherence invariant

The fundamental obstacle is that `consistentWithRegime` (RegimeConsistency.lean:982)
only constrains carriers whose guard tag is **already interpreted** by the regime:

```lean
∀ l qt k, ctx.memEnv.lookup l = some qt →
   qtypGuardTag qt = some k →
   R.lookup? k ≠ none →          -- ONLY fires when regime has entry
   locsRegime predSat R μ θ (l, qt)
```

In mode-3, `R.lookup? k = none`, so `consistentWithRegime` says **nothing**
about carriers tagged with `k`. The proof needs a new invariant that constrains
these carriers.

The required invariant is **runtime coherence**: all carriers sharing the same
guard descriptor `(k, d)` must denote the same runtime value. This requires:

1. **Typechecker-side functionality**: tag `k` determines at most one descriptor
   `d`. This is already latent in `wfTagMeaningCtx` via
   `GuardDescInEnvsDeep` + `Relator.RightUnique`.

2. **Runtime-side coherence**: a canonical witness function
   `canon : Tag → GuardDesc → Value` such that every carrier with descriptor
   `(k, d)` has value `canon k d`.

3. **Cross-run sharing**: both runs must use the **same** canonical witness
   (see §2.2).

### 2.2. Per-run coherence is insufficient — shared canonical witness needed

This was discovered late (commit `8b76796`, March 16) and caused a major
architecture revision.

**The problem**: independent per-run existentials
(`∃ canon₀, ...` and `∃ canon₁, ...`) allow `canon₀ k d ≠ canon₁ k d`.
Even though both runs satisfy coherence internally, the transfer principle
needs values to agree **across** runs.

**Counterexample**: `x`, `y` both carry `guardClosure k d` (dirty, not
constrained by `agreeOnClean` since `R.lookup? k = none`). Expression:
`if (x == x) then y else 0`. Both runs take true branch. Per-run coherence
gives `y₀ = x₀` and `y₁ = x₁`. Result is typed clean. But `y₀ ≠ y₁` when
`x₀ ≠ x₁`.

**Fix**: `StepFRGuardCoherent` must use a **shared** canonical witness:

```lean
∃ canon,
  guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀ ∧
  guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁
```

This means `canon k d` is the same value in both runs, so all tag-`k`
carriers automatically agree across runs.

### 2.3. The `guardOnly` soundness gap

`guardOnly k` carriers are an independent gap:

1. `typecheckVar` treats `guardOnly k` and `guardClosure k d` identically —
   both de-poison when `tagEnv[k] = (true, _)`
2. `joinPredicates` creates `guardOnly k` from different
   `guardClosure k d1` and `guardClosure k d2`
3. `locsRegime.guardOnly_ok` and `varsRegime.guardOnly_ok` impose **zero
   semantic constraint** — no predicate-holds, no regime alignment, nothing
4. But `qtypCleanUnder R qt` considers `guardOnly k` clean when
   `R.lookup? k = some true`

So the mode-3 counterexample survives with `guardOnly k` carriers.

**`guardOnly` is NOT merely a join artifact.** It also models the deliberate
pattern where a function returns `guardClosure k d` and links an associated
memory location to the same tag via `guardOnly k`. Removing de-poisoning for
`guardOnly` would break this pattern. **Do not try to fix this by disabling
`guardOnly` de-poisoning.**

**Fix**: extend `guardClosureCoherentWith` to cover `guardOnly` carriers:
for each `guardOnly k` entry, assert `∃ d, tm.lookup k = some d ∧ canon k d = v`.

### 2.4. The `Regime.bound` / visibility interaction

Mode-3 inserts `k` into `regime.map` but does NOT bump `regime.bound`.
Whether the insert is visible via `Regime.lookup?` depends on whether
`k < regime.bound`:

- **`k < bound`**: insert visible, `Regime.lookup? k = some true/false`.
  `consistentWithRegime` fires at `k`. The proof must construct
  `locsRegime.withPred_ok` / `varsRegime.withPred_ok` using the transfer
  principle.

- **`k ≥ bound`**: insert invisible, `Regime.lookup? k = none` still.
  `consistentWithRegime` is vacuous at `k`. Nothing to prove for regime
  consistency, but `tagEnvConsistentWithRegime` breaks because
  `tagEnv[k] = true` but `regime.lookup? k = none`.

This case split is unavoidable and is the structural skeleton of the mode-3
proof.

### 2.5. `tagEnvConsistentWithRegime` breaks for `k ≥ bound`

`tagEnvConsistentWithRegime` (StepFR.lean:49) requires:

```lean
∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

When `k ≥ bound`, the true branch context has `tagEnv[k] = (true, deps)` but
`regime.lookup? k = none`. Neither `StepFR_IH` nor any guard-coherent IH can
be applied to the branch context, because all require `regimeConsistentWithCtx`.

**Fix**: use **masking** — exempt tag `k` from the regime check. Define
`masked' = fun t => masked t ∨ t = k` and use a masked version of
`regimeConsistentWithCtx` that skips masked tags.

### 2.6. Deep closure member-matching problem

When `k < bound`, inserting `k` into the regime makes
`capturedVarsRegimeProperty` fire at tag `k` for deep captured variables
inside closures. Constructing `varsRegime.withPred_ok` at the deep level
needs `canon k d = v` (the canonical value for the captured binding).

The evidence lives in **two separate** `deepValueQTypProperty` chains:
- Regime chain (via `closureCapturedVarsRegime`)
- Coherence chain (via `guardClosureCoherentWith`)

After `joinETyps`, `tcls` can contain multiple `FnTClosure.regular` entries
for the same `(x_param, body)` with different `σcap`, so the two chains may
pick different `σcap` values. This is the **member-matching problem** — you
cannot combine evidence from two independent deep properties post-hoc.

**Fix**: use a **single combined deep property** carrying both regime and
coherence evidence at the same `σcap`. See §4.2 for details.

---

## 3. Dead Ends and Rejected Approaches

### 3.1. `predTagsBoundedInCtx` — FALSE theorem

**What**: Proposed threaded invariant asserting all top-level guard tags in
the context are below `regime.bound`. Would let us derive `k < bound` from
`matchGuard` success, avoiding the `k ≥ bound` case.

**Why it's false**: Closure application (`applyFnTClosure`) exposes captured
environments as the body context's `varEnv`. `typecheckNewRef` can copy a
guard tag from a captured env into the output `memEnv`. The guard tag can be
arbitrarily large (from deep captures) while `regime.bound` stays at 0.

**Verified counterexample**:
- `regime.bound = 0`, `varEnv = { "f" ↦ funQT }` where captured env contains
  `"y" ↦ ⟨int, false, guardOnly 5⟩`
- Expression: `app (var "f") (num 0)` then `newRef`
- Output: fresh cell with `qtypGuardTag = some 5` but `regime.bound = 0`

**Lesson**: Deep captures can escape the shallow bound. Any invariant about
tag values being bounded must either (a) recurse through closures (expensive)
or (b) be avoided entirely.

### 3.2. Bumping `regime.bound` in mode-3 — rejected

**What**: Change mode-3 to set `bound := max(bound, k+1)`.

**Why rejected**: Breaks `Regime.monotoneStep` (Typecheck.lean:189), a true
structural invariant with 326+ uses across proof files. `monotoneStep`
asserts `R'.bound = R.bound`. Changing this cascades through all proofs that
depend on bound equality.

**Lesson**: `Regime.monotoneStep` is deeply wired into the proof
infrastructure. Any approach that changes `regime.bound` will face massive
cascading breakage.

### 3.3. Standalone projection (canonical → old single-run) — rejected

**What**: Replace the old `singleIH` in
`TypeSystemEnforcesFaultRobustness_step_IOFree` with a call to the canonical
single-run theorem, projecting the output.

**Why rejected**: Blocked on the INPUT side. The canonical single-run requires
`StepFRCtxConsGuardCanonical` as input (includes `guardClosureCoherentWith`,
`guardTaggedMemRealized`, combined deep property). The two-run step theorem's
IH (`StepFR_IH`) does not carry these. Cannot construct canonical inputs
from weak premises.

**Lesson**: You cannot derive strong invariants from weak premises at the
call site. The strong invariants must be carried through the IH.

### 3.4. Combined dispatcher with universal `singleIH` — rejected

**What**: Inside the combined dispatcher, construct `singleIH` by calling the
canonical single-run and projecting.

**Why rejected**: `singleIH : StepFRSingleRunFinalCleanPcTrue_IH` is
universally quantified over ALL runtime states (`∀ μ ρ θ, ...`). The
canonical single-run needs canonical witness inputs for each SPECIFIC state.
You can't build a universally-quantified function from specific-state evidence.

**Lesson**: The consumers (`stepFR_ite_mode4`, `stepFR_app`) call `singleIH`
at specific states — they don't need the full universality. The fix is to
upgrade the `singleIH` parameter TYPE to require strong inputs (§4.3).

### 3.5. Per-owner de-poisoning (Alternative C) — rejected

**What**: Change mode-3 to only de-poison the matched owner, not all carriers
with the same tag.

**Why rejected**: Significant precision loss. The guard-tag mechanism's entire
purpose is per-tag de-poisoning. Making it per-owner eliminates the utility
of sharing tags.

### 3.6. Strengthening `locsRegime.guardOnly_ok` — rejected

**What**: Require θ-realization and memory-lookup evidence for `guardOnly_ok`,
paralleling `locsRegime.withPred_ok`.

**Why rejected**: `consistentRegimeSpec` (FaultRobustness.lean:390) is an
unconditional `List.Forall` over all memory entries. In the two-run FR proof,
the typechecker types both if-branches but only one executes at runtime. The
joined memEnv may reference cells whose realization depends on which branch
was taken. Requiring θ-realization on all entries conflicts with the two-run
comparison architecture.

**Lesson**: Keep `locsRegime.guardOnly_ok` zero-obligation. Put value
constraints for `guardOnly` in `guardClosureCoherentWith` (a separate
predicate consumed by the transfer principle).

### 3.7. Separate `guardOnlyTagsInTagMeaning` predicate — rejected

**What**: New predicate asserting every `guardOnly k` tag has a backing
`tm.lookup k = some d` entry.

**Why rejected**: Cannot be derived from current premises.
`wfTagMeaningCtx` is entirely vacuous for `guardOnly` (the chain
`wfTagMeaningCtx → EnvRespectsTagMeaning → GuardDescInEnvsDeep → qtypGuardDesc?`
never fires for `guardOnly`). A context can contain `guardOnly k'` with
`tm.lookup k' = none` and still satisfy `wfTagMeaningCtx`.

**Fix**: Fold the `tm.lookup k` requirement directly into
`guardClosureCoherentWith`. The extended coherence predicate asserts
`∃ d, tm.lookup k = some d ∧ canon k d = v` for `guardOnly k` entries.
No separate bridge predicate needed.

### 3.8. Output-side deep property fan-out — deferred

**What**: Adding `ctxCapturedVarsRegimeGuardCanonical` to the OUTPUT of
`StepFRWithGuardInputs`.

**Why problematic**: Mode-4 branch assemblies (4 combinations) each need ~90
lines. Mode-1/mode-2 take `IH : StepFR_IH` (not IHGC), so they cannot
produce it without additional parameter changes.

**Lesson**: Restrict deep property threading to the INPUT side during initial
construction. Output-side should be deferred to the combined dispatcher (Part D).

---

## 4. Required Modifications for a Fresh Attempt

### 4.1. New definitions needed (in RegimeConsistency.lean)

**`GuardClosureCanonical`** — witness type:
```lean
abbrev GuardClosureCanonical := Tag → GuardDesc → Value
```

**`capturedVarsGuardClosureCanonicalProperty`** — deep recursion:
```lean
def capturedVarsGuardClosureCanonicalProperty (canon : GuardClosureCanonical)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ x qt v k d, σcap.lookup x = some qt → ρcap.lookup x = some v →
    qtypGuardDesc? qt = some (k, d) → canon k d = v
```

**`capturedVarsGuardOnlyCanonicalProperty`** — for `guardOnly` at deep level:
```lean
def capturedVarsGuardOnlyCanonicalProperty (canon : GuardClosureCanonical)
    (tm : TagMeaning) (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ x qt v k, σcap.lookup x = some qt → ρcap.lookup x = some v →
    qt.pred = Predicate.guardOnly k →
    ∃ d, tm.lookup k = some d ∧ canon k d = v
```

**`guardClosureCoherentWith`** — extended with `tm` parameter and `guardOnly`:
```lean
def guardClosureCoherentWith (canon : GuardClosureCanonical) (tm : TagMeaning)
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ x qt v, ctx.varEnv.lookup x = some qt → ρ.lookup x = some v →
    (∀ {k d}, qtypGuardDesc? qt = some (k, d) → canon k d = v) ∧
    (∀ {k}, qt.pred = Predicate.guardOnly k →
       ∃ d, tm.lookup k = some d ∧ canon k d = v) ∧
    deepValueQTypProperty
      (fun σcap ρcap =>
        capturedVarsGuardClosureCanonicalProperty canon σcap ρcap ∧
        capturedVarsGuardOnlyCanonicalProperty canon tm σcap ρcap ∧
        capturedVarsTypingProperty θ σcap ρcap) qt v) ∧
  (∀ l qt a n, ctx.memEnv.lookup l = some qt → θ.lookup l = some a →
    μ.lookup a = some n →
    (∀ {k d}, qtypGuardDesc? qt = some (k, d) → canon k d = Value.num n) ∧
    (∀ {k}, qt.pred = Predicate.guardOnly k →
       ∃ d, tm.lookup k = some d ∧ canon k d = Value.num n))
```

**`guardTaggedMemRealized`** — θ entries for all guard-tagged cells (not
just `guardClosure`):
```lean
def guardTaggedMemRealized (ctx : TypeContext) (θ : RealizationMap) : Prop :=
  ∀ l qt k, ctx.memEnv.lookup l = some qt →
    qtypGuardTag qt = some k → ∃ a, θ.lookup l = some a
```

**`MonotoneCanonicalWitness`** — witness monotonicity:
```lean
def MonotoneCanonicalWitness (canon canon' : GuardClosureCanonical) : Prop :=
  ∀ k d v, canon k d = v → canon' k d = v
```

**`guardClosureFunctionalPerTag`** — tag determines descriptor:
```lean
def guardClosureFunctionalPerTag (ctx : TypeContext) : Prop :=
  Relator.RightUnique (GuardDescInEnvsDeep ctx.varEnv ctx.memEnv)
```

This is derivable from `wfTagMeaningCtx tm ctx` (already a StepFR premise).

### 4.2. Combined deep property (avoid member-matching)

**Critical**: regime evidence and coherence evidence must be carried at the
same `σcap` to avoid the member-matching problem.

Define a **combined deep property** as a single conjunct:

```lean
fun σcap ρcap =>
  capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap ∧
  capturedVarsGuardClosureCanonicalProperty canon σcap ρcap ∧
  capturedVarsGuardOnlyCanonicalProperty canon tm σcap ρcap ∧
  capturedVarsTypingProperty θ σcap ρcap
```

This must be a **conjunct of the canonical single-run bundle**, not a
separate parameter. Reason: the masked-false wrapper
(`StepFR.lean:~2913`) needs to provide combined evidence as input, which
requires construction from separate evidence — hitting the σcap problem.
As a bundle conjunct, it's passed through structurally.

**Impact**: ~80 bundle references + ~26 theorem signatures across ~13 files.
Most per-case proofs: carriers unchanged → inherited via
`deepValueQTypProperty_mono`.

### 4.3. Upgrade singleIH parameter type

The consumers (`stepFR_ite_mode4`, `stepFR_app`) take `singleIH` with weak
type (`consistentWithRegime` input). Change to a guard-coherent type that
also requires `guardClosureCoherentWith` and `guardTaggedMemRealized` as
input. The consumers provide these at each call site from the combined
dispatcher's IH.

### 4.4. Strengthen masking premise (eliminates `predTagsBoundedInCtx`)

Change the canonical single-run masking premise from:

```lean
(∀ k, masked k → ctx.regime.lookup? k = none)
```

to:

```lean
(∀ k, masked k → k ≥ ctx.regime.bound)
```

This is strictly stronger (implies the old premise). Benefits:
- Trivially true at top level (`masked = fun _ => False`)
- Automatically preserved (`R'.bound = R.bound` via `monotoneStep`)
- Eliminates `predTagsBoundedInCtx` entirely

With this, mode-3 keeps the **same mask** and case-splits on `k < bound`:
- `k < bound`: regime insert visible, construct `locsRegime.withPred_ok`
  via transfer principle
- `k ≥ bound`: regime insert invisible, extend mask to
  `masked' = fun t => masked t ∨ t = k`

### 4.5. `StepFRGuardCoherent` combined dispatcher

A new combined theorem type that proves `StepFR` AND carries guard coherence.
Two-run interface with **shared** canonical witness, `MonotoneCanonicalWitness`
in output, and `∀ masked'` IH for mode-3 mask flexibility.

Input additions to `StepFR`:
- Shared canonical witness: `∀ canon, guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀ → guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁ → ...`
- `guardTaggedMemRealized ctx θ₀` and `guardTaggedMemRealized ctx θ₁`
- `ctxCapturedVarsRegimeGuardCanonical` (combined deep property for both runs)

Output additions:
- `∃ canon', MonotoneCanonicalWitness canon canon' ∧ guardClosureCoherentWith canon' tm (ctxAfter ctx res) cf₀.memory cf₀.varEnv θ₀' ∧ guardClosureCoherentWith canon' tm (ctxAfter ctx res) cf₁.memory cf₁.varEnv θ₁' ∧ ...`

### 4.6. Top-level theorem weakening

`FaultRobustnessSpec` gets a new compound premise:

```lean
def InitialGuardClosureCoherence tm ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ :=
  (∃ canon, guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀
          ∧ guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁) ∧
  guardTaggedMemRealized ctx θ₀ ∧
  guardTaggedMemRealized ctx θ₁
```

For fresh initial states (empty heap, no guard-tagged variables): vacuously
true. For specification-conforming states: natural well-formedness condition.

### 4.7. No typechecker changes needed (beyond what's already in main)

The `vlet` shadowing rejection fix is already landed on `main`. No further
typechecker changes are required. The fix is entirely on the proof side.

---

## 5. Proof Strategy for Mode-3

### 5.1. Overall structure

The mode-3 proof decomposes into 4 cases:

```
by_cases hk : k < ctx.regime.bound
├─ k < bound (regime insert VISIBLE via lookup?):
│  ├─ same branch (b₀ = b₁): use IHGC on the branch
│  └─ different branches (b₀ ≠ b₁): use singleIH per-run + transfer principle
│
└─ k ≥ bound (regime insert INVISIBLE):
   ├─ same branch: extend mask, use masked IHGC
   └─ different branches: extend mask, use masked singleIH per-run
```

### 5.2. Transfer principle (k < bound cases)

When the regime insert is visible, the proof must construct
`locsRegime.withPred_ok` for every carrier tagged with `k`. The transfer
argument:

1. `matchGuard_ok_extract_owner_in_ctx` gives the matched owner's descriptor
   `(k, d)` and its location in `ctx.varEnv` or `ctx.memEnv`
2. `guardClosureFunctionalPerTag` (from `wfTagMeaningCtx`) gives uniqueness:
   any other carrier with `guardClosure k d'` has `d' = d`
3. `guardClosureCoherentWith` gives `canon k d = v` for every such carrier
4. `matchGuard_ok_runtime_owner_predSat_iff` gives
   `b_rt = true ↔ predSat k μ v_owner` (the runtime truth value determines
   predicate satisfaction for the matched owner)
5. Since all carriers have `canon k d = v` (same value), the predicate
   result transfers to all of them

For the **negative direction** (false branch, `b_rt = false`):
- `b_rt = false → ¬ predSat k μ v_owner` from the iff
- Coherence gives same value for all carriers → `¬ qtypPredHolds` for all

For **`guardOnly k` carriers**: `locsRegime.guardOnly_ok` (zero evidence) —
no transfer needed. The value constraints live in `guardClosureCoherentWith`.

### 5.3. Mask extension (k ≥ bound cases)

When the regime insert is invisible:

1. Extend mask to `masked' = fun t => masked t ∨ t = k`
2. Verify masking premise: `masked' t → t ≥ bound` (either `masked t → t ≥ bound`,
   or `t = k → k ≥ bound`)
3. `tagEnvConsistentWithRegimeMasked`: tag `k` is masked → ok
4. `consistentWithRegimeMasked`: `R.lookup? k = none` → vacuous at `k`
5. Call `IH_any_mask` with `masked'` on the branch
6. At the join: unmask (drop `k` from mask), analogous to
   `tagEnvConsistentWithRegimeMasked_join_drop` used in the two-run proof

### 5.4. The `regimeConsistentWithCtx` blocker and how to resolve it

When `k ≥ bound`, the branch context has `tagEnv[k] = true` but
`regime.lookup? k = none`. `regimeConsistentWithCtx` (StepFR.lean:58)
requires `tagEnv[k] = true → regime.lookup? k = some true`, which fails.

The IH (both `StepFR_IH` and any guard-coherent IH) requires
`regimeConsistentWithCtx` as a premise. So neither IH can be applied to the
branch context as-is.

Resolution: both the IH and the per-case lemma signatures need masked
variants of `regimeConsistentWithCtx`. The combined dispatcher's strong
induction naturally provides `∀ masked'` quantification.

### 5.5. Output regime and join

The output regime is `joinRegimes res2.regime' res3.regime'`. For the
`ctxAfter ctx res` context:
- `regimeConsistentWithCtx (ctxAfter ctx res)` must be established
- `consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ'` must be proved

The join helpers (`tagEnvConsistentWithRegimeMasked_join_drop`,
`consistentWithRegimeMasked_join`, etc.) are needed here. These exist in the
current branch but may need to be re-derived from `main`.

---

## 6. Practical Gotchas

### 6.1. `Regime.monotoneStep` invariants

`R'.bound = R.bound` is a true structural invariant of ioFree typechecking.
**Never** try to change `regime.bound` in a new typing rule — it cascades
through 326+ uses.

### 6.2. `wfTagMeaningCtx` is vacuous for `guardOnly`

The chain `wfTagMeaningCtx → EnvRespectsTagMeaning → GuardDescInEnvsDeep →
qtypGuardDesc?` never fires for `guardOnly k`. The preservation proof at
StepFR.lean:~9764 actively exploits this vacuity. Do not try to make
`wfTagMeaningCtx` track `guardOnly` — it will break existing proofs.

### 6.3. `FnTClosure` member-matching after `joinETyps`

After `joinETyps`, `tcls` can contain multiple `FnTClosure.regular` entries
for the same `(x_param, body)` with different `σcap`. Two independent
`deepValueQTypProperty` chains may pick different members. You CANNOT combine
two independent deep properties post-hoc — use a single combined deep property
from the start (§4.2).

### 6.4. `locsRegime.withPred_ok` needs θ evidence

Constructing `locsRegime.withPred_ok` requires `θ.lookup l = some a` and
`μ.lookup a = some n`. The existing `runtimeInstantiatesCtx` is one-way
on memory (`θ → memEnv`, not `memEnv → θ`). When `R.lookup? k = none`,
`consistentRegimeSpec` is vacuous, so no θ evidence is available from
existing premises.

Fix: `guardTaggedMemRealized` provides the missing θ entries. This is a
genuinely new obligation.

### 6.5. `consistentRegimeSpec` vs `consistentWithRegime`

`consistentRegimeSpec` (FaultRobustness.lean:390) is the top-level spec
that feeds into `consistentWithRegime` via a bridge lemma. Keep
`consistentRegimeSpec` unchanged — it's an unconditional `List.Forall`
over all entries and should stay permissive (especially for `guardOnly`).

### 6.6. Scale considerations

The branch added ~10,700 lines across 16 files. The mode-3 StepFRIte.lean
alone grew by +7,214 lines. The canonical single-run infrastructure (per-case
proofs for all expression types) is the largest piece.

**Consider whether the canonical single-run needs to be a separate parallel
theorem.** The branch built it as independent infrastructure because of the
failed attempts to integrate into the existing two-run stack. A fresh approach
might try to thread coherence directly into `StepFR` from the start (see §7).

---

## 7. Architectural Alternatives to Consider

### 7.1. Direct `StepFR` strengthening (not attempted cleanly)

Instead of building a parallel canonical single-run theorem, strengthen
`StepFR` itself to carry `guardClosureCoherentWith` in both its input
and output. This avoids:
- Duplicating per-case proofs
- The standalone projection problem (§3.3)
- The universal `singleIH` problem (§3.4)

**Risk**: Every per-case proof must be modified to thread coherence. But
for most cases (literal, var, op, seq, fn, pfn), carriers are unchanged →
coherence is trivially preserved. Only `assign`, `app`, `ite`, `vlet` need
real work.

**Advantage**: eliminates the need for a separate canonical single-run
theorem entirely. The combined dispatcher IS `StepFR` with added outputs.

### 7.2. Masking from the start

The `main` branch already has `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`
(a masked single-run). Consider making **all** of `StepFR` masked from the
start (with `masked = fun _ => False` at top level). This eliminates the
need to maintain separate masked and unmasked variants.

### 7.3. Incremental approach: prove k < bound first

The `k < bound` case requires the transfer principle but not masking.
The `k ≥ bound` case requires masking but the transfer principle is
vacuous. Prove them independently, starting with the conceptually
harder `k < bound` case.

### 7.4. Consider whether mode-3 typing rule can be simplified

While Alternative C (per-owner de-poisoning) was rejected for precision
loss, a middle ground might exist: mode-3 could assert `k < regime.bound`
as a precondition (fail otherwise). This would eliminate the `k ≥ bound`
case entirely. The cost: `matchGuard` may succeed for tags that mode-3
cannot handle (those with `k ≥ bound`), causing those cases to fall through
to mode-4 (standard if). Worth evaluating the precision impact.

---

## 8. Key Lemma References (in main branch)

These are the existing lemmas/definitions that any new attempt will need:

| Lemma/Definition | File:Line | Purpose |
|---|---|---|
| `StepFR` | StepFR.lean:980 | Two-run FR step theorem type |
| `StepFR_IH` | StepFR.lean:~1045 | Inductive hypothesis for StepFR |
| `consistentWithRegime` | RegimeConsistency.lean:982 | Regime consistency predicate |
| `locsRegime` constructors | RegimeConsistency.lean:844 | Per-entry regime evidence |
| `varsRegime` constructors | RegimeConsistency.lean:867 | Per-entry regime evidence (vars) |
| `qtypGuardTag` | RegimeConsistency.lean:~30 | Extract tag from any guard predicate |
| `qtypGuardDesc?` | RegimeConsistency.lean:37 | Extract (tag, desc) from guardClosure |
| `closureCapturedVarsRegime` | RegimeConsistency.lean:~950 | Deep regime property for closures |
| `deepValueQTypProperty` | RegimeConsistency.lean:~900 | Generic deep recursion through closures |
| `deepValueQTypProperty_mono` | RegimeConsistency.lean:~935 | Monotonicity under P strengthening |
| `capturedVarsRegimeProperty` | RegimeConsistency.lean:~940 | Property at each closure level |
| `capturedVarsTypingProperty` | RegimeConsistency.lean:~960 | Typing evidence at each closure level |
| `wfTagMeaningCtx` | RegimeConsistency.lean:~370 | Tag meaning well-formedness |
| `GuardDescInEnvsDeep` | RegimeConsistency.lean:~350 | Deep guard descriptor extraction |
| `tagEnvConsistentWithRegime` | StepFR.lean:49 | tagEnv/regime agreement |
| `regimeConsistentWithCtx` | StepFR.lean:58 | Full context/regime consistency |
| `Regime.lookup?` | Typecheck.lean:154 | Bounded regime lookup |
| `Regime.monotoneStep` | Typecheck.lean:189 | Regime monotonicity invariant |
| `matchGuard` | Typecheck.lean:~620 | Guard condition matcher |
| `terminatesTo_ite_inv'` | SemanticsProperties.lean | Ite evaluation inversion |
| `joinMemEnvsStrong` | Typecheck.lean | Strong memory join |
| `joinRegimes` | Typecheck.lean:~175 | Conservative regime join |

---

## 9. Summary of Required Changes (Minimal)

For a fresh attempt, the minimum changes from `main` are:

1. **New definitions** (RegimeConsistency.lean): `GuardClosureCanonical`,
   `guardClosureCoherentWith`, `capturedVarsGuardClosureCanonicalProperty`,
   `capturedVarsGuardOnlyCanonicalProperty`, `guardTaggedMemRealized`,
   `MonotoneCanonicalWitness`, `guardClosureFunctionalPerTag`

2. **Strengthen `StepFR`** with shared canonical witness, combined deep
   property, and `guardTaggedMemRealized` (input + output)

3. **Upgrade `singleIH` type** in `stepFR_ite` and `stepFR_app` signatures

4. **Strengthen masking premise** to `k ≥ bound` (if using masking approach)

5. **New top-level premise** in `FaultRobustnessSpec` for initial coherence

6. **Mode-3 proof body**: 4-case skeleton with transfer principle (k < bound)
   and mask extension (k ≥ bound)

**No typechecker changes.** No changes to `locsRegime`, `varsRegime`, or
`consistentRegimeSpec`. No changes to `Regime.monotoneStep` or
`regime.bound`.
