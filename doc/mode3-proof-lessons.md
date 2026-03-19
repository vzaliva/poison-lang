# Mode 3: Analysis, Counterexample, and Repair Options

This document consolidates three earlier analyses into a single self-contained
reference for understanding and resolving the mode-3 `if` soundness problem.
It does not assume access to the abandoned `issue-128-rebase-invariant` branch.

**Terminology used throughout:**

- **tag-only** (`guardOnly k`): a guard tag with no attached predicate closure.
  Purely logical; the carrier value does not matter for `matchGuard`.
- **tag+predicate** (`guardClosure k arg body cap`): a guard tag with an
  attached predicate closure.  The carrier value participates in `predSat`.
- **mode 1 / mode 2**: `R.lookup? k = some true` / `some false`.
- **mode 3**: `R.lookup? k = none` (regime-unknown; the focus of this document).
- **mode 4**: `matchGuard` fails entirely; standard `if`.

---

## 1. Background: What Mode 3 Does

Mode 3 is the case of `typecheckIf` (`Typecheck.lean:1648`) where:

- `matchGuard e1 ctx.memEnv ctx.varEnv fuel = .ok (k, deps)` — a guard match
  succeeds
- `ctx.regime.lookup? k = none` — the outer regime has no entry for tag `k`

The typechecker then:

1. Types `e1` under `pureCtx := true` (the condition is pure).
2. Types the true branch `e2` under `tagEnv[k := (true, deps)]` and
   `regime.map[k := true]`.
3. Types the false branch `e3` under `tagEnv[k := (false, deps)]` and
   `regime.map[k := false]`.
4. Joins results conservatively: `joinMemEnvsStrong`, `joinTagEnvs`,
   `joinRegimes`, `joinETyps`, with `poison = join pc (join p1 (join p2 p3))`
   and `pred = noPred`.

Crucially, the regime inserts **do not bump `regime.bound`**:

```lean
def lookup? (R : Regime) (k : Tag) : Option Bool :=
  if k < R.bound then R.map.get? k else none
```

So the insert into `regime.map` is visible through `lookup?` only when
`k < regime.bound`.  This creates a fundamental split between the `k < bound`
(visible) and `k >= bound` (invisible) subcases.

### 1.1. The two sorrys on `main`

- `stepFRSingleRun_ite_mode3_maskedReg` (`StepFRIte.lean:3502`) — single-run
  variant proving `StepFRSingleRunFinalCleanPcTrueMaskedRegParam` with masked
  regime.
- `stepFR_ite_mode3` (`StepFRIte.lean:3560`) — two-run variant proving `StepFR`
  (the full fault-robustness comparison).

Both are after inverting the `ite` evaluation via `terminatesTo_ite_inv'` and
applying the IH to `e1`.  What remains is handling the four combinations of
branch selection (`b₀ ∈ {true, false}`, `b₁ ∈ {true, false}`) and proving
agreement on the joined output.

---

## 2. The Soundness Problem

### 2.1. The theorem is false, not merely unfinished

The remaining mode-3 sorry is **not just missing proof work** — the `StepFR`
statement under the current invariant is false.  A formal counterexample was
proved on the `issue-128-rebase-invariant` branch (not on `main`).

### 2.2. Counterexample construction

The counterexample uses two variables with the same tag:

- `x`: clean, carries `Predicate.guardClosure 0 "a" (a == a) []`
- `y`: dirty (poison = true), carries the same predicate

Expression:

```text
if (x == x) then y else 0
```

Outer regime: `bound = 1`, empty map.  So `R.lookup? 0 = none` — exactly
mode 3.

**Why `matchGuard` matches `x` but not `y`:**  The predicate body `a == a`
is parameterised by argument name `"a"`.  During `matchGuard`, the body is
instantiated at the owner:

- For `x`: instantiated body is `x == x`, which matches the condition.
- For `y`: instantiated body is `y == y`, which does **not** match `x == x`.

So exactly one owner (`x`) matches, and mode 3 is triggered.

**The two runs:**

- Run 0: `x = 0`, `y = 1`
- Run 1: `x = 0`, `y = 2`

Both runs agree on every clean input (`x` is clean and equal; `y` is dirty,
so it may differ).

### 2.3. Why the expression typechecks as clean

The true-branch context uses `R[0 |-> true]`.  Inside that context,
`typecheckVar` reads `y` and finds:

```lean
| Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
    match ctx.tagEnv.get? k with
    | some ⟨true, _deps⟩ =>
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
```

Because `y` carries tag `0` and `tagEnv[0] = (true, deps)`, `y` is de-poisoned
to `⟨int, pc, noPred⟩`.  The else branch returns `0 : int :> clean`.  The
joined result is `int :> clean :> noPred` — classified as clean.

### 2.4. Why the runtime outputs disagree

Both runs evaluate `x == x` to `true` (since `x` is clean and equal across
runs), so both take the true branch, returning `y`.

- Run 0 returns `1`
- Run 1 returns `2`

The outputs differ, but the typechecker classified the result as clean.
`StepFR` would then require `Value.num 1 = Value.num 2`, which is absurd.

### 2.5. The formal contradiction

The formal proof (on the abandoned branch) instantiated the full `StepFR`
premises — well-formed realization maps, runtime instantiation, regime
consistency, agreement on clean inputs, successful evaluation — then used the
`StepFR` conclusion to obtain `resultAgreesIfClean` for `Value.num 1` and
`Value.num 2`.  Since the result type is a clean non-reference non-function
`int`, `agreeValueUnder_nonref_eq_of_clean` forces `Value.num 1 = Value.num 2`,
a contradiction.

### 2.6. Why the final join does not save the rule

One might hope: "the final branch join drops the temporary regime entry for
`k`, so the output regime is conservative again."  That is true but irrelevant.
The unsoundness already happened while typing the true branch — `y` was
de-poisoned under `R[k |-> true]`, and the clean output type survived the join.
Dropping `k` from the joined regime afterward does not retroactively justify the
de-poisoning of `y`.

### 2.7. What the counterexample really shows

The counterexample does not say that every branch-local regime update is wrong.
It says something more specific:

> A successful `matchGuard` on one owner is not enough to activate the same
> tag for every other tag+predicate carrier of that tag.

The unsoundness is about same-tag tag+predicate carriers.  Tag-only carriers
are purely logical and carry no value-dependent `predSat` obligation — they
are not the source of the gap.

---

## 3. Root Cause Analysis

### 3.1. De-poisoning by tag, not by owner

`matchGuard` proves that one specific owner with tag `k` matched the condition.
But in mode 3, once the branch context inserts `k := true` or `k := false`,
`typecheckVar` and `typecheckDeref` treat **every** carrier with guard tag `k`
as affected — both `guardClosure k d` and `guardOnly k` share the same match
arm (`Typecheck.lean:729`).

The typechecker implicitly needs a **transfer principle**: if `matchGuard`
proves the predicate for one owner with tag `k`, then every other carrier
cleaned by tag `k` is semantically compatible.  No such transfer principle
exists on `main`.

### 3.2. `agreeOnClean` is too weak before the branch

`agreeOnClean` only constrains entries that are already clean under the
pre-branch regime.  In mode 3, the interesting tag satisfies `R.lookup? k =
none`, so the relevant carriers are **not** clean yet.  The pre-branch two-run
hypothesis gives no cross-run agreement for them.

Even if each run is internally coherent, that does not imply the two runs agree
on the newly activated `k`-carriers.

### 3.3. The `guardOnly` gap

`guardOnly k` carriers are an independent soundness gap:

1. `typecheckVar` treats `guardOnly k` and `guardClosure k d` identically —
   both de-poison when `tagEnv[k] = (true, _)`.
2. `joinPredicates` creates `guardOnly k` from different `guardClosure k d1`
   and `guardClosure k d2` (`Typecheck.lean:342`).
3. `locsRegime.guardOnly_ok` and `varsRegime.guardOnly_ok` impose **zero
   semantic constraint** — no predicate-holds, no regime alignment, nothing.
4. But `qtypCleanUnder R qt` considers `guardOnly k` clean when
   `R.lookup? k = some true`.

So the mode-3 counterexample survives even with `guardOnly k` carriers.

`guardOnly` is **not** merely a join artifact.  It deliberately models linked
values — e.g., after `x = read buf`, a successful check on `x` (via
`matchGuard`) can also de-poison a separately-tagged `buf` via a shared tag.
**Do not try to fix the soundness gap by disabling `guardOnly` de-poisoning.**

### 3.4. `Regime.bound` and visibility

When `k >= ctx.regime.bound`, the branch-local insert into `regime.map` is
invisible through `Regime.lookup?`.  This creates a mismatch:

- `tagEnv[k] = true` or `false` in the branch context
- but `regime.lookup? k = none`

This breaks `tagEnvConsistentWithRegime` (`StepFR.lean:49`):

```lean
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

Neither `StepFR_IH` nor any guard-coherent IH can be applied to the branch
context when this invariant fails.

The case split `k < bound` vs `k >= bound` is unavoidable and forms the
structural skeleton of the mode-3 proof.

### 3.5. `wfTagMeaningCtx` is vacuous for `guardOnly`

`wfTagMeaningCtx` only constrains `guardClosure`-style entries.  The chain
`wfTagMeaningCtx → EnvRespectsTagMeaning → GuardDescInEnvsDeep →
qtypGuardDesc?` never fires for `guardOnly`.

So a context can contain `guardOnly k'` with `tm.lookup k' = none` and still
satisfy `wfTagMeaningCtx`.  Any repair that needs a descriptor behind
`guardOnly k` must add that fact explicitly elsewhere.

The preservation proof at `StepFR.lean` actively exploits this vacuity.
**Do not try to make `wfTagMeaningCtx` track `guardOnly`** — it would break
existing proofs.

### 3.6. Deep closure depth matters

A top-level invariant about tags in `ctx.varEnv` and `ctx.memEnv` is not
enough.  Closure application can expose captured environments that were not
top-level before, and `newRef` can copy their guard tags into memory.

Concrete obstruction found on the abandoned branch:

- Start with `regime.bound = 0`.
- Keep a function in the context whose captured environment contains
  `guardOnly 5`.
- Apply the function so the captured variable becomes visible in the body.
- Then `newRef` that value.

The result contains a guard-tagged memory cell with tag `5`, but the regime
bound is still `0`.

Any successful invariant must account for deep captured values, not only
top-level bindings.

### 3.7. Separate deep facts do not compose after joins

After `joinETyps`, the same apparent closure shape may be represented by
multiple `FnTClosure.regular` entries with different captured environments
(`σcap`).  Two separately-produced deep properties can choose different captured
environments and fail to line up.

In practice, this killed attempts to prove one deep fact for regime reasoning
and another for canonical/coherence reasoning and then combine them later.
Progress resumed only after those facts were bundled into a single combined
deep property.

---

## 4. Dead Ends

These consumed significant time on the abandoned branch and should not be
retried blindly.

### 4.1. `predTagsBoundedInCtx` preservation is FALSE

**Idea:** Thread an invariant asserting all top-level guard tags in the context
are below `regime.bound`, letting us derive `k < bound` from `matchGuard`
success.

**Why false:** Closure application (`applyFnTClosure`) exposes captured
environments as the body context's `varEnv`.  `typecheckNewRef` can copy a
guard tag from a captured env into the output `memEnv`.  The guard tag can be
arbitrarily large (from deep captures) while `regime.bound` stays at 0.

**Do not build a new plan around preserving `predTagsBoundedInCtx`.**

### 4.2. Bumping `regime.bound` in mode 3

**Idea:** When entering a mode-3 branch, also raise the bound so the insert is
always visible.

**Why rejected:** Breaks `Regime.monotoneStep` (`Typecheck.lean:188`), a true
structural invariant with 326+ uses across proof files.  `monotoneStep` asserts
`R'.bound = R.bound`.  Changing this cascades through all proofs that depend on
bound equality.

### 4.3. Strengthening `locsRegime.guardOnly_ok`

**Idea:** Require θ-realization and memory-lookup evidence for `guardOnly_ok`,
paralleling `locsRegime.withPred_ok`.

**Why rejected:** `consistentRegimeSpec` (`FaultRobustness.lean:390`) is an
unconditional `List.Forall` over all memory entries.  In the two-run proof, the
typechecker types both `if`-branches but only one executes at runtime.  The
joined `memEnv` may reference cells whose realization depends on which branch
was taken.  Requiring θ-realization on all entries conflicts with the two-run
comparison architecture.

**Lesson:** Keep `locsRegime.guardOnly_ok` zero-obligation.  Put value
constraints for `guardOnly` in a separate coherence predicate.

### 4.4. Separate `guardOnlyTagsInTagMeaning` bridge predicate

**Idea:** New predicate asserting every `guardOnly k` tag has a backing
`tm.lookup k = some d` entry.

**Why rejected:** Cannot be derived from current premises.
`wfTagMeaningCtx` is vacuous for `guardOnly` (§3.5).  The predicate only
relocates the gap.

**Fix:** Fold the `tm.lookup k` requirement directly into the coherence
predicate (§6.2).

### 4.5. Direct projection from canonical single-run theorem into old single-run

**Idea:** Replace the old `singleIH` in
`TypeSystemEnforcesFaultRobustness_step_IOFree` with a call to a stronger
canonical single-run theorem, projecting the output.

**Why rejected:** Blocked on the INPUT side.  The canonical single-run requires
`guardClosureCoherentWith` and `guardTaggedMemRealized` as input.  The two-run
step theorem's IH (`StepFR_IH`) does not carry these.  Cannot construct
canonical inputs from weak premises.

### 4.6. Combined dispatcher with universal `singleIH`

**Idea:** Inside the combined dispatcher, construct `singleIH` by calling the
canonical single-run and projecting.

**Why rejected:** `singleIH : StepFRSingleRunFinalCleanPcTrue_IH` is
universally quantified over ALL runtime states (`∀ μ ρ θ, ...`).  The canonical
single-run needs canonical-witness inputs for each SPECIFIC state.  You cannot
build a universally-quantified function from state-specific evidence.

**Lesson:** The consumers (`stepFR_ite_mode4`, `stepFR_app`) call `singleIH` at
specific states — they do not need full universality.  The fix is to upgrade the
`singleIH` parameter TYPE to require strong inputs (§7.3).

### 4.7. Per-run coherence without a shared witness

**Idea:** Independent per-run existentials (`∃ canon₀, ...` and `∃ canon₁, ...`).

**Why rejected:** Allows `canon₀ k d ≠ canon₁ k d`.  Even though both runs
satisfy coherence internally, the transfer principle needs values to agree
**across** runs.  This was not just inconvenient — it directly fails in the
two-run setting.

### 4.8. Output-side deep-property fan-out

**Idea:** Add the combined deep property to the OUTPUT of `StepFR`.

**Why problematic:** Mode-4 branch assemblies (4 combinations) each need ~90
lines.  Mode-1/mode-2 take `IH : StepFR_IH` (not IHGC), so they cannot produce
it without additional parameter changes.

**Lesson:** Restrict deep property threading to the INPUT side during initial
construction.  Output-side should be deferred to the combined dispatcher.

---

## 5. Candidate Solutions

The counterexample shows that one of the following must change: the theorem
statement, the typing rule, the underlying tag discipline, or the semantic
invariants.  Two candidate repairs are under consideration.

### 5.1. Option A: Restrict de-poisoning to the matched owner

The simplest sound repair: stop mode 3 from de-poisoning arbitrary same-tag
carriers.  Only the specific variable that `matchGuard` matched would be
cleaned.

#### Current behavior

`matchGuard` returns `Tag × Deps` and discards the identity of the matched
owner.  Mode 3 inserts `k |-> true/false` into both the tag environment and the
regime map, causing `typecheckVar` and `typecheckDeref` to de-poison every
carrier of tag `k`.

#### Required changes

**1. Extend `matchGuard` to return the matched owner identity.**  For variable
owners, the identity is the variable name.  This information is already
available at `Typecheck.lean:646` but is currently discarded before the return
at line 694.

**2. Replace the global tag/regime insertion with a local context rewrite.**
Instead of inserting `k |-> true` into the tag environment and regime map,
mode 3 directly updates the matched owner's type in the branch context:

- True branch: `ctxTrue.varEnv[x] := ⟨etyp, ctx.pc, noPred⟩` (de-poisoned,
  predicate consumed)
- False branch: `ctxFalse.varEnv[x] := ⟨etyp, true, noPred⟩` (forced
  poisoned)

All other variables with tag `k` keep their existing types.  The tag
environment and regime stay unchanged (`R.lookup? k = none`).

**3. Reference owners are more complex.**  A naive approach — rewriting memory
type entries at the owner's `LocSet` — is unsound as an "owner only" mechanism:
any variable whose `LocSet` overlaps would also see the rewrite.  A correct
mechanism needs an owner token that `typecheckDeref` checks before de-poisoning.
A simpler initial version restricts owner-only de-poisoning to variable owners
and leaves reference owners conservatively dirty (falling through to mode 4).

#### Implementation staging: variable owners first

**Step 1:** Restrict `matchGuard` to variable owners.  Skip the reference
matching loop (`Typecheck.lean:651–690`).  If the only match was through a
reference, `matchGuard` returns an error, and `typecheckIf` falls through to
mode 4.

**Step 2:** Return the matched variable name alongside `Tag × Deps`.

**Step 3:** Rewrite the matched variable instead of inserting into the regime.

#### Precision impact

| Scenario | Option A | Current (unsound) | Notes |
|----------|----------|-------------------|-------|
| Single variable owner | clean | clean | Most common case; identical |
| Copy of matched owner | **dirty** | clean | Copy shares value but is not the matched owner |
| Reference owner | **dirty** | clean | Ref matching unsupported without owner-token |
| Inner re-check on same owner | **dirty** | clean | Predicate consumed to `noPred` at branch entry |
| Unrelated same-tag carrier | dirty | "clean" | Option A correct; current rule unsound |

The predicate-consumption issue deserves emphasis.  Under Option A, the matched
owner's type is rewritten to `noPred`.  An inner `if` cannot rematch the same
owner because `matchGuard` needs a `guardClosure` predicate.  The current rule
preserves the original `guardClosure` in the environment and only adds
tag/regime knowledge.

#### Engineering cost

- Changes to `Typecheck.lean`: `matchGuard` signature and mode-3 rewrite
- Changes to proof lemmas about mode-3 typing structure
- **No new runtime invariant**, no changes to `consistentWithRegime` (71 use
  sites untouched), no preservation proofs
- No changes to `FaultRobustnessSpec` or the top-level theorem statement
- Significantly cheaper than Option B

### 5.2. Option B: Coherence invariant — strengthen the semantics

Preserve the current mode-3 typing power by adding a semantic invariant that
justifies the global de-poisoning.  This requires two complementary pieces.

#### The invariant

A new deep coherence invariant:

> For any fixed runtime state, if two live carriers have the same exact
> tag+predicate combination, then their runtime values are equal.

Here "same exact tag+predicate combination" means the same tag and the same
structural predicate closure, not merely the same tag.  Tag-only occurrences
are outside this invariant.

This directly blocks the counterexample: `x` and `y` both carry
`guardClosure 0 "a" (a == a) []`, so the invariant forces them to have the
same runtime value whenever both are live with that exact tag+predicate.

The proof argument for mode 3 would then be: when mode 3 inserts `k |-> true`,
every same-tag carrier that gets de-poisoned either (a) is a tag-only carrier,
which is purely logical, or (b) is a tag+predicate carrier with the same exact
closure as the matched owner.  In case (b), the coherence invariant guarantees
value equality, so the `predSat` fact established by `PredSatLaws.match_iff`
for the owner transfers to the carrier.

#### Companion same-tag discipline

The equality invariant alone is insufficient because mode 3 de-poisons by tag
alone — `var_guard_true` and `deref_guard_true` inspect only the tag `k`, not
whether the carrier's predicate closure matches `matchGuard`'s.

The gap: two live tag+predicate carriers may share tag `k` but have
structurally different predicate closures.  Mode 3 would clean both, but the
equality invariant only relates carriers with the same exact closure.

The preferred enforcement mechanism is **downgrading to tag-only**: whenever a
typing rule would introduce a `guardClosure` for tag `k` into a context that
already contains a structurally different `guardClosure` for the same `k`, both
entries collapse to `guardOnly k`.  This already happens at join points
(`joinPredicates`, `Typecheck.lean:342`).  The remaining work is extending this
discipline to assignment, function capture, and sequential composition.

**Structural equality is brittle.**  Closures capture full typing-environment
snapshots via `VarTypeEnv.toCaptured`.  Semantically "the same guard" created
at two different program points will often compare structurally unequal because
the surrounding context grew or changed.  When this happens frequently, the
companion discipline fires often, downgrading to `guardOnly` and losing future
`matchGuard` ability (since `matchGuard` skips `guardOnly` at
`Typecheck.lean:630`).

#### The witness must be shared across the two runs

Per-run existential witnesses are not enough.  If run 0 has `canon₀ k d = x₀`
and run 1 has `canon₁ k d = x₁`, nothing relates `x₀` and `x₁`.  Progress
resumed on the abandoned branch only after switching to a shared witness for
both runs:

```lean
∃ canon,
  guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀ ∧
  guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁
```

#### `guardOnly` must be covered by the same coherence story

Trying to repair only `guardClosure` is insufficient.  The coherence predicate
must explicitly cover `guardOnly`, asserting for each `guardOnly k` entry:
`∃ d, tm.lookup k = some d ∧ canon k d = v`.

#### Guard-tagged memory realization

The proof repeatedly needs: if `ctx.memEnv` says a memory cell carries guard
tag `k`, then `θ` already realizes that cell.  This is not derivable from
existing premises.  `runtimeInstantiatesCtx` is one-way on memory (`θ →
memEnv`, not the reverse).  When `R.lookup? k = none`,
`consistentRegimeSpec` is vacuous at tag `k`.

A repair that keeps the current typing rule needs a new explicit premise:

```lean
def guardTaggedMemRealized (ctx : TypeContext) (θ : RealizationMap) : Prop :=
  ∀ l qt k, ctx.memEnv.lookup l = some qt →
    qtypGuardTag qt = some k → ∃ a, θ.lookup l = some a
```

#### Post-state monotonicity of the witness

Even after evaluating `e1`, the proof must transfer facts from the pre-`e1`
witness to the post-`e1` state.  This requires an output-side monotonicity
property:

```lean
def MonotoneCanonicalWitness (canon canon' : GuardClosureCanonical) : Prop :=
  ∀ k d v, canon k d = v → canon' k d = v
```

#### Precision impact

| Scenario | Option B | Current (unsound) | Notes |
|----------|----------|-------------------|-------|
| Coherent same-tag family | clean | clean | Preserved by the invariant |
| Same tag, different closure (after downgrade) | tag-only | guardClosure | Companion discipline fires; `matchGuard` can no longer match this tag |
| Structural σcap divergence | tag-only | guardClosure | Capture-env snapshot grew between two sites |

#### Engineering cost

- New deep predicate definition in `RegimeConsistency.lean`
- New premise and conclusion in `StepFR` (affects every case proof)
- Preservation proofs for every evaluation rule (assignment, application,
  if-expression, etc.)
- Likely changes to `FaultRobustnessSpec` and the top-level theorem
- Risk that the invariant turns out to be unprovable if the type system does
  not actually enforce the required same-tag discipline

### 5.3. Comparison and staging

The two approaches are not mutually exclusive.  A pragmatic path is:

1. Implement Option A first to obtain a sound mode 3 with minimal proof
   disruption.
2. If the precision loss proves limiting, upgrade to Option B later by adding
   the coherence invariant and restoring the global de-poisoning rule.

**Head-to-head:**

| Scenario | Option A | Option B |
|----------|----------|----------|
| Single variable owner | clean | clean |
| Coherent copy/alias | **dirty** | clean |
| Reference owner | **dirty** | clean |
| Inner re-check on same owner | **dirty** | clean |
| After companion-discipline downgrade | n/a | **tag-only** (loses future matching) |

The single-owner case is the most common pattern.  Both approaches are identical
there.

**Engineering trade-off:**

| Dimension | Option A | Option B |
|-----------|----------|----------|
| De-poisoning power | Matched variable only | Coherent same-tag family (minus downgrades) |
| Reference owners | Dirty (or needs owner-token) | Clean |
| Inner re-matching | Lost (predicate consumed) | Preserved |
| Future matching after conflict | n/a | Lost (downgrade to `guardOnly`) |
| Proof cost | Low | High |
| Changes to `Typecheck.lean` | Yes (`matchGuard` + mode 3) | Companion discipline rules |
| Changes to proof infrastructure | Local (mode-3 lemmas) | Global (new invariant everywhere) |
| Risk | Low | Moderate (invariant may be unprovable) |
| Top-level theorem statement | Unchanged | Likely strengthened |

---

## 6. Required Infrastructure for Option B

This section details the proof-side changes needed if the current mode-3 typing
rule is kept and the coherence-invariant approach (Option B) is pursued.

### 6.1. New definitions (in `RegimeConsistency.lean`)

```lean
abbrev GuardClosureCanonical := Tag → GuardDesc → Value

def capturedVarsGuardClosureCanonicalProperty (canon : GuardClosureCanonical)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ x qt v k d, σcap.lookup x = some qt → ρcap.lookup x = some v →
    qtypGuardDesc? qt = some (k, d) → canon k d = v

def capturedVarsGuardOnlyCanonicalProperty (canon : GuardClosureCanonical)
    (tm : TagMeaning) (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ x qt v k, σcap.lookup x = some qt → ρcap.lookup x = some v →
    qt.pred = Predicate.guardOnly k →
    ∃ d, tm.lookup k = some d ∧ canon k d = v

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

def guardTaggedMemRealized (ctx : TypeContext) (θ : RealizationMap) : Prop :=
  ∀ l qt k, ctx.memEnv.lookup l = some qt →
    qtypGuardTag qt = some k → ∃ a, θ.lookup l = some a

def guardClosureFunctionalPerTag (ctx : TypeContext) : Prop :=
  Relator.RightUnique (GuardDescInEnvsDeep ctx.varEnv ctx.memEnv)
```

This last predicate is derivable from `wfTagMeaningCtx tm ctx`.

### 6.2. Combined deep property (avoid member-matching)

Regime evidence and coherence evidence must be carried at the same `σcap`
to avoid the member-matching problem (§3.7).  Define a combined deep property:

```lean
fun σcap ρcap =>
  capturedVarsRegimePropertyMasked masked predSat R μ σcap ρcap ∧
  capturedVarsGuardClosureCanonicalProperty canon σcap ρcap ∧
  capturedVarsGuardOnlyCanonicalProperty canon tm σcap ρcap ∧
  capturedVarsTypingProperty θ σcap ρcap
```

This must be a conjunct of the canonical single-run bundle, not a separate
parameter.  The masked-false wrapper (`StepFR.lean:~2913`) needs to provide
combined evidence as input; as a bundle conjunct, it is passed through
structurally.

Impact: ~80 bundle references + ~26 theorem signatures across ~13 files.  Most
per-case proofs: carriers unchanged → inherited via
`deepValueQTypProperty_mono`.

### 6.3. Upgrade `singleIH` parameter type

The consumers (`stepFR_ite_mode4`, `stepFR_app`) take `singleIH` with weak type
(`consistentWithRegime` input).  Change to a guard-coherent type that also
requires `guardClosureCoherentWith` and `guardTaggedMemRealized` as input.  The
consumers provide these at each call site from the combined dispatcher's IH.

### 6.4. Strengthen masking premise

Change from:

```lean
(∀ k, masked k → ctx.regime.lookup? k = none)
```

to:

```lean
(∀ k, masked k → k ≥ ctx.regime.bound)
```

This is strictly stronger (implies the old premise).  Benefits:

- Trivially true at top level (`masked = fun _ => False`)
- Automatically preserved (`R'.bound = R.bound` via `monotoneStep`)
- Eliminates `predTagsBoundedInCtx` entirely

With this, mode 3 keeps the same mask and case-splits on `k < bound`:

- `k < bound`: regime insert visible, construct `locsRegime.withPred_ok` via
  transfer principle
- `k >= bound`: regime insert invisible, extend mask to
  `masked' = fun t => masked t ∨ t = k`

### 6.5. `StepFRGuardCoherent` combined dispatcher

A new combined theorem type proving `StepFR` AND carrying guard coherence.
Two-run interface with shared canonical witness, `MonotoneCanonicalWitness` in
output, and `∀ masked'` IH for mode-3 mask flexibility.

Input additions to `StepFR`:

- Shared canonical witness:
  `∀ canon, guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀ →
  guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁ → ...`
- `guardTaggedMemRealized ctx θ₀` and `guardTaggedMemRealized ctx θ₁`
- Combined deep property for both runs

Output additions:

- `∃ canon', MonotoneCanonicalWitness canon canon' ∧
  guardClosureCoherentWith canon' tm (ctxAfter ctx res) ... ∧ ...`

### 6.6. Top-level theorem weakening

`FaultRobustnessSpec` gets a new compound premise:

```lean
def InitialGuardClosureCoherence tm ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ :=
  (∃ canon, guardClosureCoherentWith canon tm ctx μ₀ ρ₀ θ₀
          ∧ guardClosureCoherentWith canon tm ctx μ₁ ρ₁ θ₁) ∧
  guardTaggedMemRealized ctx θ₀ ∧
  guardTaggedMemRealized ctx θ₁
```

For fresh initial states (empty heap, no guard-tagged variables): vacuously
true.  For specification-conforming states: natural well-formedness condition.

### 6.7. No further typechecker changes needed

The `vlet` shadowing rejection fix is already on `main`.  No further
typechecker changes are required for Option B.  The fix is entirely on the
proof side.

---

## 7. Proof Strategy for Option B

### 7.1. Overall structure

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

The hardest subcase is consistently the visible different-branch case
(`k < bound`, `b₀ ≠ b₁`).

### 7.2. Transfer principle (`k < bound` cases)

When the regime insert is visible, the proof must construct
`locsRegime.withPred_ok` for every carrier tagged with `k`:

1. `matchGuard_ok_extract_owner_in_ctx` gives the matched owner's descriptor
   `(k, d)` and its location in `ctx.varEnv` or `ctx.memEnv`.
2. `guardClosureFunctionalPerTag` (from `wfTagMeaningCtx`) gives uniqueness:
   any other carrier with `guardClosure k d'` has `d' = d`.
3. `guardClosureCoherentWith` gives `canon k d = v` for every such carrier.
4. `matchGuard_ok_runtime_owner_predSat_iff` gives
   `b_rt = true ↔ predSat k μ v_owner`.
5. Since all carriers have the same value (`canon k d`), the predicate result
   transfers to all of them.

For tag-only carriers: `locsRegime.guardOnly_ok` requires zero evidence — no
transfer needed.

### 7.3. Mask extension (`k >= bound` cases)

When the regime insert is invisible:

1. Extend mask to `masked' = fun t => masked t ∨ t = k`.
2. Verify masking premise: `masked' t → t ≥ bound` (either old mask, or
   `t = k → k ≥ bound`).
3. `tagEnvConsistentWithRegimeMasked`: tag `k` is masked → ok.
4. `consistentWithRegimeMasked`: `R.lookup? k = none` → vacuous at `k`.
5. Call `IH_any_mask` with `masked'` on the branch.
6. At the join: unmask (drop `k` from mask).

### 7.4. The `regimeConsistentWithCtx` blocker and resolution

When `k >= bound`, the branch context has `tagEnv[k] = true` but
`regime.lookup? k = none`, breaking `regimeConsistentWithCtx`.

Resolution: both the IH and the per-case lemma signatures need masked variants
of `regimeConsistentWithCtx`.  The combined dispatcher's strong induction
naturally provides `∀ masked'` quantification.

### 7.5. Output regime and join

The output regime is `joinRegimes res2.regime' res3.regime'`.  For the
`ctxAfter ctx res` context, `regimeConsistentWithCtx` and
`consistentWithRegime` must be established.  The join helpers
(`tagEnvConsistentWithRegimeMasked_join_drop`,
`consistentWithRegimeMasked_join`, etc.) are needed here.

---

## 8. Architectural Alternatives

### 8.1. Direct `StepFR` strengthening (not attempted cleanly)

Instead of building a parallel canonical single-run theorem, strengthen `StepFR`
itself to carry `guardClosureCoherentWith` in both input and output.  This
avoids duplicating per-case proofs and the standalone-projection problem (§4.5).

**Risk:** Every per-case proof must thread coherence.  But for most cases
(literal, var, op, seq, fn, pfn), carriers are unchanged → coherence is
trivially preserved.  Only `assign`, `app`, `ite`, `vlet` need real work.

**Advantage:** Eliminates the need for a separate canonical single-run theorem
entirely.

### 8.2. Masking from the start

The `main` branch already has `StepFRSingleRunFinalCleanPcTrueMaskedRegParam`.
Consider making all of `StepFR` masked from the start (with
`masked = fun _ => False` at top level).  This eliminates the need to maintain
separate masked and unmasked variants.

### 8.3. Incremental approach: prove `k < bound` first

The `k < bound` case requires the transfer principle but not masking.  The
`k >= bound` case requires masking but the transfer principle is vacuous.
Prove them independently, starting with the conceptually harder `k < bound`.

### 8.4. Require `k < regime.bound` as a mode-3 precondition

A middle ground: mode 3 could assert `k < regime.bound` and fail otherwise,
causing those cases to fall through to mode 4 (standard if).  This eliminates
the `k >= bound` case entirely.  The cost: `matchGuard` may succeed for tags
that mode 3 cannot handle (those with `k >= bound`), causing a precision loss
for those cases.

---

## 9. Key Lemma References (`main` branch)

| Lemma/Definition | File | Purpose |
|---|---|---|
| `StepFR` | StepFR.lean:984 | Two-run FR step theorem type |
| `StepFR_IH` | StepFR.lean:5578 | Inductive hypothesis for StepFR |
| `consistentWithRegime` | RegimeConsistency.lean:818 | Regime consistency predicate |
| `locsRegime` constructors | RegimeConsistency.lean:843 | Per-entry regime evidence (locs) |
| `varsRegime` constructors | RegimeConsistency.lean:863 | Per-entry regime evidence (vars) |
| `qtypGuardTag` | TypeSafety.lean:777 | Extract tag from any guard predicate |
| `qtypGuardDesc?` | RegimeConsistency.lean:36 | Extract (tag, desc) from guardClosure |
| `closureCapturedVarsRegime` | RegimeConsistency.lean:~888 | Deep regime property for closures |
| `deepValueQTypProperty` | RegimeConsistency.lean:888 | Generic deep recursion through closures |
| `deepValueQTypProperty_mono` | RegimeConsistency.lean:~935 | Monotonicity under P strengthening |
| `capturedVarsRegimeProperty` | RegimeConsistency.lean:~940 | Property at each closure level |
| `capturedVarsTypingProperty` | RegimeConsistency.lean:~960 | Typing evidence at each closure level |
| `wfTagMeaningCtx` | RegimeConsistency.lean:119 | Tag meaning well-formedness |
| `GuardDescInEnvsDeep` | RegimeConsistency.lean:107 | Deep guard descriptor extraction |
| `EnvRespectsTagMeaning` | RegimeConsistency.lean:113 | Envs respect tag meaning |
| `tagEnvConsistentWithRegime` | StepFR.lean:49 | tagEnv/regime agreement |
| `regimeConsistentWithCtx` | StepFR.lean:58 | Full context/regime consistency |
| `Regime.lookup?` | Typecheck.lean:154 | Bounded regime lookup |
| `Regime.monotoneStep` | Typecheck.lean:188 | Regime monotonicity invariant |
| `matchGuard` | Typecheck.lean:~620 | Guard condition matcher |
| `joinPredicates` | Typecheck.lean:331 | Predicate join (creates guardOnly) |
| `terminatesTo_ite_inv'` | SemanticsProperties.lean | Ite evaluation inversion |
| `joinMemEnvsStrong` | Typecheck.lean | Strong memory join |
| `joinRegimes` | Typecheck.lean:~175 | Conservative regime join |
| `consistentRegimeSpec` | FaultRobustness.lean:390 | Top-level spec regime consistency |
| `FaultRobustnessSpec` | FaultRobustness.lean:707 | Top-level fault-robustness property |

---

## 10. Summary

### What the abandoned branch achieved

- The strong-invariant route (Option B) is not obviously impossible.  With
  enough extra structure, the branch proved the stronger canonical single-run
  mode-3 case.
- The two-run proof reduces naturally to four subcases (§7.1).
- The hardest subcase was consistently the visible different-branch case.
- The original `main` interfaces are genuinely insufficient.
- The remaining blockers were mostly proof-engineering complexity inside the
  four-way two-run split.

### Practical takeaways for a clean restart

If keeping the current mode-3 typing rule (Option B):

- Expect to strengthen proof interfaces, not just fill the existing holes.
- Expect a new semantic/coherence premise at the top level.
- Treat `guardOnly`, `k >= bound`, and deep captured environments as
  first-class concerns from the start.
- Do not spend time trying to rescue `predTagsBoundedInCtx`.
- Do not assume the old single-run theorem is salvageable without interface
  changes.

If those costs are unacceptable, Option A (restrict de-poisoning to matched
owner) is significantly cheaper and removes the soundness problem entirely,
at the cost of losing same-tag de-poisoning for non-owner carriers.

### Minimum changes from `main` (Option B)

1. New definitions in `RegimeConsistency.lean` (§6.1)
2. Strengthen `StepFR` with shared canonical witness and combined deep property
   (§6.2, §6.5)
3. Upgrade `singleIH` type (§6.3)
4. Strengthen masking premise to `k >= bound` (§6.4)
5. New top-level premise in `FaultRobustnessSpec` (§6.6)
6. Mode-3 proof body: 4-case skeleton with transfer principle and mask
   extension (§7)

### Minimum changes from `main` (Option A)

1. Extend `matchGuard` to return matched owner identity
2. Rewrite mode-3 to update matched variable only (no regime/tagEnv insert)
3. Adapt mode-3 proof lemmas (substantially simpler)
4. No changes to `StepFR`, `consistentWithRegime`, `FaultRobustnessSpec`,
   `Regime.monotoneStep`, `locsRegime`, `varsRegime`, or
   `consistentRegimeSpec`
