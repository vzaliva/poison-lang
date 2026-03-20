# Mode 3: Analysis, Counterexample, and Repair

This document is a self-contained reference for understanding and resolving
the mode-3 `if` soundness problem.

**Terminology:**

- **tag-only** (`guardOnly k`): a guard tag with no predicate closure.
  Cannot be matched by `matchGuard`.
- **tag+predicate** (`guardClosure k arg body cap`): a guard tag with a
  predicate closure.  Can be matched by `matchGuard`.
- **mode 1 / mode 2**: `R.lookup? k = some true` / `some false`.
- **mode 3**: `R.lookup? k = none` (regime-unknown; the focus of this
  document).
- **mode 4**: `matchGuard` fails; standard `if`.

---

## 1. What Mode 3 Does

Mode 3 is the case of `typecheckIf` where `matchGuard` succeeds with tag `k`
but the outer regime has no entry for it (`R.lookup? k = none`).

The typechecker:

1. Types `e1` under `pureCtx := true` (the condition is pure).
2. Sets `branchPc := join ctx.pc p1` (condition poison flows into both
   branches).
3. Types the true branch under `tagEnv[k := (true, deps)]`,
   `regime.map[k := true]`, and `pc := branchPc`.
4. Types the false branch under `tagEnv[k := (false, deps)]`,
   `regime.map[k := false]`, and `pc := branchPc`.
5. Joins results conservatively with `pred = noPred`.

The regime inserts **do not bump `regime.bound`**.  Since
`Regime.lookup?` returns `none` when `k >= bound`, the insert is visible
only when `k < regime.bound`.  This creates a fundamental `k < bound` vs
`k >= bound` split in the proof (§3.4).

### 1.1. The two sorrys on `main`

- `stepFRSingleRun_ite_mode3_maskedReg` — single-run variant.  What remains
  is proving the masked-regime result for the taken branch.
- `stepFR_ite_mode3` — two-run variant.  What remains is handling the four
  branch-selection combinations (`b₀, b₁ ∈ {true, false}`) and proving
  agreement on the joined output.

Both are in `StepFRIte.lean`, after the IH has been applied to `e1`.

---

## 2. The Soundness Problem

The mode-3 sorry is **not just missing proof work** — `StepFR` is false under
the current invariant.  This section constructs the counterexample and
explains why.

### 2.1. Counterexample

The counterexample is a proof-level construction: an assumed initial typing
context fed to `StepFR`, not a source-language program.  Two variables share
guard tag `0`:

- `x`: clean `bool`, `guardClosure 0 "a" a []` (tag+predicate)
- `y`: dirty `int`, `guardOnly 0` (tag-only)

This models the linked-value pattern where a checkable status value is linked
to some other data via a shared tag (for example, `ok = validate(buf)` where
`ok` is a boolean and `buf` is linked to it).

```text
if x then y else 0
```

Initial `pc = false` (clean).  Regime: `bound = 1`, empty map — so
`R.lookup? 0 = none`, exactly mode 3.

`matchGuard` skips tag-only predicates, so `y` is never a match candidate.
For `x`, the predicate body instantiates to `x`, matching the condition.
Exactly one match; mode 3 fires.

Two runs: `x = true` in both (clean, must agree); `y = 1` vs `y = 2` (dirty,
may differ).

The counterexample works for any guarded predicate on `y` sharing tag `0`
— whether `guardOnly 0` or any `guardClosure 0 ...`.  The de-poisoning is
driven by the tag alone.

### 2.2. Why it typechecks as clean

The true-branch context inserts into both `tagEnv` and `regime.map`.  The
de-poisoning comes from `tagEnv`: `typecheckVar` inspects `ctx.tagEnv.get? k`
and finds `(true, deps)` for tag `0`.  Both tag-only and tag+predicate
carriers share the same match arm:

```lean
| Predicate.guardOnly k | Predicate.guardClosure k _ _ _ =>
    match ctx.tagEnv.get? k with
    | some ⟨true, _deps⟩ =>
        let qt' : QTyp := ⟨etyp, ctx.pc, Predicate.noPred⟩
```

So `y` is de-poisoned to `⟨int, branchPc, noPred⟩`.  Since `x` is clean,
`p1 = false`, so `branchPc = ctx.pc`.  The else branch returns
`0 : int :> clean`.  The joined result is typed clean.

### 2.3. Why the outputs disagree

Both runs evaluate `x` to `true`, take the true branch, and return `y`.
Run 0 returns `1`; run 1 returns `2`.  But the result is typed clean, so
`StepFR` would require `1 = 2` — a contradiction.

All `StepFR` premises are satisfiable: regime consistency is trivial (the
regime has no entry at `k`), and `agreeOnClean` only requires agreement on
clean inputs (`y` is dirty, so it is unconstrained).

### 2.4. Why the join does not help

The final branch join drops the temporary `tagEnv`/regime entry for `k`.
But the unsoundness already happened: `y` was de-poisoned inside the true
branch via `tagEnv`, and the clean output type survived the join.

### 2.5. What the counterexample really shows

Fault robustness says poisoned *values* must not leak into clean outputs.
De-poisoning a value declares it clean — the FR theorem then requires both
runs to agree on it.

`matchGuard` success does not force a branch in mode 3.  The regime is still
unknown, so either branch may be taken.  In the FR proof, it justifies a
**same-branch fact for a particular pair of runs**: if the checked owner
agrees across runs, then both runs evaluate the condition the same way and
take the same branch.

But taking the same branch is still not enough to make the result clean.  A
clean result requires the value actually returned by that branch to agree
across runs.

In the counterexample, `x` is clean so branch selection works.  The leak is
through `y`: mode 3 de-poisons every carrier of tag `k` without evidence of
cross-run agreement.

Returning the checked owner itself is not the bug: if the owner is dirty,
its poison flows into the condition, then into `branchPc`, and the result
stays poisoned.  The bug is that a check on `x` causes mode 3 to de-poison
a *different* same-tag value `y` whose content may differ across runs.

### 2.6. Follow-up stress case: same-type exact-closure sharing

This subsection is not needed to establish unsoundness — §2.1 already does
that.  It is a narrower follow-up case that explains why older
coherence-style repairs looked tempting, and tests whether a fix for the
basic boolean/tag-only problem is actually strong enough.

Consider this variant:

- `x`: clean `int`, `guardClosure 0 "a" (a == a) []`
- `z`: dirty `int`, `guardClosure 0 "a" (a == a) []`

```text
if (x == x) then z else 0
```

Two runs:

- Run 0: `x = 0`, `z = 1`
- Run 1: `x = 0`, `z = 2`

This is also unsound on `main` by the same mechanism:

- `x` is clean, so both runs agree on the condition and `branchPc` stays clean.
- Mode 3 then de-poisons `z` by tag.
- The result is typed clean, but the runs return `1` and `2`.

Unlike §2.1, the checked owner and the returned carrier have the same type and
the same exact guard descriptor.  That makes it plausible to rescue with a
stronger coherence invariant saying such carriers agree on their runtime
value.  `main` does not have such an invariant.  So §2.6 is not a second root
problem; it is a stress case for evaluating whether a proposed repair to the
basic cross-type/tag-only bug is really complete.

---

## 3. Root Causes

### 3.1. De-poisoning by tag, not by owner

`matchGuard` returns only `(k, deps)` — it does not retain the matched
owner's identity.  But mode 3 inserts `k := true` into `tagEnv`, causing
`typecheckVar` and `typecheckDeref` to de-poison **every** carrier with tag
`k`.  Both tag+predicate and tag-only share the same code path.

This tag-based de-poisoning is intentional: it is the linked-value mechanism
that shared tags were designed to support.  The soundness gap is not that mode
3 de-poisons by tag, but that the current FR invariant does not justify
extending evidence obtained from the matched owner to other same-tag carriers.

### 3.2. `agreeOnClean` does not cover newly activated tags

`agreeOnClean` constrains entries already clean under the pre-branch regime.
In mode 3, `R.lookup? k = none`, so tag-`k` carriers are not yet clean and
the two-run hypothesis says nothing about them.

### 3.3. The tag-only gap

Tag-only carriers are doubly unprotected:

1. De-poisoned by tag alone — their value is never checked.
2. `locsRegime.guardOnly_ok` and `varsRegime.guardOnly_ok` impose zero
   semantic constraint, so even in modes 1/2 they have no `predSat`-based
   protection.

Tag-only predicates model linked values (e.g., `ok = validate(buf)` where
`buf` carries `guardOnly k`).  Disabling their de-poisoning would remove a
core language capability.

### 3.4. `Regime.bound` and visibility

When `k >= regime.bound`, the `regime.map` insert is invisible through
`Regime.lookup?`.  This breaks `tagEnvConsistentWithRegime`:

```lean
∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

The branch context has `tagEnv[k] = true` but `regime.lookup? k = none`, so
neither `StepFR_IH` nor any guard-coherent IH can be applied.  The
`k < bound` vs `k >= bound` split is unavoidable.

### 3.5. `wfTagMeaningCtx` says nothing about tag-only entries

`wfTagMeaningCtx` ensures that all tag+predicate entries sharing tag `k`
carry the same predicate closure.  This makes each tag have a single
unambiguous meaning.  It says nothing about tag-only entries.

A tag-only entry for tag `k` can exist even if no predicate for `k` is
registered.  Any transfer principle that needs to know what predicate `k`
refers to cannot get that from `wfTagMeaningCtx` — a separate invariant
is needed.

### 3.6. Deep closures can surface arbitrary tags

A top-level invariant about tags in `ctx.varEnv` and `ctx.memEnv` is not
enough.  Closure application exposes captured environments, and `newRef` can
copy their guard tags into memory.  A captured `guardOnly 5` can surface as
a top-level memory cell while `regime.bound` is still `0`.

Any invariant must account for deep captured values, not only top-level
bindings.

### 3.7. Separate deep facts do not compose after joins

After `joinETyps`, the same closure shape may have multiple
`FnTClosure.regular` entries with different captured environments.  Two
separately-produced deep properties can pick different entries and fail to
line up.

The only successful approach was bundling regime and coherence facts into a
single combined deep property from the start.

---

## 4. Dead Ends

This section documents approaches that were tried on the abandoned branch and
failed.  It is kept as a reference so that future repair attempts do not
repeat the same mistakes.  The entries are technical and assume familiarity
with the proof infrastructure.

### 4.1. `predTagsBoundedInCtx` — FALSE

**Idea:** Assert all guard tags in the context are below `regime.bound`.

**Why false:** Closure application exposes deep captures; `newRef` can copy
them into memory.  Tags can be arbitrarily large while `regime.bound`
stays at 0.

### 4.2. Bumping `regime.bound` in mode 3

**Idea:** Raise the bound so the insert is always visible.

**Why rejected:** Breaks `Regime.monotoneStep`, which requires
`R'.bound = R.bound` and is used extensively across the proof files.

### 4.3. Strengthening `locsRegime.guardOnly_ok`

**Idea:** Require θ-realization evidence for tag-only entries.

**Why rejected:** `consistentWithRegime` requires `locsRegime`/`varsRegime`
evidence for every entry whose guard tag is active in the regime
(`R.lookup? k ≠ none`).  Strengthening `guardOnly_ok` to require
θ-realization would make this evidence mandatory for all active tag-only
entries.  In the two-run proof, the joined `memEnv` may reference cells
whose realization depends on which branch was taken, making this obligation
unsatisfiable.

**Lesson:** Keep `guardOnly_ok` zero-obligation; put value constraints in
a separate coherence predicate.

### 4.4. `guardOnlyTagsInTagMeaning` bridge predicate

**Idea:** Assert every tag-only entry has a backing `tm.lookup k = some d`.

**Why rejected:** Cannot be derived from current premises —
`wfTagMeaningCtx` ignores tag-only entries (§3.5).  Fold the requirement
into the coherence predicate instead.

### 4.5. Extending `wfTagMeaningCtx` to cover tag-only entries

**Idea:** Require tag-only entries to have a registered meaning.

**Why rejected:** Existing preservation proofs rely on tag-only entries
being unconstrained.  Changing this cascades through them.

### 4.6. Projection from canonical single-run into old single-run

**Idea:** Replace `singleIH` with a call to a stronger canonical single-run
theorem.

**Why rejected:** The canonical theorem requires `guardClosureCoherentWith`
and `guardTaggedMemRealized` as input.  `StepFR_IH` does not carry these;
cannot construct strong inputs from weak premises.

### 4.7. Combined dispatcher with universal `singleIH`

**Idea:** Build `singleIH` inside the combined dispatcher by calling the
canonical single-run.

**Why rejected:** `singleIH` is universally quantified over all runtime
states.  The canonical single-run needs state-specific coherence inputs.
Cannot build a universal function from specific evidence.

**Lesson:** Upgrade the `singleIH` parameter type to require strong inputs
(§6.3).

### 4.8. Per-run coherence without a shared witness

**Idea:** Independent per-run witnesses (`∃ canon₀` and `∃ canon₁`).

**Why rejected:** Allows `canon₀ k d ≠ canon₁ k d`.  The transfer principle
needs cross-run agreement; per-run witnesses do not provide it.

### 4.9. Output-side deep-property fan-out

**Idea:** Add the combined deep property to the OUTPUT of `StepFR`.

**Why problematic:** Mode-4 branch assemblies (4 combinations) each need ~90
lines.  Mode-1/mode-2 take `IH : StepFR_IH` (not IHGC), so they cannot produce
it without additional parameter changes.

**Lesson:** Restrict deep property threading to the INPUT side during initial
construction.  Output-side should be deferred to the combined dispatcher.

### 4.10. Restrict de-poisoning to the matched owner only

**Idea:** Stop mode 3 from de-poisoning arbitrary same-tag carriers and only
clean the matched owner (variable or dereferenced reference).

**Why rejected:** This eliminates the linked-value mechanism that tag-only
predicates were designed for.  The core use case — checking a status value
(e.g., `ok`) to de-poison linked data (e.g., `buf`) via a
shared tag — would no longer work.  Tag-only carriers can never be matched
owners (since `matchGuard` skips them), so they could never be de-poisoned
through mode 3 at all.  This is not a minor precision loss; it removes a
fundamental language capability.

### 4.11. Naive transfer principle

**Idea:** Justify tag-based mode-3 de-poisoning by a general transfer
principle: if one owner with tag `k` was checked, transfer that value-level
reasoning to other same-tag carriers.

**Why rejected:** Shared tags are not type-indexed.  The same tag can link
carriers of different types (for example, an `int` and a `bool`).  In that
setting there is no general value-equality or value-transport principle to
transfer from one carrier to another.  Any such argument only makes sense in
same-type cases, so a naive global transfer principle is not viable.

---

## 5. Proposed Solution: Coherence Invariant

The counterexample shows that one of the following must change: the theorem
statement, the typing rule, the underlying tag discipline, or the semantic
invariants.

The proposed repair preserves the current mode-3 typing power by adding a
semantic invariant that justifies the global de-poisoning.  This requires two
complementary pieces.

#### The invariant

A new deep coherence invariant:

> For any fixed runtime state, if two live carriers have the same exact
> tag+predicate combination, then their runtime values are equal.

Here "same exact tag+predicate combination" means the same tag and the same
structural predicate closure, not merely the same tag.  Tag-only occurrences
are outside this invariant.

By itself this does not block the primary counterexample from §2.1, because
that leak goes through a tag-only carrier.  It does directly block the
narrower same-type variant from §2.6: `x` and `z` both carry
`guardClosure 0 "a" (a == a) []`, so the invariant forces them to have the
same runtime value whenever both are live with that exact tag+predicate.

For same-type exact-closure carriers, the proof argument for mode 3 would
then be: when mode 3 inserts `k |-> true`, a same-tag tag+predicate carrier
with the same exact closure as the matched owner is forced by the coherence
invariant to have the same runtime value.  Then the `predSat` fact
established by `PredSatLaws.match_iff` for the owner transfers to that
carrier.  Tag-only carriers still need the additional story discussed below.

#### Companion same-tag discipline

The equality invariant alone is insufficient because mode 3 de-poisons by tag
alone — `var_guard_true` and `deref_guard_true` inspect only the tag `k`, not
whether the carrier's predicate closure matches `matchGuard`'s.

The gap: two live tag+predicate carriers may share tag `k` but have
structurally different predicate closures.  Mode 3 would clean both, but the
equality invariant only relates carriers with the same exact closure.

The preferred enforcement mechanism is **downgrading to tag-only**: whenever a
typing rule would introduce a tag+predicate entry for tag `k` into a context
that already contains a structurally different tag+predicate for the same `k`,
both entries collapse to tag-only.  This already happens at join points
(`joinPredicates`).  The remaining work is extending this
discipline to assignment, function capture, and sequential composition.

**Structural equality is brittle.**  Closures capture full typing-environment
snapshots via `VarTypeEnv.toCaptured`.  Semantically "the same guard" created
at two different program points will often compare structurally unequal because
the surrounding context grew or changed.  When this happens frequently, the
companion discipline fires often, downgrading to tag-only and losing future
`matchGuard` ability (since `matchGuard` skips tag-only predicates).

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
`consistentRegimeSpec` imposes no constraint at tag `k`.

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

| Scenario | With coherence | Current (unsound) | Notes |
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

---

## 6. Required Infrastructure

This section details the proof-side changes needed to implement the coherence
invariant approach.

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

For fresh initial states (empty heap, no guard-tagged variables): trivially
true.  For specification-conforming states: natural well-formedness condition.

### 6.7. No further typechecker changes needed

The `vlet` shadowing rejection fix is already on `main`.  No further
typechecker changes are required.  The fix is entirely on the
proof side.

---

## 7. Proof Strategy

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
4. `consistentWithRegimeMasked`: `R.lookup? k = none` → no constraint at `k`.
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
`k >= bound` case requires masking but the transfer principle is not needed.
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
| `StepFR` | StepFR.lean | Two-run FR step theorem type |
| `StepFR_IH` | StepFR.lean | Inductive hypothesis for StepFR |
| `consistentWithRegime` | RegimeConsistency.lean | Regime consistency predicate |
| `locsRegime` constructors | RegimeConsistency.lean | Per-entry regime evidence (locs) |
| `varsRegime` constructors | RegimeConsistency.lean | Per-entry regime evidence (vars) |
| `qtypGuardTag` | TypeSafety.lean | Extract tag from any guard predicate |
| `qtypGuardDesc?` | RegimeConsistency.lean | Extract (tag, desc) from guardClosure |
| `closureCapturedVarsRegime` | RegimeConsistency.lean | Deep regime property for closures |
| `deepValueQTypProperty` | RegimeConsistency.lean | Generic deep recursion through closures |
| `deepValueQTypProperty_mono` | RegimeConsistency.lean | Monotonicity under P strengthening |
| `capturedVarsRegimeProperty` | RegimeConsistency.lean | Property at each closure level |
| `capturedVarsTypingProperty` | RegimeConsistency.lean | Typing evidence at each closure level |
| `wfTagMeaningCtx` | RegimeConsistency.lean | Tag meaning well-formedness |
| `GuardDescInEnvsDeep` | RegimeConsistency.lean | Deep guard descriptor extraction |
| `EnvRespectsTagMeaning` | RegimeConsistency.lean | Envs respect tag meaning |
| `tagEnvConsistentWithRegime` | StepFR.lean | tagEnv/regime agreement |
| `regimeConsistentWithCtx` | StepFR.lean | Full context/regime consistency |
| `Regime.lookup?` | Typecheck.lean | Bounded regime lookup |
| `Regime.monotoneStep` | Typecheck.lean | Regime monotonicity invariant |
| `matchGuard` | Typecheck.lean | Guard condition matcher |
| `joinPredicates` | Typecheck.lean | Predicate join (creates guardOnly) |
| `terminatesTo_ite_inv'` | SemanticsProperties.lean | Ite evaluation inversion |
| `joinMemEnvsStrong` | Typecheck.lean | Strong memory join |
| `joinRegimes` | Typecheck.lean | Conservative regime join |
| `consistentRegimeSpec` | FaultRobustness.lean | Top-level spec regime consistency |
| `FaultRobustnessSpec` | FaultRobustness.lean | Top-level fault-robustness property |

---

## 10. Summary

### What the abandoned branch achieved

- The coherence-invariant route is not obviously impossible.  With
  enough extra structure, the branch proved the stronger canonical single-run
  mode-3 case.
- The two-run proof reduces naturally to four subcases (§7.1).
- The hardest subcase was consistently the visible different-branch case.
- The original `main` interfaces are genuinely insufficient.
- The remaining blockers were mostly proof-engineering complexity inside the
  four-way two-run split.

### Practical takeaways for a clean restart

Restricting de-poisoning to the matched owner was rejected because it
eliminates the linked-value mechanism (§4.10).  The coherence-invariant
approach is the remaining path:

- Expect to strengthen proof interfaces, not just fill the existing holes.
- Expect a new semantic/coherence premise at the top level.
- Treat tag-only entries, `k >= bound`, and deep captured environments as
  first-class concerns from the start.
- Do not spend time trying to rescue `predTagsBoundedInCtx`.
- Do not assume the old single-run theorem is salvageable without interface
  changes.

### Minimum changes from `main`

1. New definitions in `RegimeConsistency.lean` (§6.1)
2. Strengthen `StepFR` with shared canonical witness and combined deep property
   (§6.2, §6.5)
3. Upgrade `singleIH` type (§6.3)
4. Strengthen masking premise to `k >= bound` (§6.4)
5. New top-level premise in `FaultRobustnessSpec` (§6.6)
6. Mode-3 proof body: 4-case skeleton with transfer principle and mask
   extension (§7)
