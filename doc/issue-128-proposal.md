# Proposal for Issue #128

GitHub issue: https://github.com/vzaliva/poison-lang/issues/128

## 1. Proposed Solution: Synchronize R.map with L, Keep Strong Invariant

### Problem Summary

When the typechecker inserts `k |-> true` into `L` (tagEnv) — in
if-mode-3 branches and while-depoison loop bodies — it leaves `R`
(regime) unchanged.  The proof invariant `tagEnvConsistentWithRegime`
requires every true-tagged entry in `L` to be mirrored in `R`, i.e.:

```lean
∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

When `R(k) = none` this invariant is violated, blocking the IH
application in `stepFR_ite_mode3` (and, by the same mechanism, in any
future while-depoison FR proof).

The mismatch occurs in **two** places in the typechecker:

1. **`typecheckIf` mode 3** (`Typecheck.lean:1686,1739`): branches get
   `L[k |-> true/false]` but `R` is inherited unchanged.
2. **`runWhileFixpoint` with guard** (`Typecheck.lean:1063`): loop body
   gets `L[k |-> true]` but `R` is inherited unchanged.

### Fix: Update R.map Alongside L (Strong Invariant Preserved)

**Update `R.map` (not `R.bound`) alongside `L`.**
Insert `k |-> b` in the regime map when inserting `k |-> b` in
tagEnv.  For tags with `k < R.bound` this makes `R.lookup? k = some b`,
restoring consistency.  The bound is never modified.

**Note on `Regime.monotoneStep`:**  `Regime.monotoneStep` constrains
the *input-to-output* regime relationship (i.e., the regime entering
the if/while vs. the regime leaving it).  The per-branch regimes
`R[k |-> true]` and `R[k |-> false]` are *intermediate*: they exist
only inside the branch typing contexts and do not appear in the
output.  `joinRegimes` drops the disagreeing entry for `k` (since
`true ≠ false`), so the output regime has `R(k) = none` — exactly
the input regime's state.  Thus `Regime.monotoneStep` between input
and output is preserved.

### Historical: Bound-Guarded Invariant Attempt

An earlier attempt tried to avoid changing the typechecker by changing
the invariant itself: make `tagEnvConsistentWithRegime` constrain only
in-bound tags (tags `k < R.bound`).  Concretely, this meant adding an
explicit bound guard, e.g.:

```lean
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ →
    k < regime.bound →
    regime.lookup? k = some true
```

or an equivalent `if k < regime.bound then ... else True` formulation.
This would make a mode 3 branch context "consistent" even when
`R.lookup? k = none` because `k` is out of bounds.

This approach failed in practice for proof engineering reasons:

1. It pushed a new `k < R.bound` premise into essentially every use of
   `tagEnvConsistentWithRegime` across the StepFR development (e.g.
   `stepFR_var`, `stepFR_deref`, and many transport/preservation lemmas),
   since all of them would now have to prove boundedness whenever they
   relied on the invariant.

2. Those call sites typically learn `k` only from a lookup
   `tagEnv.get? k = some ⟨true, deps⟩`, which does not imply
   `k < R.bound`.  The obligation becomes stuck unless we thread an
   additional invariant about all predicate tags being in-bound anyway.

3. Once we accepted that proving boundedness of tags returned by
   `matchGuard` is unavoidable, it was strictly better to keep the
   original strong invariant and instead fix the typechecker so that
   branch contexts satisfy it.

Therefore we kept the original definition (no bound guard) and moved
the burden to (a) synchronizing `R.map` with `L` inside the branch
typing contexts and (b) proving that `matchGuard` returns in-bound tags
in the relevant ioFree contexts.

**Why `k < R.bound` holds:** In ioFree mode, `matchGuard` can only
return tags `k < regime.bound`.  This follows from three facts:

1. **No fresh tags in ioFree.**  The only fresh-tag generator is
   `typecheckFrand` (`Typecheck.lean:1161`), which throws before
   reaching `generateFreshTagRes`.  All extern operations have the
   same ioFree guard.
2. **All predicate tags come from the initial spec.**  Since no fresh
   predicates are created, every predicate in `memEnv`/`varEnv` was
   present in the initial context.
3. **`wfRegime` bounds spec tags.**  `wfRegime` (`FaultRobustness.lean:89`)
   requires `∀ k, k ∈ inputSpecTags s → k < R.bound`.

Therefore, when mode 3 inserts `k` into `R.map`, we have `k < R.bound`,
so `R.lookup? k = some true/false`, and the strong invariant is
satisfied.

**Summary by mode:**

- **Mode 1** (`R(k) = some true`): R already has the entry.
  Existing `tagEnvConsistentWithRegime_insert_true` applies.
- **Mode 2** (`R(k) = some false`): L inserts `k |-> false`, which
  never triggers the invariant (it only constrains true entries).
- **Mode 3 / while** (`R(k) = none`): the R.map update plus
  `k < R.bound` makes `R.lookup? k = some true`, satisfying the
  strong invariant via `tagEnvConsistentWithRegime_insert_true_with_regime`.

### Symmetry Decision: Both Branches Get R.map Updates

Both the true branch (`R[k |-> true]`) and the false branch
(`R[k |-> false]`) receive regime map insertions.  This was a
deliberate design choice:

1. **Semantic faithfulness**: In the true branch we know the guard
   predicate holds; in the false branch we know it does not hold.
   Recording both facts in the regime is the faithful representation.

2. **Nested if-expressions**: If a nested `if` in the false branch
   references the same guard tag `k`, having `R(k) = some false` in
   the regime allows the typechecker to use mode 2 (known-false)
   rather than mode 3 (unknown).  Removing the false-branch insertion
   would lose this information, potentially affecting typing precision
   for nested conditionals.

3. **Proof obligations are dischargeable**: The false-branch
   `consistentWithRegime` obligations mirror the true-branch ones.
   `PredSatLaws.match_iff` gives `b = true ↔ predSat k μ v` for the
   owning value.  In the false branch (`b = false`), the negation
   `¬ predSat k μ v` is exactly what `varsRegime.withPred_ok` /
   `locsRegime.withPred_ok` need for the `b = false → ¬qtypPredHolds`
   direction.

4. **Output regime is unchanged**: `joinRegimes` drops entries where
   the two branches disagree.  Since `true ≠ false`, the output
   regime has `R(k) = none` regardless, so the insertions are purely
   local to each branch.

**Dependency on tag reuse resolution:** Points 2 and 3 above are
only sound if the tag reuse caveat (Section 5) can be resolved.
Setting `R(k) = false` globally inside the false branch asserts
`¬ predSat k μ v` for **all** entries with guard tag `k`, not just
the owning one.  If multiple entries share tag `k` but bind different
runtime values, this assertion may be semantically wrong — not merely
hard to prove.  If tag reuse cannot be ruled out or controlled, the
false-branch insertion may need to be dropped (reverting to the
asymmetric approach where only the true branch gets `R[k |-> true]`
and the false branch inherits `R` unchanged).

## 2. Changes to Ott Rules

### If Rules

All four `R_unknown` rules need the same update.  Using
`if_depoison_R_unknown` as representative:

**Current** (`poison-lang.ott:1163–1171`):

```
match_guard e1 G S = k with LS
R(k) = none
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L ; R
pm ; R ; join pc p1 ; G ; S ; L[k |-> true using LS] |- e2 : ...
pm ; R ; join pc p1 ; G ; S ; L[k |-> false using LS] |- e3 : ...
------  :: if_depoison_R_unknown
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3 : ...
  -| JoinGStrong G2 G3 ; JoinL L2 L3 ; JoinR R2 R3
```

**Proposed** (changes marked `(*)`):

```
match_guard e1 G S = k with LS
R(k) = none
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L ; R
pm ; R[k |-> true] ; join pc p1 ; G ; S ; L[k |-> true using LS] |- e2 : ...   (*)
pm ; R[k |-> false] ; join pc p1 ; G ; S ; L[k |-> false using LS] |- e3 : ... (*)
------  :: if_depoison_R_unknown
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3 : ...
  -| JoinGStrong G2 G3 ; JoinL L2 L3 ; JoinR R2 R3
```

The notation `R[k |-> b]` means inserting `k |-> b` in the regime map
**without** changing `R.bound`.  Since `k < R.bound` (Section 1),
`lookup?` returns `some b`.

The conclusion is unchanged: `JoinR R2 R3` drops the disagreeing
entry for `k` (since `true != false`), so the output regime has
`R(k) = none`.

The same change applies to `if_depoison_fn_R_unknown`,
`if_depoison_pfn_R_unknown`, and `if_depoison_ref_R_unknown`.

### While Rule

**Current** (`poison-lang.ott:1259–1276`), body premise:

```
pm ; indexR R i ; join ... ; ... ; S ; indexL L i[k |-> true using LS] |- e2 : ...
```

**Proposed**:

```
pm ; (indexR R i)[k |-> true] ; join ... ; ... ; S ; indexL L i[k |-> true using LS] |- e2 : ...  (*)
```

The while fixpoint absorbs this: `indexR R 0 = R` has no entry for `k`,
so `JoinR(indexR R 0, body_output)` drops `k` (one side missing).
The iteration regimes `indexR R i` thus never accumulate `k`, and the
insertion is purely local to each iteration's body context.

## 3. Changes to Code

### `typecheckIf` mode 3 (`Typecheck.lean:1735`)

Current:

```lean
| none => do
    let branchPc := joinPoison ctx.pc p1
    let ctxTruePoisoned  := { ctxTrue  with pc := branchPc }
    let ctxFalsePoisoned := { ctxFalse with pc := branchPc }
```

Proposed:

```lean
| none => do
    let branchPc := joinPoison ctx.pc p1
    let regimeTrue  := { ctx.regime with map := ctx.regime.map.insert k true }
    let regimeFalse := { ctx.regime with map := ctx.regime.map.insert k false }
    let ctxTruePoisoned  := { ctxTrue  with pc := branchPc, regime := regimeTrue }
    let ctxFalsePoisoned := { ctxFalse with pc := branchPc, regime := regimeFalse }
```

Note: `R.bound` is untouched.  Since `k < R.bound` (Section 1),
`lookup?` returns `some true/false` after insertion.

### `runWhileFixpoint` with guard (`Typecheck.lean:1062`)

Current:

```lean
let bodyCtx := match guardOpt with
  | some (k, deps) =>
      { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
  | none => bodyCtxBase
```

Proposed:

```lean
let bodyCtx := match guardOpt with
  | some (k, deps) =>
      { bodyCtxBase with
        tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps),
        regime := { bodyCtxBase.regime with map := bodyCtxBase.regime.map.insert k true } }
  | none => bodyCtxBase
```

## 4. Proof Invariant: No Changes to Definition

### `tagEnvConsistentWithRegime` is unchanged (`FaultRobustnessProofs.lean:35`)

The definition stays as:

```lean
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true
```

The strong invariant is preserved because `matchGuard` only returns
in-bound tags in ioFree mode (Section 1).

### Impact on Existing Lemmas

- **`tagEnvConsistentWithRegime_insert_true`** (line 55): Unchanged.
  Used when `R(k) = some true` (mode 1).

- **`tagEnvConsistentWithRegime_insert_false`** (line 77): Unchanged.
  False entries never trigger the invariant.

- **`tagEnvConsistentWithRegime_invalidate`** (line 96): Unchanged.
  Invalidation only removes entries.

- **All downstream uses** are unaffected because the definition has not
  changed.

### New Lemmas (implemented)

For mode 3, where we insert into **both** tagEnv and R.map
simultaneously:

```lean
-- True branch: insert k |-> true into both tagEnv and R.map
private lemma tagEnvConsistentWithRegime_insert_true_with_regime
    (tagEnv : TagEnv) (R : Regime) (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegime tagEnv R)
    (hk_bound : k < R.bound) :
    tagEnvConsistentWithRegime
      (tagEnv.insert k ⟨true, deps⟩)
      { R with map := R.map.insert k true } := by
  ...

-- False branch: insert k |-> false into both tagEnv and R.map
private lemma tagEnvConsistentWithRegime_insert_false_with_regime
    (tagEnv : TagEnv) (R : Regime) (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime
      (tagEnv.insert k ⟨false, deps⟩)
      { R with map := R.map.insert k false } := by
  ...
```

The true-branch lemma requires `k < R.bound`, which is discharged
using `matchGuard_tag_in_bound` (Section 5).  The false-branch lemma
needs no bound premise because false entries never trigger the
invariant.

## 5. Proof Obligations for Future `stepFR_ite_mode3` / While-Depoison Work

The items in this section document proof obligations on the
**critical path** to closing `stepFR_ite_mode3` (the issue #128
blocker) and the while-depoison FR proof.  Some have been
implemented (with partial sorry's); the rest must be completed
to fully resolve the issue.

**Critical path** from issue #128 to resolution (dependency order):

1. `matchGuard_tag_in_bound` — establishes `k < R.bound` from
   bounded context tags *(implemented, one sorry in ref case)*.
2. `tagEnvConsistentWithRegime_insert_true_with_regime` — uses
   `k < R.bound` to restore the `tagEnvConsistentWithRegime`
   invariant after inserting into both L and R *(implemented, proven)*.
3. `consistentWithRegime_insert_regime_{true,false}` — transfers the
   full `consistentWithRegime` to the extended regime
   *(true version implemented, closure conjunct sorry'd;
   false version not yet implemented)*.
4. `predTagsBoundedInCtx` invariant — threading through StepFR
   so that (1)'s premises can be discharged at the call site
   *(not yet implemented)*.
5. `PredSatLaws.match_iff` application — derives predicate
   satisfaction from guard evaluation to discharge (3)'s premises
   *(not yet implemented)*.

**Recommended work order** (highest risk first — fail fast):

1. **Tag reuse caveat** — if multiple entries share guard tag `k`,
   `PredSatLaws.match_iff` only gives satisfaction for the owning
   value. If this cannot be resolved, the entire approach may need
   to be reconsidered. Investigate first.
2. **`predTagsBoundedInCtx` invariant** — requires threading a new
   premise through StepFR or deriving it from existing premises.
   Potentially invasive; assess feasibility early.
3. **`PredSatLaws.match_iff` application** — should be
   straightforward once (1) and (2) are resolved.
4. **Remaining sorry's** — mechanical fixes (ref case non-emptiness,
   while-depoison per-iteration).

### Proving `matchGuard` Returns In-Bound Tags (Critical Path Step 1)

The **required** bridge for closing `stepFR_ite_mode3` is a lemma
establishing that `matchGuard` only returns tags within the regime's
domain in ioFree mode.  Without this, `tagEnvConsistentWithRegime_insert_true_with_regime`
cannot be applied (it requires `k < R.bound`):

```lean
private lemma matchGuard_tag_in_bound
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hvar_bounded : ∀ x qt k', ctx.varEnv.lookup x = some qt →
        qtypGuardTag qt = some k' → k' < ctx.regime.bound)
    (hmem_bounded : ∀ l qt k', ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k' → k' < ctx.regime.bound) :
    k < ctx.regime.bound
```

The `hvar_bounded` / `hmem_bounded` premises state that all predicate
guard tags in `varEnv` and `memEnv` are within the regime's bound.
This needs to be established as an invariant preserved by ioFree
typechecking:

**Proof strategy** (parallels `typecheck_ioFree_preserves_nextTag`):

1. In ioFree mode, `nextTag` is preserved
   (`typecheck_ioFree_preserves_nextTag`, `TypeSafety.lean:5243`).
2. No fresh predicate tags are created (only `typecheckFrand`
   generates them, which is blocked by the ioFree guard).
3. Predicates flow through unchanged (`typecheckVar`, `typecheckDeref`)
   or are dropped to `noPred` (`joinPredicates`).
4. Therefore, all predicate tags in any sub-context during ioFree
   typing are the same tags that were in the initial context.
5. By `wfRegime` (`FaultRobustness.lean:89`), all initial spec tags
   satisfy `k < R.bound`.

The formal proof would be an induction on the typechecker structure,
showing that `hpreds_bounded` is preserved at each step.  Since
ioFree never creates predicates, most cases are trivial (predicates
are inherited or dropped).

### Deriving `consistentWithRegime` for the Extended Regime (Critical Path Step 3)

### The Obligation

`StepFR` requires `consistentWithRegime predSat R ctx μ ρ θ` as a
precondition for IH applications.  `consistentWithRegime`
(`RegimeConsistency.lean:818`) is:

```lean
(∀ l qt k, ctx.memEnv.lookup l = some qt →
   qtypGuardTag qt = some k → R.lookup? k ≠ none →
   locsRegime predSat R μ θ (l, qt)) ∧
(∀ x qt k, ctx.varEnv.lookup x = some qt →
   qtypGuardTag qt = some k → R.lookup? k ≠ none →
   varsRegime predSat R μ ρ (x, qt)) ∧
(∀ x qt v, ctx.varEnv.lookup x = some qt →
   ρ.lookup x = some v →
   closureCapturedVarsRegime predSat R qt μ v)
```

The gate is `R.lookup? k ≠ none`.  When `R(k) = none` (the original
mode 3 / while regime), this gate is closed and the first two
conjuncts impose **no** obligations for tag `k`.  After inserting
`k |-> true` in the regime map (with `k < R.bound`), the gate opens:
we must now produce `locsRegime`/`varsRegime` witnesses for **every**
entry in `memEnv`/`varEnv` whose guard tag is `k`.

### What the Witness Requires

`locsRegime.withPred_ok` (for a loc entry) and
`varsRegime.withPred_ok` (for a var entry) both need:

```
hregime : R.lookup? k = some b
hconsist : (b = true  → qtypPredHolds predSat qt μ v) ∧
           (b = false → ¬qtypPredHolds predSat qt μ v)
```

In the true branch `b = true`, so the obligation is
`qtypPredHolds predSat qt μ v` (predicate satisfaction).

### How to Derive It

The key tool is `PredSatLaws.match_iff`
(`RegimeConsistency.lean:670`): given `matchGuard condition Γ σ fuel
= .ok (k, deps)` and the condition evaluating to `Value.bool b`,
it gives `b = true ↔ predSat k μ v` for the **owning value** `v`
(the specific variable or ref-via-memory entry that `matchGuard`
matched).

The derivation chain for the true-branch IH (mode 3 if / while body):

1. `matchGuard` succeeded with `(k, deps)`.
2. The condition evaluates to `Value.bool b₀` in run 0 (and `b₁` in
   run 1).
3. The IH for `e1` gives `valueHasETyp θ₀' (Value.bool b₀)
   ETyp.bool` etc.
4. `PredSatLaws.match_iff` + `runtimeInstantiatesCtx` gives
   `b₀ = true ↔ predSat k μ₀ v₀` for the owning value `v₀`.
5. In the true branch (`b₀ = true`), we have `predSat k μ₀ v₀`,
   which yields `qtypPredHolds predSat qt μ₀ v₀` for the owning
   entry.
6. For entries with guard tag `k` that were already constrained under
   the outer regime (i.e., entries where the outer
   `R.lookup? k ≠ none` was satisfied — but this is vacuous since
   the outer regime has `R(k) = none`), the outer
   `consistentWithRegime` already provides witnesses that can be
   transferred.

### Tag Reuse Caveat — Investigation Findings

**Status**: Investigation complete.  The tag reuse problem is real and
has two distinct sub-problems that affect different conjuncts of
`consistentWithRegime`.  This section summarizes the findings and
options.

#### Background: `consistentWithRegime` Structure

`consistentWithRegime` (`RegimeConsistency.lean:818`) has three
conjuncts:

1. **locsRegime** (gated by `R.lookup? k ≠ none`): obligations for
   memory entries with active guard tag.
2. **varsRegime** (gated by `R.lookup? k ≠ none`): obligations for
   variable entries with active guard tag.
3. **closureCapturedVarsRegime** (ungated): for every `(x, qt, v)` in
   varEnv/ρ, recurses into the value `v` and checks
   `capturedVarsRegimeProperty` at each closure nesting level.

Inside conjunct 3, `capturedVarsRegimeProperty`
(`RegimeConsistency.lean:792`) IS gated by `R.lookup? k_x ≠ none` —
but the outer iteration over all variables is not.  When R grows
(adding `k ↦ true`), previously closed gates inside closures open,
requiring evidence that wasn't needed under the smaller R.

#### Sub-problem A: Top-Level Tag Reuse (Conjuncts 1 & 2)

`PredSatLaws.match_iff` gives `predSat k μ v₀` only for the
**owning** entry — the specific variable or ref that `matchGuard`
matched.  `consistentWithRegime` conjuncts 1 and 2 require witnesses
for **all** entries with guard tag `k` whose gate opens under R'.

If multiple entries share guard tag `k` but bind different runtime
values, satisfaction at the owning value does not transfer.  The
project documentation ("Tag Uniqueness") establishes that each tag
uniquely identifies a predicate body and captured context, but does
not prevent multiple `memEnv`/`varEnv` entries from sharing the same
guard tag `k` (via let-binding or assignment that propagates a
qualified type).

**Key finding — `predSat` is memory-independent**:
`predSat_mem_noPred_compat` (`FaultRobustnessProofs.lean:659`) proves:

```lean
∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v
```

So `predSat k μ v` depends only on `v`, not on memory state.  This
simplifies the semantic question to: do all entries with guard tag `k`
bind the same runtime value?

#### Sub-problem B: Closure Captured Vars (Conjunct 3 — the Sorry'd Gap)

This is the harder sub-problem and the actual sorry in
`consistentWithRegime_insert_regime_true` (line 9324).

**The design assumption that breaks:**  The comment on
`closureCapturedVarsRegime` (`RegimeConsistency.lean:804–806`) says:

> Checked against the CURRENT regime R rather than the regime at
> capture time.  This is sound because Regime.monotoneStep only
> removes entries, so any obligation that held under a larger regime
> still holds under the current (smaller) one.

`closureCapturedVarsRegime_monotone` (`FaultRobustnessProofs.lean:731`)
formalizes this: given `Regime.monotoneStep R R'` (R shrinks to R'),
evidence under R transfers to R'.  The key is that `monotoneStep`
only **drops** entries — when a gate closes, the obligation disappears,
so the evidence is trivially preserved.

**The mode 3 problem**: When we insert `k ↦ true` into R (going from
R to R' = `{ R with map := R.map.insert k true }`), R' has **more**
entries than R.  This is regime **growth**, not shrinkage.  The
monotone lemma goes the wrong direction:

- `closureCapturedVarsRegime_monotone` handles R → R' when
  `monotoneStep R R'` (R shrinks to R')
- We need R → R' when R **grows** to R' (k added)
- For captured vars inside closures with guard tag k:
  - Under R: `R.lookup? k = none` → gate closed → no evidence needed
  - Under R': `R'.lookup? k = some true` → gate open → evidence needed
  - But no evidence was collected when the gate was closed

**Why it's architectural, not semantic**: `predSat` is
memory-independent (sub-problem A finding), so if a captured value
`v_cap` satisfies `predSat k μ v_cap`, it does so regardless of
memory state.  The predicate still "holds" in the intended semantic
sense.  But the proof framework never recorded evidence for captured
vars with guard tag k when the gate was closed, and there is no
mechanism to recover it when the gate reopens.

#### Resolution Options

**(a) Gate conjunct 3 like conjuncts 1 & 2.**  Change the third
conjunct of `consistentWithRegime` from:

```lean
∀ x qt v, ctx.varEnv.lookup x = some qt →
   ρ.lookup x = some v →
   closureCapturedVarsRegime predSat R qt μ v
```

to something like:

```lean
∀ x qt v k, ctx.varEnv.lookup x = some qt →
   ρ.lookup x = some v →
   qtypGuardTag qt = some k → R.lookup? k ≠ none →
   closureCapturedVarsRegime predSat R qt μ v
```

This would make the gate uniform across all three conjuncts.  When R
grows to R', the new obligations for the newly-opened gate could be
discharged using the same `PredSatLaws.match_iff` derivation as
conjuncts 1 and 2 (modulo sub-problem A).

**Risk**: This changes the `consistentWithRegime` definition.  Every
existing proof that establishes or uses conjunct 3 would need to be
updated.  The `stepFR_vlet` and `stepFR_var` proofs that shuttle
closure evidence through variable storage/retrieval would need to
handle the gate.  Also, `closureCapturedVarsRegime_monotone` and
its callers would need reworking.

**(b) Carry "latent evidence" for closed gates.**  Add an auxiliary
invariant (either a fourth conjunct or a separate `StepFR` premise)
that records `predSat k μ v_cap` for captured vars even when
`R.lookup? k = none`.  When the gate reopens, the latent evidence
is promoted.

Since `predSat` is memory-independent, the latent evidence remains
valid across memory growth — `predSat_mem_noPred_compat` ensures
that.  The invariant could be:

```
∀ x qt v, varEnv.lookup x = some qt → ρ.lookup x = some v →
   ∀ (captured var with guard tag k in closure of v),
     predSat k μ v_cap
```

**Risk**: Adds complexity to the proof framework.  Requires threading
through all StepFR cases.  May need significant engineering effort.

**(c) Prove all entries with tag k alias the owning value.**  Show
that `runtimeInstantiatesCtx` forces all entries with guard tag `k`
to bind the same runtime value (or values that share the same
predicate satisfaction status).

**Assessment**: Investigation found that `runtimeInstantiatesCtx`
does not directly relate values across different variables.  Tags
propagate through let-binding (same value), deref (same value), and
ref aliasing (shared location), but `joinPredicates` drops to
`noPred` when tags disagree.  A formal single-owner proof would need
to show that tag propagation through assignment and let-binding
preserves value identity, which is non-trivial.

**(d) Accept sorry as known architectural limitation.**  Document that
the closure conjunct transfer for regime growth is a known gap.  The
sorry in `consistentWithRegime_insert_regime_true` (conjunct 3) would
remain, and the overall fault-robustness proof would be conditional
on this gap.

#### Recommendation

Option (a) (gating conjunct 3) is the most principled fix — it makes
the framework uniformly handle regime growth the same way for all
three conjuncts.  However, it is also the most invasive, requiring
changes to the `consistentWithRegime` definition and all its clients.

The decision depends on how much refactoring is acceptable.  If
modifying `consistentWithRegime` is too costly, option (d) (accept
sorry) is a pragmatic fallback that still allows the rest of the
mode 3 proof to proceed.

**All subsequent tasks (predTagsBoundedInCtx threading, false-branch
transfer lemma, match_iff application) are ON HOLD pending this
decision**, since the choice of resolution affects whether and how
those tasks should be implemented.

### While-Depoison: Same Obligation Per-Iteration

The "join drops k so it's local" argument (Section 2) is correct for
the **output** regime.  But inside each iteration body, the IH
application requires `consistentWithRegime` for the body context with
the extended regime (`R.map.insert k true`).  The same derivation
chain above applies per-iteration, using the guard evaluation result
from that iteration.

### New Lemma: `consistentWithRegime` Under R.map Insert

A transfer lemma is needed for the full `consistentWithRegime`.
With symmetric R.map updates, **both** a true-branch and false-branch
version are required (or a single lemma parameterized by `b : Bool`):

```lean
-- True branch (implemented: conjuncts 1+2 proven, conjunct 3 sorry'd)
private lemma consistentWithRegime_insert_regime_true
    (predSat : PredSat) (ctx : TypeContext) (R : Regime)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (k : Tag)
    (hcwr : consistentWithRegime predSat R ctx μ ρ θ)
    (hk_bound : k < R.bound) (hk_none : R.lookup? k = none)
    (hmem_k : ∀ l qt, ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k →
        locsRegime predSat { R with map := R.map.insert k true } μ θ (l, qt))
    (hvar_k : ∀ x qt, ctx.varEnv.lookup x = some qt →
        qtypGuardTag qt = some k →
        varsRegime predSat { R with map := R.map.insert k true } μ ρ (x, qt)) :
    consistentWithRegime predSat { R with map := R.map.insert k true } ctx μ ρ θ

-- False branch (not yet implemented — same structure with b = false)
private lemma consistentWithRegime_insert_regime_false
    (predSat : PredSat) (ctx : TypeContext) (R : Regime)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (k : Tag)
    (hcwr : consistentWithRegime predSat R ctx μ ρ θ)
    (hk_bound : k < R.bound) (hk_none : R.lookup? k = none)
    (hmem_k : ∀ l qt, ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k →
        locsRegime predSat { R with map := R.map.insert k false } μ θ (l, qt))
    (hvar_k : ∀ x qt, ctx.varEnv.lookup x = some qt →
        qtypGuardTag qt = some k →
        varsRegime predSat { R with map := R.map.insert k false } μ ρ (x, qt)) :
    consistentWithRegime predSat { R with map := R.map.insert k false } ctx μ ρ θ
```

The `hmem_k` / `hvar_k` premises are discharged at each call site
using `PredSatLaws.match_iff` and the guard evaluation result.
For the true branch, `match_iff` gives `predSat k μ v`; for the
false branch, it gives `¬ predSat k μ v`.  Both are modulo the
tag reuse caveat above.

## 6. Verification Checklist

### Completed (typechecker + spec changes, unblocks proof work)

- [x] Modify `typecheckIf` mode 3 in `Typecheck.lean` (Section 3)
- [x] Modify `runWhileFixpoint` body context in `Typecheck.lean` (Section 3)
- [x] Update Ott spec: 4 `if_depoison_*_R_unknown` + `while_depoison`
      (Section 2)
- [x] Update `typecheckIf_structure` in `TypeSafety.lean` to reflect
      new branch context shape (regime field changed)
- [x] Verify `regime_monotone` still holds for if/while
      (new lemmas: `joinRegimes_monotone_mode3`,
      `joinRegimes_monotone_while_body_ext`)
- [x] Add `tagEnvConsistentWithRegime_insert_true_with_regime` and
      `tagEnvConsistentWithRegime_insert_false_with_regime` lemmas
- [x] Update `stepFR_ite_mode3` hypotheses and
      `typecheckIf_ioFree_ok_pred_noPred` proof for new branch
      context shape
- [x] Run `make test` — 80/80 pass
- [x] Run `make lean-build` — compiles (no new sorry's)

### Proof infrastructure (implemented, some sorry's remain)

- [x] Add `regime_insert_lookup_other` and `regime_insert_lookup_self`
      helpers for reasoning about `R.map.insert k b` lookups
      (`FaultRobustnessProofs.lean:150`)
- [x] Add `matchGuard_ok_tag_from_ctx`: successful `matchGuard` implies
      the returned tag appears as `qtypGuardTag` in `varEnv` or `memEnv`
      (`FaultRobustnessProofs.lean:9219`; ref case sorry for LocSet
      non-emptiness — see below)
- [x] Add `matchGuard_tag_in_bound`: given bounded context tags,
      `matchGuard` returns `k < regime.bound`
      (`FaultRobustnessProofs.lean:9243`; fully proven modulo
      `matchGuard_ok_tag_from_ctx`)
- [x] Add `consistentWithRegime_insert_regime_true` transfer lemma
      (`FaultRobustnessProofs.lean:9268`; conjuncts 1+2 fully proven,
      conjunct 3 (closures) sorry'd — see tag reuse caveat below)
- [ ] Add `consistentWithRegime_insert_regime_false` transfer lemma
      (false-branch analogue; same structure, not yet implemented)

### Remaining sorry's in new lemmas

- [ ] `matchGuard_ok_tag_from_ctx` ref case: need `∃ l, l ∈ ls` for
      the location set. Follows from `matchGuard_refStep` requiring
      `ls.isEmpty = false`. Fix: strengthen `ref_match_from_refMatches`
      invariant to carry non-emptiness witness.
- [ ] `consistentWithRegime_insert_regime_true` conjunct 3
      (`closureCapturedVarsRegime`): transfer from R to R' is
      non-trivial because R' interprets more tags. Needs resolution
      of the tag reuse caveat (Section 5).

### Remaining work to close `stepFR_ite_mode3` (highest risk first)

- [ ] **Tag reuse caveat resolution** (highest risk — do first):
      Either prove a single-owner invariant, or adopt a hybrid
      approach.  If this cannot be resolved, the entire R.map
      synchronization approach may need to be reconsidered.
      Blocks closing the closure conjunct sorry in
      `consistentWithRegime_insert_regime_true` (Section 5).
- [ ] **`predTagsBoundedInCtx` invariant** (high risk — potentially
      invasive): Add to StepFR (or derive from existing premises) so
      `matchGuard_tag_in_bound`'s `hvar_bounded` / `hmem_bounded`
      premises can be discharged at the call site.
- [ ] **`consistentWithRegime_insert_regime_false`** (medium risk):
      False-branch analogue of the true-branch transfer lemma.
      Same structure; soundness depends on tag reuse resolution.
- [ ] **`PredSatLaws.match_iff` application** (medium risk):
      Derive predicate satisfaction from the guard evaluation result
      to discharge `consistentWithRegime_insert_regime_{true,false}`'s
      `hmem_k` / `hvar_k` premises for the owning entry.
- [ ] Same derivation chain for **while-depoison** body context
      per-iteration.
