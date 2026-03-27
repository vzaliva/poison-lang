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

The regime inserts are always visible since `Regime.lookup?` is an
unconditional map lookup (`regime.bound` was removed in §3.4).

### 1.1. The two sorrys on `main`

- `stepFRSingleRun_ite_mode3_maskedReg` — single-run variant.  What remains
  is proving the masked-regime result for the taken branch.
- `stepFR_ite_mode3` — two-run variant.  What remains is handling the four
  branch-selection combinations (`b₀, b₁ ∈ {true, false}`) and proving
  agreement on the joined output.

Both are in `StepFRIte.lean`, after the IH has been applied to `e1`.

---

## 2. Analysis Under the "Only Poisoned Values Carry Predicates" Invariant

### 2.1. The proposed invariant

We consider a design discipline:

> **Only poisoned non-reference values carry predicates.**  For any
> non-reference qualified type in `varEnv` or `memEnv`, if `pred ≠ noPred`,
> then `poison = true`.

Reference types are excluded: `typecheckLocation` returns a clean reference
that preserves the stored predicate from `memEnv`, so clean references with
predicates are a normal part of the type system.

This invariant is **partially enforced** today: `typecheckExternVal` rejects
clean values with predicates, and the parser rejects them in extern effects
and return specs.  However, the core `effectSpecToQTyp` and
`returnSpecToQTyp` paths do not enforce it, so it is not currently
maintained end-to-end.  Adopting this discipline would require:

- Adding the missing checks in the core typechecker.
- Verifying that no other typing rule produces clean non-reference values
  with predicates.
- Formalizing the invariant and proving it is preserved by all typing rules.
- Threading the invariant through `StepFR` and `StepFR_IH`.

### 2.2. Consequence: mode 3 always produces poisoned results

Under this invariant, mode 3 can never produce a clean result — neither as
a return value nor through memory side effects.  The argument covers the two
kinds of `matchGuard` owners:

**Variable owners.**  `matchGuard` matches a variable carrying a
tag+predicate.  By the invariant, the variable is poisoned.  `matchGuard`
requires the predicate to use its argument (`usesArg` check), so the
poisoned variable appears in the condition, making `p1 = true`.

**Reference owners.**  `matchGuard` matches through a dereference `!r`,
merging predicates across the reference's locset.  The reference `r` itself
may be clean, but `matchGuard` skips poisoned references.  For a clean
reference, the merged predicate comes from the memory cells, which are
non-reference `int` entries in `memEnv`.  By the invariant, those cells are
poisoned if they carry predicates.  Typing `!r` joins `ctx.pc` with the
cell's poison, giving a poisoned deref result.  The condition then includes
this poisoned operand, making `p1 = true`.

In both cases, `p1 = true`.  Then:

1. Mode 3 sets `branchPc := join ctx.pc p1 = join ctx.pc true = true`.

2. Inside the branch, `typecheckVar` de-poisons carriers to
   `⟨etyp, branchPc, noPred⟩ = ⟨etyp, true, noPred⟩` — still poisoned.

3. Memory writes use `join branchPc (value poison)`, which is at least
   `true` — stored cells stay poisoned.

4. The final result poison includes `branchPc = true` — the result is
   poisoned.

Since the result has `poison = true` and `pred = noPred`, it is not
`qtypCleanUnder` any regime, so `resultAgreesIfClean` is trivially satisfied.

### 2.3. Mode 3 produces no clean outputs

Under this invariant, mode 3 never produces a clean return value or a clean
memory write.  The tag-based de-poisoning inside mode 3's branches changes
individual carrier poisons to `branchPc`, but `branchPc` is already `true`,
so nothing gets cleaner.

The mode-3 machinery — `tagEnv` inserts, `regime.map` inserts, branch
joins — does real work inside the branches, but the poisoned `branchPc`
ensures none of it survives into the output as clean.

Mode 3 fires whenever `R.lookup? k = none`.  Three sources:

1. **`frand`** creates fresh tags not in the spec.  (`frand` is planned for
   removal from the language.)
2. **Extern specs with fresh tags**: extern functions and values can mention
   tag numbers not in `InputSpec`.  Later externs can also reuse spec tags
   (the typechecker does not require freshness — only
   `nextTag := max nextTag (k+1)`).
3. **Regime invalidation**: `invalidateRegimeDeps` drops regime entries when
   their dependency locations are written.  A spec tag can lose its regime
   entry and fall back to mode 3.

The FR precision impact: guard-based de-poisoning only works for tags that
have an active regime entry at the point of the `if`.  Any tag without one
falls into mode 3, which under this invariant produces only poisoned
results — no better than not matching at all.

Modes 1/2 handle guards with active regime entries, and mode 3 was supposed
to handle the rest conservatively.  But "conservatively" turns out to mean
"identically to not matching at all."

Under a disciplined usage model — where `frand` is dropped, all meaningful
guard tags come from `InputSpec`, later externs reuse those same tags, and
invalidating writes are avoided before guard checks — the precision impact
is small because most guards stay in modes 1/2.  But it is not zero: extern
specs that introduce fresh tags and regime invalidation after writes remain
as sources of mode-3 fallback.

### 2.4. Contrast with modes 1 and 2

Modes 1 and 2 (`R.lookup? k = some true/false`) are different: they do NOT
flow `p1` into `branchPc`.  Mode 1 uses `poison := join ctx.pc p2` (only
the taken branch's poison, not the condition's).  So mode 1 CAN produce
clean results even with a poisoned matched owner.

Mode 1 is safe because it is regime-determined — both runs take the same
branch.  And `qtypCleanUnder` has a `guard` constructor that makes tagged
carriers clean when `R.lookup? k = some true`, so `agreeOnClean` forces
both runs to agree on those carriers in the initial context.

Mode 3 cannot use this argument because the regime has no entry for `k`.

### 2.5. Implications

If this invariant is adopted as a global discipline:

- **The mode-3 proof strategy simplifies** to showing the result is always
  poisoned.  The argument: derive `p1 = true` from the invariant plus
  `matchGuard` success, then `branchPc = true`, then the joined result is
  poisoned.  No coherence invariant or transfer principle is needed.

- **This is not a local patch.**  The invariant must be formalized, threaded
  through `StepFR` and `StepFR_IH`, and proved preserved by every typing
  rule.  The core typechecker needs missing enforcement checks (in
  `effectSpecToQTyp` and `returnSpecToQTyp`).  This is real work, but
  substantially less than the coherence-invariant approach.

- **Mode 3 produces no clean outputs** under this discipline.  The
  linked-value de-poisoning pattern (e.g., `ok = validate(buf)`) does not
  work in mode 3 — it only works in mode 1, where the regime determines
  the branch.

- **This is a language-level design choice**, not just a proof observation.
  It says: predicates are for fault-sensitive (poisoned) values only.  This
  is already partially reflected in `wfInputSpec` for critical inputs.
  Adopting it globally makes the restriction explicit and uniform.


- split `stepFR_ite_mode3` on `res1.qualType.poison`;
- do not reintroduce the deleted bridge theorem;
- do not pursue a bounded-tags theorem/interface route.

History §4.4.1 already records that `predTagsBoundedInCtx` preservation is
false in this project, so the `k < bound` / `k >= bound` split must be handled
without relying on a global bounded-tags invariant.

Next target:

1. Read the current decision point in §3.3.
2. Decide the concrete handling plan for the `k >= bound` case.
3. Only then resume proof implementation in `LeanProofs/StepFRIte.lean`.

Done condition for this step:

- the document records the current blocker and the live options accurately;
- we have chosen a concrete handling plan for the `k >= bound` case;
- the chosen route is consistent with History §4.4 and §4.5.

### 3.2. Current Status
The invariant work is now in place:

- `predOnlyOnPoisonedNonRefCtx` / `predOnlyOnPoisonedNonRefResult` are defined;
- `typecheckExpr_preserves_predOnlyOnPoisonedNonRef` is proved;
- the core spec constructors enforce the restriction on clean predicate-carrying
  non-reference values;
- invariant-carrying IH interfaces have been threaded through the relevant
  `StepFR` infrastructure.

Since then, the local mode-3 proof strategy has changed:

- the earlier bridge-theorem approach has been dropped;
- `stepFR_ite_mode3` now splits on `res1.qualType.poison`;
- in the poisoned-condition branch, the result agreement is vacuous;
- in the clean-condition branch, clean agreement on the condition yields
  `b₀ = b₁`, eliminating the mixed-branch cases there.
- the bounded-tags route is no longer under consideration, because History
  §4.4.1 already rules out `predTagsBoundedInCtx` preservation.

The remaining work is now local to the two mode-3 proof bodies in
`StepFRIte.lean`.

### 3.3. Current Decision Point

The active design question is now:

> How should `stepFR_ite_mode3` handle the `k >= bound` branch-context case,
> given that global bounded-tags routes are already ruled out by History §4.4.1?

When `k >= bound`, mode 3 can produce branch contexts where:

- `tagEnv.get? k = some ⟨true, deps⟩`;
- `regime.lookup? k = none`.

So ordinary branch-local `regimeConsistentWithCtx` can fail, which blocks the
standard two-run IH even in same-branch cases.

The bounded-tags theorem/interface route is no longer a live option.

The live proof-engineering tools are:

1. **Masked/single-run helper route.**
   Finish `stepFRSingleRun_ite_mode3_maskedReg` and reuse it, or use
   `singleIH` directly, for the difficult `k >= bound` branch-context cases.

2. **Smaller local helper route.**
   Introduce a more targeted local helper for the `k >= bound` same-branch
   branch-context case, without trying to restore full ordinary
   `regimeConsistentWithCtx` on `ctxTrue` / `ctxFalse`.

These routes are likely complementary rather than competing:

- masked/single-run reasoning is the natural tool for the poisoned-condition
  mixed-branch cases, where `branchPc = true`;
- a smaller local helper is the natural tool for the subtle
  clean-condition, same-branch, `k >= bound` case, where the regime insert is
  invisible and `branchPc` may still be false.

### 3.4. Completed: `regime.bound` Removed

**Executed on 2026-03-27.**  Route 1 from the original analysis was chosen and
implemented: `regime.bound` was removed entirely from the `Regime` struct.

#### Background (historical)

`Regime.bound` was introduced on 2026-01-05 (commits 4c1b9a9-cda525d) for the
full-IO FR proof to handle `frand`, which creates fresh guard tags from the
`nextTag` supply.  Under `forall R`, an adversarial regime could mark a fresh
tag `true`, making the result `qtypCleanUnder` and requiring two independent
random draws to agree.  The bound prevented this by making `Regime.lookup?`
return `none` for tags `>= bound`.

The `.ioFree` pivot (2026-01-20) made this unnecessary: `frand`, `rand`, and
externs cannot terminate in `.ioFree`, so their StepFR cases are vacuous
regardless of `regime.bound`.

#### What was removed

- `Regime.bound` field from the `Regime` struct
- `Regime.lookup?` bound guard (`if k < R.bound then ... else none`)
- `regimeBounded` predicate, `predTagsBoundedInCtx` predicate, `wfRegimePartial`
- Bound-equality conjunct from `Regime.monotoneStep` (3 -> 2 conjuncts)
- Bound conjunct from `regimeConsistentWithCtx` (pair -> plain Prop)
- Bound conjunct from `regimeConsistentWithCtxMasked` (pair -> plain Prop)
- Bound conjunct from `wfRegime` (3 -> 2 conjuncts)
- `regimeBounded_of_monotoneStep`, `joinTypeResults_regime_bound_le_head` lemmas
- All `k < bound` / `k >= bound` case splits in mode-3 ite proofs
- Bound premises from `FaultRobustnessSpec` and `FaultRobustnessSpec_ioFree`

This eliminated the artificial `k < bound` / `k >= bound` split that was the
main obstacle in mode-3 transport proofs.

### 3.5. Longer-Term Direction

The longer-term direction remains:

- keep the invariant from PR #133;
- keep the clean/poisoned condition split in `stepFR_ite_mode3`;
- the `k >= bound` subcase is now moot (§3.4 Route 1 executed: `regime.bound`
  removed), so the proof simplifies to standard two-run IH everywhere.

Within that direction, the remaining work is local to `StepFRIte.lean`.

### 3.6. Proof Strategy For The Remaining Mode-3 Bodies

For `stepFRSingleRun_ite_mode3_maskedReg`:

- treat it as a helper lemma, not as evidence about the invariant;
- use the fact that its theorem already assumes `ctx.pc = true`;
- focus on taken-branch IH application and masked-regime transport.

For `stepFR_ite_mode3`:

- split first on `res1.qualType.poison`.

Poisoned-condition branch:

- conclude `branchPc = true`;
- conclude the final result poison is `true`;
- derive `res.qualType.pred = Predicate.noPred` using the existing
  `typecheckIf_pred_noPred` lemma;
- conclude `resultAgreesIfClean` is vacuous using
  `resultAgreesIfClean_of_poison_noPred`;
- then split on the four runtime branch combinations.

  The regime insert is always visible (no `k >= bound` obstruction since
  `regime.bound` was removed in §3.4), so same-branch cases can use the
  ordinary two-run IH on `e2` / `e3`.

  In the mixed-branch poisoned-condition cases, the natural route is masked or
  single-run reasoning, since `branchPc = true` makes those tools applicable.

Clean-condition branch:

- preserve the invariant across typing `e1`;
- use `res1.qualType.etyp = bool` plus `res1.qualType.poison = false` to force
  `res1.qualType.pred = Predicate.noPred`;
- conclude `res1` is `qtypCleanUnder`;
- apply `resultAgreesIfClean` on `e1` to obtain `b₀ = b₁`;
- eliminate the mixed-branch cases as impossible;
- handle only the same-branch cases.

  The regime insert is always visible (no bound obstruction), so the ordinary
  two-run IH on the branch context applies directly.

For the same-branch cases, establishing
`predOnlyOnPoisonedNonRefCtx` for `ctxTrue` / `ctxFalse` should be routine:
this is already handled elsewhere in the codebase by `simpa` from the incoming
`hinv`.

For the mixed-branch cases, choose one of two routes explicitly:

- either prove and reuse `stepFRSingleRun_ite_mode3_maskedReg` as the helper;
- or call `singleIH` directly on the taken branch contexts and avoid depending
  on the masked wrapper.

The transport obligations in these cases should follow the same patterns as the
existing mode-4 proof infrastructure.

### 3.7. Optional Cleanup After Mode 3 Closes

Once both mode-3 `sorry`s are gone:

1. Decide whether the proof stack should continue to expose the broad invariant
   `predOnlyOnPoisonedNonRefCtx`, or whether the local clean/poisoned condition
   split should simply remain the mode-3 proof interface.
2. If repeated transport code emerges across mode 3 and mode 4, extract shared
   helpers rather than leaving the structure duplicated.

### 3.8. Exit Criteria

This line of work is complete when:

- `stepFRSingleRun_ite_mode3_maskedReg` is proved;
- `stepFR_ite_mode3` is proved;
- no temporary axioms are needed;
- the project builds cleanly;
- the documentation reflects the merged invariant work rather than the old
  pre-merge validation plan.

---

## 4. History

### 4.1. Axiom validation experiment (discarded)

**Branch:** `last2`, stash `Snapshot backup 2026-03-26 14:28:10`
(138 insertions in `StepFRIte.lean`; not committed).

**What we tried.**  Before PR #133 landed, we tested whether a targeted
axiom could close the mode-3 agreement argument.  We added a global
`axiom matchGuard_mode3_condition_poisoned` stating:

> If `matchGuard` succeeds with tag `k`, and `regime.lookup? k = none`,
> and the condition typechecks to `res1`, then `res1.qualType.poison = true`.

We then threaded `singleIH` and `htc` into `stepFR_ite_mode3`, derived
`hp1 = true → branchPc = true → hresPoison = true → hpred = noPred`,
and closed `resultAgreesIfClean` with `resultAgreesIfClean_of_poison_noPred`.
The four-case branch split was laid out with sorrys for transport.

**What it validated.**  All the axiom-dependent derivations compiled.  The
chain `hp1 → branchPc = true → resultAgreesIfClean vacuous` worked
exactly as hypothesised, confirming that poisoned-condition is indeed the
right fact for the vacuous-agreement half of mode 3.  The remaining
sorrys were purely mode-4-analogous join transport — nothing
axiom-specific.

**Why it was discarded.**  When we later attempted to replace the axiom
with a real theorem (the "bridge theorem"
`matchGuard_mode3_condition_poisoned_from_inv`), we discovered a
counterexample: the axiom is **false** for pathological predicate bodies.
A predicate body such as `let y = x + 1 in true` passes the `usesArg`
syntactic check (the carrier `x` appears in the bound expression) but
does not propagate the carrier's poison into the result (the body always
returns `true` with `poison = ctx.pc`).  Concretely, if `ctx.pc = false`
and `x` is poisoned, `typecheckExpr` on this expression gives
`res1.qualType.poison = false`.

**What it taught us.**  The axiom's *consequence* — vacuous agreement
when the condition is poisoned — is sound.  It is the axiom's
*hypothesis* that is too strong: the condition is not *always* poisoned
in mode 3.  This led directly to the current proof strategy: case-split
on `res1.qualType.poison` instead of asserting it is `true`.  In the
`poison = true` case the original vacuous-agreement argument applies
unchanged; in the `poison = false` case the invariant forces
`pred = noPred`, so the condition is clean, both runs agree on the
boolean, and the mixed-branch cases are impossible.  The split is
strictly more general than the axiom and handles all predicate bodies
correctly.

### 4.2. Counterexample showing mode-3 de-poisoning is unsound

**Source:** `issue-128-rebase-invariant` branch retrospective (commits
a0eb5d7–7860bfa of this document).

This counterexample predates the merged invariant from PR #133.  It is kept
here because it explains why the older mode-3 design was unsound and why the
proof work pivoted in §4.5; it is not reproducible once the invariant is
assumed.

**The counterexample.**  Two variables share guard tag `0`:

- `x`: clean `bool`, `guardClosure 0 "a" a []` (tag+predicate)
- `y`: dirty `int`, `guardOnly 0` (tag-only)

Expression: `if x then y else 0`.  Initial `pc = false`, regime
`bound = 1`, empty map — so `R.lookup? 0 = none`, exactly mode 3.

`matchGuard` matches `x` (it skips tag-only predicates).  Mode 3 fires.  In
the true branch, `tagEnv[0] = true` causes `typecheckVar` to de-poison `y`
to `⟨int, branchPc, noPred⟩`.  Since `x` is clean, `p1 = false`,
`branchPc = false`, and the result is typed clean.

Two runs with `x = true` (clean, must agree) and `y = 1` vs `y = 2` (dirty,
may differ) both take the true branch and return different values for a
clean-typed result — contradicting `StepFR`.

**What it shows.** Mode 3 de-poisons by tag, not by owner.  A check on `x`
causes mode 3 to de-poison `y`, whose content may differ across runs.  No
existing `main` premise prevents this because `agreeOnClean` is vacuous at
tag `k` when `R.lookup? k = none`.

**Follow-up stress case.**  A same-type variant with `x` clean int
`guardClosure 0 "a" (a == a) []` and `z` dirty int same guard, expression
`if (x == x) then z else 0`, demonstrates the same leak even when both
carriers share the exact closure.

This counterexample is what motivated both the coherence-invariant approach
(§4.3) and, later, the simpler "only poisoned non-ref values carry
predicates" invariant (§4.5).

### 4.3. Coherence-invariant approach (abandoned)

**Source:** `issue-128-rebase-invariant` branch; documented in versions
4280a0d–7860bfa of this document.

**Idea.** Preserve mode-3 typing power by adding a deep semantic
invariant:

> For any fixed runtime state, if two live carriers have the same exact
> tag+predicate combination (`guardClosure k arg body cap`), then their
> runtime values are equal.

Tag-only carriers would be covered separately: for each `guardOnly k`,
there must exist a descriptor `d` with `tm.lookup k = some d` such that
the carrier's value equals the canonical witness `canon k d`.

The witness must be **shared across both runs** (per-run existential
witnesses are insufficient — see §4.4 item 8).

**Why it was abandoned.**

- Engineering cost was very high: new deep predicate in
  `RegimeConsistency.lean`, new premise/conclusion in `StepFR` affecting
  every case proof, preservation proofs for every evaluation rule.
- Structural equality for closures is brittle: semantically "the same guard"
  created at different program points often compares unequal because the
  captured environment snapshots differ.
- The companion same-tag discipline (downgrade structurally-different
  closures with the same tag to `guardOnly`) fires often in practice,
  losing future `matchGuard` ability.
- Separate deep facts do not compose after joins (see §4.4 item 6).
- Risk that the invariant is unprovable if the type system does not actually
  enforce the required same-tag discipline.
- The abandoned branch partially proved a canonical single-run theorem but
  never completed the two-run proof.

### 4.4. Dead ends catalog

These approaches consumed significant time and should not be retried.

1. **`predTagsBoundedInCtx` preservation is FALSE.**
   The invariant "all guard tags in varEnv/memEnv lie below `regime.bound`"
   fails because closure application can expose deep captured tags and later
   operations (e.g., `newRef`) can reify them into top-level memory.  The
   concrete obstruction: start with `bound = 0`, keep a function with
   `guardOnly 5` in its capture, apply it, then `newRef` the result — memory
   now has tag 5 but bound is still 0.

2. **Bumping `regime.bound` in mode 3.**
   Raising the bound so the `regime.map` insert is always visible would
   simplify the `k ≥ bound` story, but it breaks the
   `Regime.monotoneStep` invariant (which requires equal bounds) and is too
   invasive for the surrounding proof infrastructure.

3. **Strengthening `locsRegime.guardOnly_ok`.**
   Requiring realization evidence for `guardOnly` cells collides with the
   two-run joined-memory setup: joined `memEnv` can mention cells from a
   branch not taken at runtime, making the strengthened condition unsatisfiable.

4. **`guardOnlyTagsInTagMeaning` bridge predicate.**
   A predicate saying every `guardOnly k` has backing `tm.lookup k = some d`
   only relocates the gap — it is not derivable from the existing `main`
   premises.

5. **Extending `wfTagMeaningCtx` to cover tag-only entries.**
   The existing `wfTagMeaningCtx` is effectively vacuous for `guardOnly`.
   Adding coverage would require a deep restructuring not justified by the
   mode-3 problem alone.

6. **Separate deep facts do not compose after joins.**
   After `joinETyps`, the same closure shape may be represented by multiple
   `FnTClosure.regular` entries with different captured environments.
   Separately-produced deep properties can choose different members and fail
   to line up.  The abandoned branch only made progress once regime and
   coherence facts were bundled into a single combined deep property.

7. **Projection from canonical single-run into old single-run.**
   The canonical single-run theorem needed stronger inputs (per-state
   coherence evidence).  The old `singleIH` is universally quantified over
   arbitrary states and cannot accept those stronger inputs.

8. **Per-run coherence without a shared witness.**
   Per-run existential witnesses `canon₀`, `canon₁` with no cross-run
   relation directly fail in the two-run setting — they allow
   `canon₀ k d ≠ canon₁ k d`.

9. **Naive transfer principle.**
   Shared tags are not type-indexed.  The same tag can link carriers of
   different types (e.g., `int` and `bool`), so no general value-transport
   principle exists.

10. **Per-owner de-poisoning (restrict to matched owner only).**
    This would eliminate the linked-value mechanism that tag-only predicates
    were designed for.  The core use case — checking a status value to
    de-poison linked data via a shared tag — would no longer work.  This
    removes a fundamental language capability.

11. **Output-side deep-property fan-out.**
    Pushing the full deep property (coherence + regime + typing) into every
    output tuple caused a large proof explosion and did not immediately help
    the active mode-3 work.

### 4.5. Pivot to the "only poisoned non-ref values carry predicates" invariant

**Source:** commit 306a760 ("new approach") of this document.

**Key insight.**  Instead of strengthening the proof interfaces to justify
mode-3 de-poisoning for all same-tag carriers (the coherence-invariant
approach), we observed that under a simpler discipline — only poisoned
non-reference values carry predicates — the counterexample from §4.2
cannot arise at all.

In the counterexample, `x` is a **clean** boolean with a `guardClosure`
predicate.  The invariant says non-reference values with predicates must be
poisoned.  So `x.poison = true`, which forces `p1 = true` and
`branchPc = true`.  Then everything inside the branch stays poisoned, and
the result is poisoned with `pred = noPred`.  `resultAgreesIfClean` is
vacuous.

This was a dramatically simpler repair than the coherence-invariant route:
define the invariant, prove preservation across all typing rules, enforce
in the spec constructors, thread through StepFR.  PR #133 implemented
this and landed on 2026-03-26.

**Limitation discovered later.**  The invariant ensures the carrier is
poisoned, but a poisoned carrier does not always force the *condition
expression* to be poisoned (see §4.1 — `usesArg` is syntactic, not
semantic).  The final proof strategy avoids this gap entirely by
case-splitting on the condition's poison rather than asserting it is always
true.
