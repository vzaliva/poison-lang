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

