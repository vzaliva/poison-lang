# `ExternTypingAssumptions.guardProvenance`: Bug Diagnosis and Fix

This note follows up on Open Question #2 of `doc/ffi-axioms.md`:

> Revisit the shape of `ExternTypingAssumptions.guardProvenance`. It needs
> either a derivation from more structural extern-call facts or an explicitly
> scoped trust story parallel to the predicate-law registry evidence.

The conclusion of the analysis is sharper than the question suggests: the
axiom exists because of an **implementation bug** in the typechecker's extern
effect summary, not because of a deep semantic gap. The fix is to align
`applyExternEffect` with the existing assignment-typing rule under poisoned
`pc`, after which `guardProvenance` becomes structurally provable and the
axiom can be removed outright.

## Status of the question

The current state of the code:

- `ExternTypingAssumptions.guardProvenance` lives at
  `LeanProofs/ExternTypingAssumptions.lean:596-602` exactly as
  `doc/ffi-axioms.md` lines 411-422 describe.
- It is consumed at **exactly one site** —
  `LeanProofs/StepFR.lean:12496`, inside the `extern` branch of the impure-call
  inversion in `typecheckExpr_lookup_origin_of_pc_true_split`.
- Its structural sibling `applyFnTClosure_extern_ok_memEnv_poison_origin`
  (`StepFR.lean:5926`) handles the poison side without an axiom (called at
  `StepFR.lean:12258`).
- Recent history: commit `2cbc2ea` "prove extern poison memEnv origin
  structurally", then `daa44d4` "shrink extern provenance axiom to guard-only",
  then `5cc34ee` "Retire the tagsoundness-axiom design doc; refresh
  ffi-axioms.md". So the open question is the **most recent unresolved
  residue** of the axiom-shrinking effort.

## The proof obligation

The lemma `typecheckExpr_lookup_origin_of_pc_true_split` does a backward
trace: given a "clean" cell at location `l` in the **post**-typecheck memEnv
(under `pc = true`), find a clean cell at the same location in the
**pre**-typecheck memEnv. "Clean" splits two ways:

1. **Poison-clean**: `qt.poison = false`.
2. **Guard-clean**: `qtypGuardTag qt = some k ∧ regime.lookup? k = some true ∧
   qt.etyp.isFunctionType = false`.

Both cases need the same backward trace, but only the poison side is
currently structural.

## Why poison is structural and guards are not

Under `pc = true`, every cell that `applyExternEffect` writes gets
`storedQt.poison = joinPoison true _ = true` (`Typecheck.lean:1300`). So an
*unpoisoned* post-cell was provably **not** overwritten — the lookup must
fall through to the pre-cell. That's the operational invariant the structural
poison proof rides on (`StepFR.lean:5859-5872`).

The guard side has no such forcing identity. `applyExternEffect` writes
`storedQt.pred = resolvedPred`, which can be `Predicate.guardClosure k arg
pbody cap` or `Predicate.guardOnly k` whenever `effect.pred` is a
`guardClosure idx ...` or `guardOnly idx` and the tag mapping resolves
`idx ↦ k`. So a written cell *can* legitimately carry a guard tag — even
under poisoned control flow. The axiom papers over this.

## The bug

Compare `applyExternEffect` (`LeanPoison/Typecheck.lean:1289-1303`) with the
assignment-typing rule (`LeanPoison/Typecheck.lean:1186`):

- **Assignment under `pc = true`** already erases the predicate before
  storing. A poisoned-control assignment cannot install a guard.
- **Extern effect under `pc = true`** installs `resolvedPred` regardless of
  `pc`. A poisoned-control extern call *can* install a guard.

That asymmetry is the bug. There is no design rationale for an extern call to
have stronger predicate-installation power than an ordinary assignment under
the same control conditions. Both are memory writes; both should treat
poisoned control as provenance-destroying. The typechecker just got it wrong
for externs.

This is the root cause of `guardProvenance`. The axiom exists not because
some deep semantic invariant is hard to express — it exists because extern
effect summaries failed to apply the same predicate-erasure normalization
that assignment already applies.

## The fix

Tighten `applyExternEffect` to mirror assignment under poisoned `pc`. The
conservative formulation gates strictly on `pc`, *not* on the joined poison
of the stored qt:

```lean
let storedPred := if pc then Predicate.noPred else effectQt.pred
let storedQt := ⟨effectQt.etyp, joinPoison pc effectQt.poison, storedPred⟩
```

Why gate on `pc` rather than on the joined poison: erasing the predicate
"whenever the stored poison is `true`" would also erase ordinary
`poisoned {guard}` summaries written under clean control flow, which is the
core de-poisoning mechanism — those summaries must keep their guard so a
later masked-regime check can re-clean them. Only control-flow poisoning
(`pc = true`) should trigger erasure, just as for assignment.

After this change, no extern effect can install a guard tag under poisoned
control flow. The structural argument then closes the axiom:

- a cell written under `pc = true` is poisoned and guard-tag-less;
- so any post-cell that is guard-clean must have avoided every write;
- so its lookup falls through to the pre-state. ∎

## The proof plan

The structural proof of `guardProvenance` after the fix decomposes naturally
along the shape of `effects` in the extern call. Use this decomposition both
to organize the proof and to verify that no case is missed:

1. **No memory effects (`effects = []`).** `applyExternEffect` is never
   called. `r.memEnv' = result2.memEnv'`, so the trace is the identity
   composed with the IH. One-liner.

2. **Memory effects, but every `effect.pred` is `noPred`.** Already
   structural even *before* the fix: the stored qt has no guard tag, so any
   guard-clean post-cell must have come from the pre-state. The proof is the
   loop-scan analogue of `applyFnTClosure_extern_ok_memEnv_poison_origin`,
   substituting "stored qt has no guard tag" for "stored qt is poisoned."

3. **Memory effects with `guardOnly` or `guardClosure` predicates.** *This is
   the case the bug fix unblocks.* Before the fix, the stored qt could carry
   a fresh active guard tag and break the backward trace; after the fix, the
   stored qt's predicate is forced to `noPred` under `pc = true`, collapsing
   this case into bucket 2.

   Two relevant facts about why bucket 3 cannot be merged into bucket 2
   without the fix:

   - `SyntaxPredicate.guardOnly idx` resolves to `Predicate.guardOnly tag`
     (`LeanPoison/Typecheck.lean:850`).
   - `qtypGuardTag` returns `some k` for both `Predicate.guardClosure k _ _ _`
     and `Predicate.guardOnly k` (`LeanProofs/TypeSafety.lean:537-540`).
     `qtypCleanUnder.guard` (`LeanProofs/FaultRobustness.lean:356-363`) is
     purely tag-based and does not require a closure body.

   So `guardOnly` cannot be lumped with `noPred` for cleanness purposes; it
   writes a fresh active guard tag exactly the way `guardClosure` does. Only
   the bug fix collapses both back into the no-guard write case.

After bucket 3 collapses into bucket 2, all three buckets close structurally.
Replace the call to `extTyping.guardProvenance` at `StepFR.lean:12496` with a
structural lemma analogous to `applyFnTClosure_extern_ok_memEnv_poison_origin`,
then delete the `guardProvenance` field from `ExternTypingAssumptions` and
its threading through every consumer.

## Impact

The fix is contained to the typechecker and its proof artifacts. Operational
semantics, the runtime executable path, and end-user `.poison` programs are
unaffected.

### Operational semantics — **no change**

`applyExternEffect` lives in `LeanPoison/Typecheck.lean`, not `BigStep.lean`.
A grep for `applyExternEffect` in `LeanPoison/BigStep.lean` returns nothing;
the operational big-step evaluator does not consume effect predicates at all.
Effect summaries are a typechecker-level concept used to compute the
post-effect `MemoryTypeEnv`, not the runtime memory. So:

- No edits to `LeanPoison/BigStep.lean`.
- No edits to `LeanPoison/Runtime.lean`.
- The interpreter behavior is unchanged on every existing program.

### Typechecker — **localized change**

One function changes — `applyExternEffect`
(`LeanPoison/Typecheck.lean:1289-1303`). The change is the conservative
`if pc` gate on `storedPred`. Two callers pass the result through unchanged
(`Typecheck.lean:1348` for `applyFnTClosureAtCursor`, `Typecheck.lean:1419`
for the parallel pure path) and need no edits.

`applyExternEffect`'s sibling `effectSpecToQTyp` is referenced by proofs
(`StepFR.lean:6984`, `TypeSafety.lean:6964`) but is not itself changed.

### Ott rules / formal spec — **localized update**

The Ott specification has extern-typing rules that mention effects and `pc`
explicitly:

- `poison-lang-spec/poison-lang.ott:1265` — `extern_fn` typing rule.
- `poison-lang-spec/poison-lang.ott:1274` — `extern_pfn` typing rule.
- `poison-lang-spec/poison-lang.ott:1322`, `:1333` — extern-call
  application rules in impure mode.
- `poison-lang-spec/poison-lang.ott:1357`, `:1366` — extern-call
  application rules under both modes.

The effect-storage premise of these rules (or its supporting auxiliary
relation, depending on how effects are formalized in the Ott file) needs the
same `pc`-gated predicate-erasure step. Pattern after the existing
assignment rule, which already handles this correctly.

### Documentation — **narrative update**

`doc/poison-lang-description.tex` describes extern effect semantics in
prose. The narrative needs one consistency edit: under poisoned control flow,
extern effect writes erase predicates, identically to assignment. This is
likely a one-paragraph change; the document already explains assignment's
poisoned-pc behavior, so the edit can reference that section rather than
re-deriving it.

`doc/ffi-axioms.md` Open Question #2 is closed by the bug fix; the
cross-reference to this note is updated accordingly.

### Tests — **golden audit, expected mostly clean**

108 files in `examples/` mention `extern`. The behavior changes only for
programs that:

1. install a guard predicate via an extern *effect* (not via the return
   spec); **and**
2. invoke that extern under poisoned control flow (inside an `if` branch
   whose condition is dirty, or after a poisoned variable assignment, etc.).

Programs that exercise extern guards under *clean* control flow are
unaffected — `pc = false` still installs the predicate. Programs that use
extern effects without guards (effect predicate is `noPred`) are unaffected.

Audit candidates from a quick grep — `examples/sensor-processing.poison`,
`examples/basic-poison-flow1.poison`,
`examples/locset-merge-nested-poison.poison`,
`examples/multiple-poison-sources.fail`, and others that combine extern
calls with poison flow — should be re-run after the typechecker change. Any
golden file that currently shows a guard-clean cell after a poisoned-control
extern call will change to a poisoned cell. That is the bug being fixed; the
new output is the correct output.

### Proof artifacts — **the bulk of the work**

This is the largest piece of the fix in code volume, but each step is local:

- `applyExternEffect_preserves_clean_lookup` and
  `forIn_effects_loop_preserves_clean_lookup` (`StepFR.lean:5834-5919`)
  gain a "stored qt is guard-tag-less under `pc = true`" conclusion alongside
  the existing poison conclusion.
- A new structural lemma
  `applyFnTClosure_extern_ok_memEnv_guard_origin` is added next to the
  existing `applyFnTClosure_extern_ok_memEnv_poison_origin`
  (`StepFR.lean:5926`).
- The call to `extTyping.guardProvenance` at `StepFR.lean:12496` is replaced
  with the new structural lemma.
- The `guardProvenance` field is removed from `ExternTypingAssumptions`
  (`LeanProofs/ExternTypingAssumptions.lean:596-602`), and its threading
  through every consumer is cleaned up. Since `extTyping` is still threaded
  for `externPredSatDelta`, the structural change is just narrowing the
  structure, not deleting the parameter.
- Existing proofs that use `effectSpecToQTyp`'s shape
  (`TypeSafety.lean:6964-6987`, `StepFR.lean:6984-6987`) need a small edit
  to handle the new `if pc` branch. The discharge is mechanical — case-split
  on `pc` and use the existing analysis on each branch.

## Implementation checklist

1. **Typechecker change.** Update `applyExternEffect`
   (`LeanPoison/Typecheck.lean:1289-1303`) to gate predicate installation on
   `pc`, matching the assignment rule at `LeanPoison/Typecheck.lean:1186`.
2. **Spec/Ott update.** Reflect the same gating in
   `poison-lang-spec/poison-lang.ott` and `doc/poison-lang-description.tex`.
   The narrative should say externs treat poisoned control as
   provenance-destroying for memory writes, exactly like assignment.
3. **Test churn.** `examples/` cases that depend on extern-installed guards
   under poisoned `pc` will change behavior. Audit and regenerate
   `.output`/`.fail` golden files where appropriate. Examples that rely on
   guard installation under *clean* control flow are unaffected.
4. **Update existing structural lemmas.** Strengthen
   `applyExternEffect_preserves_clean_lookup` and
   `forIn_effects_loop_preserves_clean_lookup`
   (`StepFR.lean:5834-5919`) to also conclude "stored qt is guard-tag-less
   under `pc = true`."
5. **Replace the axiom call.** At `StepFR.lean:12496`, replace
   `extTyping.guardProvenance` with a new structural lemma — call it
   something like `applyFnTClosure_extern_ok_memEnv_guard_origin`, parallel
   to the existing `applyFnTClosure_extern_ok_memEnv_poison_origin` at
   `StepFR.lean:5926`.
6. **Delete the field.** Remove `guardProvenance` from
   `ExternTypingAssumptions` (`LeanProofs/ExternTypingAssumptions.lean:596-602`)
   and clean up its threading through every caller.
7. **Doc cleanup.** Update `doc/ffi-axioms.md`: Open Question #2 is closed by
   bug fix; the residual story is the `externPredSatDelta` field (Open
   Question #1) plus the broader extern-boundary refactor.

## Relationship to issue #137

[Issue #137](https://github.com/vzaliva/poison-lang/issues/137) asks whether
`--regime` should be allowed to mention tags that have not yet been
allocated by the typechecker. That is a separate language-design question
about regime semantics, and an earlier draft of this note treated #137 as
the gating decision for closing the axiom. With the bug fix in hand it isn't:
once externs respect `pc`-gated predicate erasure, `guardProvenance` becomes
structurally provable regardless of whether regimes can name future tags.
#137 should be resolved on its own merits (regime input validation,
user-facing behavior of `--regime`), not as a prerequisite to closing this
axiom.

## Design note

The asymmetry between the poison and guard sides was *not* an intended deep
design choice; it is an implementation mismatch. Three observations make this
concrete:

- Assignment already treats poisoned control as provenance-destroying
  (`LeanPoison/Typecheck.lean:1186`).
- Extern effect summaries should do the same, since they are also memory
  writes under control flow.
- The current axiom exists because extern effects failed to apply that same
  normalization at the typechecker level.

Once the normalization is restored, the asymmetry between the two cleanness
modes (`poison-clean` and `guard-clean`) closes at its root: under poisoned
`pc` both are forced — poison is forced to `true`, the predicate is forced
to `noPred`. The "merge-up" behavior poison enjoys under `joinPoison true _`
is matched by the predicate side. The structural backward-trace argument
that already works for poison transfers directly to guards.
