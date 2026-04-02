# Extern Functions: Remaining Axioms on `new-iofree`

## Purpose

This note records the current extern-related proof surface on the `new-iofree`
branch, explains why the remaining axioms exist, and classifies each one as:

- a **foundational extern contract** obligation that is not expected to be
  provable from the current typechecker alone, or
- a **provable proof obligation** that should disappear once the right
  infrastructure or theorem shape is in place.

It is modeled on the older `iofree` branch document, but reflects the current
state of this branch rather than the earlier migration attempt.

## Current Status

As of the current repository state:

- `lake build` succeeds
- `LeanProofs/` contains **0** `sorry`
- there are **11 explicit axiom declarations**
  - 10 in `LeanProofs/StepFR.lean`
  - 1 in `LeanProofs/TypeSafety.lean`

This is a substantial improvement over the old `iofree` branch, which still had
two `sorry`s in `StepFRIte.lean` plus a larger extern axiom surface. In
particular, the old `mode3` `if` proof debt is gone entirely on `new-iofree`;
the remaining gaps are isolated to the extern contract.

The current 11 axioms are:

| Axiom | File | Current assessment |
|------|------|--------------------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | `StepFR.lean` | Likely provable, but only after substantial effect-loop infrastructure plus semantic/structural separation |
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | `StepFR.lean` | Foundational semantic extern contract |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | `StepFR.lean` | Foundational semantic extern contract |
| `applyFnTClosure_extern_ok_lookup_origin` | `StepFR.lean` | Likely provable, but requires new effect-loop provenance reasoning |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | `StepFR.lean` | Likely provable or vacuous from LocSet allocation invariant |
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | `StepFR.lean` | Likely provable from bounded-tags invariant |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | `StepFR.lean` | Likely provable from bounded-tags invariant |
| `typecheckExternVal_QTypRespectsTagMeaning_axiom` | `StepFR.lean` | Foundational semantic extern contract (split from bundled axiom) |
| `typecheckExternVal_preserves_lookup_origin_axiom` | `StepFR.lean` | False as written for `ref int`; must be restated before proof work continues |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | `StepFR.lean` | Likely provable from bounded-tags invariant |
| `applyFnTClosure_extern_wfTypeResult` | `TypeSafety.lean` | Likely provable from LocSet allocation invariant |

## Why Extern Obligations Remain

Raw extern syntax is still vacuous on the **runtime** side of fault-robustness:

- `Expr.externVal`
- `Expr.externFn`
- `Expr.externPfn`

all evaluate to runtime errors in `LeanPoison/BigStep.lean`.

So the top-level FR theorem still treats raw extern expressions as unreachable
runtime cases. The remaining proof obligations come from the **typing**
machinery instead:

1. `typecheckExternVal`
2. `applyFnTClosure` on `FnTClosure.extern`
3. `applyPFnTClosure` on `PFnTClosure.extern`

These functions resolve symbolic extern predicates, allocate fresh tags, thread
captured environments, and in the impure extern case update memory through the
effects loop. Those typing-side artifacts must satisfy the same internal proof
invariants that regular closures satisfy by induction on their bodies.

## Comparison With `iofree`

The older `iofree` branch documented 12 extern-related axioms:

- 11 in `StepFR.lean`
- 1 in `TypeSafety.lean`

The current branch is down to 11. In particular:

- the old `applyPFnTClosure_extern_ok_lookup_origin` axiom is no longer present
- all old non-extern `sorry`s have been eliminated
- the two old `StepFRIte.lean` `mode3` `sorry`s are gone entirely

So the remaining work is now concentrated on the true extern contract and the
infrastructure around fresh tags, effect loops, and captured LocSets.

## Grouped Analysis

### Group 1: Foundational semantic extern contract

These are the obligations that most directly encode the FFI boundary.

| Axiom | Status | Why |
|------|--------|-----|
| `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` | Foundational | Extern effect/return predicates may introduce `guardClosure` descriptors that are not determined by the ordinary inductive proof on expressions |
| `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning` | Foundational | Same issue for pure extern closures |
| `typecheckExternVal_preserves_wfTagMeaningCtx_axiom` | Partly foundational | Its `QTypRespectsTagMeaning` conjunct is foundational; its `wfTagMeaningCtx` conjunct should be split off and proved separately |

#### Interpretation

The irreducible semantic content is:

- when extern typing resolves a `SyntaxPredicate.guardClosure idx arg body`,
  the resulting concrete tag must map to the right `GuardDesc` in `tm`
- this is a statement about the intended meaning of the extern spec, not about
  a structural property of the typechecker alone

This is the same basic conclusion as on `iofree`: the deepest likely permanent
axiom floor is the tag-meaning contract, not the larger current 11-axiom set.

#### Suggested direction

- split `typecheckExternVal_preserves_wfTagMeaningCtx_axiom` into:
  - a provable `wfTagMeaningCtx` lemma
  - a separate `QTypRespectsTagMeaning` axiom
- keep the three semantic tag-meaning obligations as the candidate permanent
  extern contract unless later work finds a cleaner syntax-level formulation

#### Useful hints from `iofree`

- For `applyFnTClosure_extern_ok_QTypRespectsTagMeaning` and
  `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`, the old branch does not
  contain proofs, but it does justify the right internal interface:
  `iofree:LeanProofs/RegimeConsistency.lean` uses
  `QTypRespectsTagMeaning_fn_regular` and `QTypRespectsTagMeaning_pfn_regular`
  as the regular-case bridge, and `iofree:doc/extern-axioms.md` explicitly
  argues that the extern contract should reuse that same bridge rather than
  invent a different extern-only notion.
- Those ideas are already partially ported and strengthened on the current
  branch: `LeanProofs/RegimeConsistency.lean` now contains not only the regular
  helpers `QTypRespectsTagMeaning_fn_regular` and
  `QTypRespectsTagMeaning_pfn_regular`, but also the structural extern helpers
  `QTypRespectsTagMeaning_fn_extern` and `QTypRespectsTagMeaning_pfn_extern`.
  These do not discharge the remaining semantic extern axioms, but they show
  that the captured-environment part of the argument is already available on
  this branch.
- For `typecheckExternVal_preserves_wfTagMeaningCtx_axiom`, the old branch is
  especially useful because `iofree:doc/extern-axioms.md` already notes that
  this axiom is bundled too coarsely. The structural ingredient for splitting
  off the first conjunct is already visible in
  `iofree:LeanProofs/RegimeConsistency.lean` via
  `EnvRespectsTagMeaning_updateMemEnv`.

### Group 2: Tag freshness via bounded-tags invariant

These axioms concern the fact that newly allocated extern tags should be absent
from `tagEnv` at the point they are introduced.

| Axiom | Status | Likely proof route |
|------|--------|--------------------|
| `applyFnTClosure_extern_ok_guardClosure_tag_absent` | Provable | Bounded-tags invariant on `tagEnv` plus local fresh-tag allocation facts |
| `applyPFnTClosure_extern_ok_guardClosure_tag_absent` | Provable | Same |
| `typecheckExternVal_guardClosure_pred_implies_tag_absent` | Provable | Same |

#### Why these should be provable

After the `TagIndex` refactor:

- extern declarations carry symbolic indices, not concrete tags
- `collectAndAllocExternTags` allocates fresh concrete tags from `nextTag`
- `resolveSyntaxPred` instantiates those fresh tags locally

So freshness is no longer a semantic extern promise. It should follow from a
typechecker invariant of the form:

`forall k v, tagEnv.get? k = some v -> k < nextTag`

Once that invariant is threaded through the relevant typing lemmas, the three
freshness axioms should collapse.

#### Suggested direction

- formalize the bounded-tags invariant for `TypeContext`
- prove it is preserved by all typing rules
- then discharge the three freshness axioms directly from:
  - allocation from `nextTag`
  - preservation of `tagEnv`

#### Useful hints from `iofree`

- The old branch already introduced the right intermediate invariant:
  `predTagsBoundedInCtx` in `iofree:LeanProofs/StepFR.lean`. Its concrete
  definition is tied to the old bounded-regime encoding and should not be
  copied literally, but it captures the same intended obligation: all top-level
  guard tags already present in the typing context lie below the fresh-tag
  supply.
- The bridge from a syntactic `matchGuard` result to a bounded tag is spelled
  out in `iofree:LeanProofs/StepFRIte.lean` as `matchGuard_tag_in_bound`. The
  exact theorem shape is old-architecture-specific, but it shows how the
  bounded-tags invariant was meant to be consumed by FR proofs.
- On the allocation side, `iofree:LeanProofs/TypeSafety.lean` already has
  `collectAndAllocExternTags_nextTag_ge` and `typecheckExternVal_nextTag_mono`.
  These are useful templates for the fresh-tag monotonicity part of the
  argument.

### Group 3: Impure extern effect-loop infrastructure

These are specific to `FnTClosure.extern`, whose effects loop updates memory.

| Axiom | Status | Likely proof route |
|------|--------|--------------------|
| `applyFnTClosure_extern_ok_wfTagMeaningCtx` | Likely provable | Requires hard effect-loop infrastructure; splitting semantic vs structural pieces is necessary but not sufficient |
| `applyFnTClosure_extern_ok_lookup_origin` | Likely provable | New effect-loop provenance lemmas, probably with stronger intermediate hypotheses |
| `applyFnTClosure_extern_wfTypeResult` | Likely provable | LocSet allocation invariant for captured reference types |
| `applyFnTClosure_extern_ok_fresh_loc_not_clean` | Likely provable / vacuous | Follows once newly written locations are shown already allocated or otherwise controlled by the effect-loop invariant |

#### `wfTagMeaningCtx`

`applyFnTClosure_extern_ok_wfTagMeaningCtx` should not be treated as a
foundational axiom by itself. However, it is also not a "quick split and simp"
obligation. The semantic split is only the first step. The real work is the
impure extern effects loop: one must reason through the resolved effect
predicates written by `LocSet.fold ... updateMemEnv`, then lift those writes
through the tag-meaning infrastructure. Once one assumes the relevant
`QTypRespectsTagMeaning` facts for those effect predicates, the remaining proof
should be structural:

- resolve predicate
- build stored `QTyp`
- update memory
- lift tag-meaning preservation through `updateMemEnv`

So this axiom is best viewed as a bundled proof obligation, not a permanent
contract item.

Useful `iofree` references:

- `iofree:LeanProofs/StepFR.lean` contains the structural extern lemmas
  `applyFnTClosure_extern_ok_tagEnv_eq` and
  `applyFnTClosure_extern_ok_regime_eq`, followed by
  `applyFnTClosure_extern_ok_regimeConsistentWithCtxMasked`. These do not prove
  `wfTagMeaningCtx`, but they isolate the purely structural part cleanly.
- The app-side consumers `applyFnTClosure_ok_wfTagMeaningCtx` and
  `applyFnTClosure_ok_QTypRespectsTagMeaning` in
  `iofree:LeanProofs/StepFRApp.lean` show the intended decomposition:
  structural equalities + semantic tag-meaning fact.

#### `wfTypeResult`

`applyFnTClosure_extern_wfTypeResult` remains an axiom because the current proof
infrastructure does not express the needed link between:

- `LocSet`s appearing inside captured reference types, and
- actual allocated memory locations already present in `result2.memEnv'`

This is the missing **LocSet allocation invariant**.

Useful `iofree` references:

- `iofree:LeanProofs/TypeSafety.lean` already had the right local helper lemmas
  around LocSet folds:
  `locset_fold_max_ge_init`, `locset_fold_max_succ_ge_of_mem`,
  and `locset_fold_updateMemEnv_preserves_contains'` /
  `locset_fold_updateMemEnv_preserves_contains`.
- Those lemmas do not solve the whole axiom, but they show the expected local
  shape of the proof once the missing global LocSet-allocation invariant is
  available.

#### `fresh_loc_not_clean`

This one should probably not be attacked first. If the LocSet allocation
invariant shows that effect-loop writes only touch already-allocated locations,
then the "fresh location" premise becomes empty for effect writes, and the axiom
collapses as a consequence of the same infrastructure work used for
`applyFnTClosure_extern_wfTypeResult`.

Useful `iofree` references:

- The old branch already had the regular-case template
  `applyFnTClosure_fresh_lookup_not_clean_of_p1p_true` in
  `iofree:LeanProofs/StepFRApp.lean`.
- `iofree:doc/extern-axioms.md` also already observed that the extern case
  should become vacuous if the LocSet allocation invariant shows that all
  effect-loop targets were already present in the input memory environment.

### Group 4: Provenance obligations

| Axiom | Status | Assessment |
|------|--------|------------|
| `applyFnTClosure_extern_ok_lookup_origin` | Probably provable | Hardest remaining proof obligation on the `FnTClosure.extern` side |
| `typecheckExternVal_preserves_lookup_origin_axiom` | False as written | Current implementation gives a fresh-`ref int` counterexample |

#### `applyFnTClosure_extern_ok_lookup_origin`

This is still a reasonable target for proof, but it is genuinely hard because
the effects loop can update memory at multiple reference targets collected from
the captured environment. The proof likely needs:

- a clear "all writes come from these effect targets" lemma
- a way to relate each target `LocSet` back to already-originating memory
- a provenance statement phrased at the right intermediate level

This is better treated as a dedicated effect-loop proof task after the simpler
invariants are in place.

Useful `iofree` references:

- `iofree:doc/extern-axioms.md` already classified provenance as mostly a
  theorem-shape / proof-API issue rather than a semantic extern assumption.
- The old branch also contained the now-removed pure-extern axiom
  `applyPFnTClosure_extern_ok_lookup_origin` in `iofree:LeanProofs/StepFR.lean`.
  The current branch no longer needs that separate axiom because the structural
  equality lemmas, especially `applyPFnTClosure_extern_memEnv_eq`, are already
  enough to absorb the pure case. That is evidence that further theorem-shape
  cleanup can reduce the impure provenance surface as well.

#### `typecheckExternVal_preserves_lookup_origin_axiom`

**RESTATED**: This axiom now carries a pre-existence hypothesis
`(hpre : ctx.memEnv.contains l)` that restricts the conclusion to locations
already present in the input memory. Fresh locations allocated by
`surfaceSpecToQTyp` for `ref int` extern values are exempt.

The restatement required cascading changes through:
- `typecheckExpr_lookup_origin_of_pc_true_split` (conclusion + all ~28 IH calls)
- `typecheckExpr_lookup_poison_origin_of_pc_true`
- `typecheckExpr_lookup_guard_origin_of_pc_true`
- `typecheckExpr_clean_lookup_origin_of_pc_true`
- ~18 consumer sites across FR proof files

The `typecheckExpr_lookup_clean_back_of_pc_true` wrapper was unchanged (it
already required `ctx.memEnv.lookup l = some qt_in`).

**Exposed sorry sites**: The restatement revealed 6 `sorry` in 3 declarations
that previously relied on the false axiom's contrapositive (fresh locations
can't be clean under `pc = true`), which is also false for `externVal ref int`:
- `StepFRIte.lean`: 4 sorry in `hclean_back_to_res1` (no `htc1` available
  to derive monotonicity for the contains precondition)
- `StepFRAssign.lean`: 1 sorry in `assign_final_clean_preservation` (same issue)
- `StepFRApp.lean`: 1 sorry in fresh-location contradiction branch (the location
  provably does NOT pre-exist, so the old proof-by-contradiction via the
  lemma no longer works)

These are genuine proof gaps that were hidden by the false axiom, not new
bugs introduced by the restatement.

Useful `iofree` references:

- The old branch did not prove this axiom either; it appears there with the
  same high-level statement in `iofree:LeanProofs/StepFR.lean`.
- `iofree:doc/extern-axioms.md` already warned that provenance obligations are
  partly theorem-shape problems. So the old branch does not provide a missing
  proof here, but it does reinforce the idea that the current statement should
  be restated before more effort is spent trying to prove it as-is.

## Suggested Way Forward

The highest-value next steps are:

1. **Restate `typecheckExternVal_preserves_lookup_origin_axiom` first.**
   In the current implementation it appears false as written for `ref int`
   extern values, so proving around the current statement would be wasted
   effort.

2. **Split `typecheckExternVal_preserves_wfTagMeaningCtx_axiom`.**
   This should reduce the axiom surface even before the harder invariants are
   developed.

3. **Prove the bounded-tags invariant.**
   This should remove the three freshness axioms.

4. **Prove the LocSet allocation invariant.**
   This should attack `applyFnTClosure_extern_wfTypeResult` directly and likely
   also collapse `applyFnTClosure_extern_ok_fresh_loc_not_clean`.

5. **Return to impure extern provenance.**
   With the easier infrastructure in place, the remaining hard target becomes
   `applyFnTClosure_extern_ok_lookup_origin`.

## Expected End State

The most plausible long-term outcome is:

- the current 11 axioms do **not** represent the true minimum
- the likely permanent floor is the semantic tag-meaning contract:
  - `applyFnTClosure_extern_ok_QTypRespectsTagMeaning`
  - `applyPFnTClosure_extern_ok_QTypRespectsTagMeaning`
  - a split `typecheckExternVal` tag-meaning axiom

Everything else should be treated as either:

- a proof-engineering obligation
- a missing invariant
- or a theorem-shape issue that still needs to be restated cleanly

In particular, the current branch is already in a much better state than the
older `iofree` attempt: the non-extern proof stack is complete again, and the
remaining surface is explicitly isolated as an extern contract rather than being
mixed with unrelated `sorry` debt.
