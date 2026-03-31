# New `iofree` Migration Plan

## Goal

Create a new branch `new-iofree` from current `main` and reintroduce only the
intended `iofree` feature set:

- remove built-in IO operators from the language
- remove `EvalMode` / old `ioFree` split
- keep the pure evaluator shape
- keep extern declarations and extern typing support
- keep only extern-local FR assumptions as axioms
- preserve all non-extern proofs that are already complete on `main`

This plan deliberately avoids rebasing the current `iofree` branch as-is.

## Recommendation

The easier direction is:

1. start from `main`
2. port the wanted `iofree` changes onto it
3. do not bring the old `mode3` proof path or `R.bound` infrastructure forward

Reason:

- `main` is the clean proof baseline
- current `iofree` mixes desired feature work with an older proof architecture
- the remaining proof gaps on current `iofree` are exactly in the old `mode3`
  path

## Scope And Complexity

This is a substantial manual transplant, not a light rebase.

Verified local scale of `main..iofree`:

- 145 files changed
- 12,482 insertions
- 17,155 deletions

Verified local scale of the proof delta alone under `LeanProofs/`:

- 22 proof files changed
- 10,700 insertions
- 15,942 deletions

Operational consequence:

- this work must be decomposed into small slices
- selective transplant is still the correct strategy
- but the plan should be executed as a staged migration with frequent
  buildable checkpoints, not as one large manual copy operation

## Current Branch Snapshot

### `main`

- locally, `main` has no `sorry`
- locally, `main` has no `axiom`
- `main` contains the newer proof cleanup and no-mode3 work
- `main` is therefore the right semantic and proof baseline

### current `iofree`

- current `iofree` builds with `lake build`
- it still has exactly 2 remaining `sorry`s in `LeanProofs/StepFRIte.lean`
- those two `sorry`s are in:
  - `stepFRSingleRun_ite_mode3_maskedReg`
  - `stepFR_ite_mode3`
- it still has 12 extern-related axioms:
  - 11 in `LeanProofs/StepFR.lean`
  - 1 in `LeanProofs/TypeSafety.lean`
- this is acceptable as an intermediate extern contract
- what is not desirable is the extra old proof infrastructure that surrounds it

## Key Differences Between `main` and current `iofree`

### 1. `Regime.bound` exists on current `iofree`, but was removed on `main`

Current `iofree` changed `Regime` into a structure with:

- `bound : Tag`
- `map : ExtTreeMap Tag Bool`

and made `lookup?` conditional on `k < bound`.

`main` no longer uses this bounded-regime representation. This matters because
many `iofree` proofs were rewritten around:

- `bound` monotonicity
- bounded lookups
- lemmas about tags below or above the bound
- transfer lemmas that exist only to support that representation

This is one of the main reasons not to rebase current `iofree` directly.

### 2. Current `iofree` still carries explicit `mode3`; `main` has moved past it

Current `iofree` still has the `typecheckIf` branch for:

- `matchGuard` succeeds
- `R.lookup? k = none`

and then types both branches under:

- `tagEnv[k := true/false]`
- branch-local `regime.map[k := true/false]`
- joined conservative result

This is the old `mode3` path. It is still live in current `iofree`, and the
remaining `sorry`s are exactly its proof obligations in `StepFRIte.lean`.

`main` has already absorbed the proof cleanup that removed this burden from the
working proof surface. Reintroducing the current `iofree` version would pull the
problem back in.

### 3. `main` is proof-complete; current `iofree` is not

What was verified locally during assessment:

- `main`: no `sorry`, no `axiom`
- current `iofree`: builds, but still has
  - 2 `sorry`s in `LeanProofs/StepFRIte.lean`
  - 12 extern-only axioms

The 2 `sorry`s are not extern-local. They are consequences of the older if/regime
proof structure. They should not be carried into `new-iofree`.

### 4. IO-removal work exists only on current `iofree`

Current `iofree` already contains the wanted language/runtime direction:

- `EvalMode` removed
- built-in IO operators removed from syntax
- evaluator made pure
- raw extern expressions remain non-executable and return runtime errors if reached

This implementation work is worth porting to `new-iofree`.

### 5. Extern typing was substantially refactored on current `iofree`

Current `iofree` adds the extern work we do want:

- symbolic tags for extern specs
- `TagIndex` as symbolic extern-spec tags
- `collectAndAllocExternTags`
- `resolveSyntaxPred`
- fresh tag allocation at extern use sites
- extern-specific tests and Ott/documentation updates

This is a good candidate for selective transplant.

### 6. `main` includes cleanup that should remain authoritative

`main` already contains the changes we want to preserve:

- finished proofs
- removal of unused invariant / dead proof machinery
- no-mode3 proof cleanup
- updated Ott typing rules
- documentation cleanup
- typechecker/test cleanup
- removal of unused lemmas

`new-iofree` should inherit all of that from `main` and only layer the new
feature delta on top.

In particular, if a lemma was removed on `main` as unused, it should stay
removed on `new-iofree` unless the transplanted extern or IO-removal work
demonstrably needs it again.

## What To Keep From current `iofree`

Port these categories of changes:

1. IO removal in implementation and CLI-facing behavior
2. pure evaluator changes
3. symbolic tags for extern specifications and the associated fresh-tag resolution
4. extern `TagIndex` design and fresh-tag resolution
5. extern parser / syntax / Ott updates
6. extern tests
7. `doc/extern-axioms.md`
8. extern-only proof assumptions, adapted to the proof shape of `main`

## What Not To Port From current `iofree`

Do not port these categories unless a very specific dependency forces it:

1. bounded `Regime` representation with `R.bound`
2. `mode3` proof-specific infrastructure
3. proof lemmas whose only purpose is to support `R.lookup? k = none` branch-local
   regime insertion
4. the two `sorry`-based `mode3` theorems from `StepFRIte.lean`
5. older workaround code that existed only because `main` had not yet completed
   the non-extern FR proof stack
6. lemmas that `main` already removed as unused, unless a new dependency
   proves they are genuinely needed

## Proof Adaptation Inventory

The proof stack should not be treated as a single blob. The following files are
likely to need inspection during the port because they are heavily affected by
the branch divergence or by the implementation interfaces:

- `LeanProofs/TypeSafety.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/StepFRApp.lean`
- `LeanProofs/StepFRAssign.lean`
- `LeanProofs/StepFRIte.lean`
- `LeanProofs/FaultRobustnessProofs.lean`
- `LeanProofs/VarEnvPreservation.lean`
- `LeanProofs/SemanticsProperties.lean`
- `LeanProofs/RegimeConsistency.lean`

Default rule for these files:

- start from `main`'s version
- do not port current `iofree` versions wholesale
- make only the minimal edits required by the new implementation surface or by
  the extern-only proof contract

Specific guidance:

- `StepFRIte.lean`: main should remain authoritative; do not port the current
  `iofree` `mode3` lemmas or the two `sorry`-bearing theorems. Only adapt this
  file if implementation/interface changes force mechanical updates elsewhere.
- `StepFRApp.lean`: inspect for extern-related fallout from the new
  typechecker/runtime surface, but do not assume current `iofree` contains proof
  progress worth preserving beyond extern-local obligations.
- `VarEnvPreservation.lean`: this file changed significantly across the branch
  split, so it must be reviewed explicitly rather than being treated as
  unaffected background infrastructure.
- `FaultRobustnessProofs.lean`: start from `main`; reintroduce only the
  non-executable-extern handling and the extern-local proof assumptions needed
  by the new surface.

If any current `iofree` proof change appears useful and is not `mode3`-specific,
it should still be re-derived or re-applied against `main`'s proof shape rather
than copied wholesale.

## Migration Strategy

### Phase 1: Create the branch

Create `new-iofree` from current `main`.

No commits should be cherry-picked blindly from current `iofree`. The branch
history mixes useful changes with obsolete proof work. Port by file and hunk.

Recommended checkpoint discipline:

- keep one checkpoint artifact per green phase or subphase
- that checkpoint can be a local commit, a backup branch, or an exported patch
  stack
- do not begin the next major slice until the previous slice is buildable

This matters because rollback from a selective transplant is otherwise awkward.

### Phase 2: Port implementation-side IO removal

Primary files to inspect and selectively transplant:

- `LeanPoison/Syntax.lean`
- `LeanPoison/BigStep.lean`
- `LeanPoison/Typecheck.lean`
- `LeanPoison/Parser.lean`
- `LeanPoison/Pretty.lean`
- `Main.lean`
- `parser/tree-sitter-poison/grammar.js`

Target result:

- no `EvalMode`
- no language-level `rand`, `frand`, `printInt`, `printString`
- evaluator is pure and total over its non-IO cases
- extern expressions are typeable but not executable

Execution note:

- this phase will probably break proofs immediately
- do not leave the branch in that state for long
- port in micro-slices and restore `lake build` before declaring a checkpoint

### Phase 3: Port extern surface and typechecker changes

Primary items to transplant:

- symbolic-tag extern specification design
- `TagIndex`
- symbolic-tag extern syntax
- fresh tag allocation and resolution
- updated extern effect/return handling
- extern-specific validation checks

Primary files:

- `LeanPoison/Syntax.lean`
- `LeanPoison/Typecheck.lean`
- `poison-lang-spec/poison-lang.ott`
- parser-related files

Important constraint:

- adapt these changes to the proof and typechecker shape already present on
  `main`
- do not reintroduce `R.bound` while doing so
- expect immediate downstream proof fallout in `TypeSafety`, `StepFR`, and
  related files

### Phase 4: Port tests and docs

Primary files:

- extern examples in `examples/`
- IO-removal example updates
- `doc/extern-axioms.md`
- `doc/poison-interpreter.md`
- relevant description/spec text

Goal:

- tests reflect the new surface language
- docs describe the pure interpreter and extern contract accurately

This phase should also bring the axiom design document into place before the
proof-adaptation phase, so that the extern-only assumption boundary is explicit.

### Phase 5: Reintroduce extern-only proof assumptions

Use `main` as the proof authority for all non-extern reasoning.

Re-add only the extern-local assumptions needed after the implementation port.
The detailed grouping is already documented in `doc/extern-axioms.md`.

Primary files to expect in this phase:

- `doc/extern-axioms.md`
- `LeanProofs/TypeSafety.lean`
- `LeanProofs/StepFR.lean`
- `LeanProofs/StepFRApp.lean`
- `LeanProofs/StepFRAssign.lean`
- `LeanProofs/FaultRobustnessProofs.lean`
- `LeanProofs/StepFRIte.lean` only if forced by interface fallout, not as a
  source of ported `mode3` proof work
- `LeanProofs/VarEnvPreservation.lean` if the implementation changes require
  infrastructure adaptation

Expected outcome:

- no new non-extern `sorry`
- no new non-extern `axiom`
- extern assumptions remain isolated to extern typing/application obligations

### Buildability Policy During Migration

The conceptual order is implementation first, proof adaptation second. But the
execution policy should still preserve buildable checkpoints.

That means:

- allow short-lived local breakage inside a working session
- do not treat Phases 2 through 4 as a long broken interval
- instead execute them as repeated micro-cycles:
  1. port one implementation slice
  2. repair the directly affected proof surface
  3. run `lake build`
  4. record a checkpoint

This avoids a situation where the implementation is fully ported but the proof
stack is too broken to reason about incrementally.

### Phase 6: Validation

At each checkpoint:

1. run `lake build`
2. run `make test` if implementation-facing behavior changed
3. grep for `sorry` and `axiom`
4. confirm any remaining axioms are extern-only
5. confirm `mode3` and `R.bound` have not been reintroduced accidentally
6. confirm removed/unused lemmas from `main` have not been reintroduced
   without a concrete use
7. confirm no proof file was ported wholesale from current `iofree` without an
   explicit justification

## Suggested Port Order

This order minimizes proof churn:

1. create `new-iofree` from `main`
2. port one small implementation slice
3. adapt the directly affected proofs or interfaces
4. run `lake build`
5. record a checkpoint
6. repeat for the next slice
7. after the implementation surface is stable, reintroduce extern-only proof
   assumptions and finalize docs/tests

The critical rule is:

- implementation first as a design priority
- proof repair immediately after each slice as an execution rule
- no attempt to preserve the old `iofree` proof architecture

## Acceptance Criteria For `new-iofree`

`new-iofree` is successful when all of the following hold:

1. it starts from current `main`
2. it preserves `main`'s completed non-extern proofs
3. it removes built-in IO operators and old `EvalMode`
4. it keeps the extern refactor with symbolic tags and fresh tag allocation
5. any remaining assumptions are extern-only
6. there are no surviving `mode3` proof gaps from current `iofree`
7. the branch builds cleanly and tests are updated

## Practical Conclusion

Bringing `main` to current `iofree` is harder.

Bringing the wanted `iofree` delta onto `main` is easier.

That is the plan this document adopts.
