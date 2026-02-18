# `stepFR_app` proof notes

## Goal

Eliminate the remaining `sorry` in `stepFR_app` (both arrow and parrow branches) in
`LeanProofs/FaultRobustnessProofs.lean` without introducing semantic-equality
infrastructure.

## Checkpoint (2026-02-18)

### Completed

- Proved helper synchronization lemmas:
  - `stepFR_app_arrow_sync_from_clean`
  - `stepFR_app_parrow_sync_from_clean`
- Proved helper extraction lemmas:
  - `stepFR_app_arrow_extract_shared_member`
  - `stepFR_app_parrow_extract_shared_member`
- Wired helper usage into both `stepFR_app` branches (arrow and parrow):
  - deferred clean-gated sync wrapper `_hsync1_of_clean`
  - extraction wrapper `_hextract_shared_of_sync`
  - combined wrapper `_sync_extract_of_clean`
- Replaced branch-level monolithic placeholders with explicit structured subgoals:
  - arrow branch now has explicit subgoals and a dedicated `resultAgreesIfClean`
    path that calls `_sync_extract_of_clean`
  - parrow branch now has the same structure
- Build status: `make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean`
  succeeds with expected `sorry` warnings only.

### Saved-state blocker shape

- The proof now fails only at explicit, local `sorry` subgoals in `stepFR_app`.
- Highest-priority open bridge in both branches:
  - derive `hclean1_e1` (clean at `result1`) from `hclean_res` (clean at joined `res`)
    so `_sync_extract_of_clean` can be used.
- After that bridge, the clean branch has a concrete shared witness package
  (`σcap` / `x,pbody,σcap`, `fuelBody`, `firstShared`, `result3Shared`) and needs:
  - body IH application on the shared body
  - transport from shared member facts to final joined `res` facts
- Dirty fallback (`¬ internalPoisonClean result1.qualType`) remains explicit and isolated.

## Current blocker

The main mismatch is structural:

- `typecheckApp_arrow_structure_full` gives a decomposition
  `results = first :: rest` and a join equation
  `joinTypeResults ctx first rest = .ok res`.
- In the app proof, runtime inversion (`apply*Closure*_inv_of_mapM_mem`) gives an
  arbitrary selected source result `src` with `src ∈ results`.
- Existing transport lemmas (`join_transport_*`) are parameterized by the join seed
  argument named `first` (the actual seed passed to `joinTypeResults`), not by an
  arbitrary member `src`.

So we know many premises for `src`, but the lemmas we want to use expect them for
the seed element from the typechecker decomposition.

## Why this is not just naming

This is not a trivial rename issue. In this context, `first` is fixed by
`results = first :: rest`. The runtime-chosen `src` may be different.

This matters most for clean-agreement transport: joined result facts can depend on
other members of `results`, not just on `src`.

## Constraints we want to keep

- Avoid semantic/setoid equality framework ("setoid hell").
- Avoid broad list-reordering infrastructure unless strictly necessary.
- Reuse existing `join_transport_*` lemmas where possible.
- Use `ioFree` monotonicity intuition (`typecheck_nextTag_mono`): subexpressions do
  not introduce new tags.

## Review-based corrections

### 1) Member-to-join "monotonicity" is not uniform

Some growth facts are easy (`nextLoc`, `nextTag` via `max`), but not all fields are
plainly monotone:

- `joinRegimes` is a meet/intersection-style operation, not a union.
- `joinMemEnvs` can drop bindings on type conflict (intended unreachable under
  well-typedness, but still present in the definition).

So transport from an arbitrary member to final `res` must carry explicit side
conditions; it cannot be treated as unconditional monotonicity.

### 2) `agreeOnClean` is the true hard edge

`join_transport_agreeOnClean` needs a premise of the form "clean lookup in joined
`res` can be viewed from source context". For an arbitrary selected member `src`,
this is generally false unless extra assumptions are provided.

### 3) Two runs can select different closures

The proof must explicitly address synchronization:

- run 0 may select one closure from `tcls`,
- run 1 may select another.

To apply body IH in the clean branch, we need to derive same-body alignment (or an
equivalent bridge) from the agreement facts on the function value.

## Revised suggested approach

### 1) Keep `typecheckApp_arrow_structure_full` as-is initially

Do not start with list split/reseed machinery. Keep the head-based decomposition and
work on local bridges first.

### 2) Add closure-synchronization lemma

From `hres_agree1` (for `e1` result) plus closure typing inversion, prove that in the
clean internal function case both runs select a compatible regular closure witness
that gives the same body expression needed by body IH.

Make the expected output explicit:

- shared `x` and shared `body` (so body IH is applicable to one expression),
- shared closure witness `tcl ∈ tcls`,
- therefore a single pinned member of `results` associated with that `tcl`.

This can collapse part of the `first` vs `src` mismatch in the clean branch: both
runs are forced to use the same selected source result. If that selected result is
the head seed, existing `join_transport_*` lemmas can be reused directly; otherwise
only a single-member bridge is needed.

### 3) Add only targeted join-to-res bridges

Introduce narrow lemmas for exactly the transported facts needed in `stepFR_app`:

- regime relation (existing monotone lemma path),
- `nextLoc`/`nextTag` bounds (existing max lemmas),
- memory/lookup transport only with explicit assumptions that make it valid.

Avoid broad reorder/commutativity proofs unless a concrete subgoal forces it.

### 4) Isolate `agreeOnClean` requirements explicitly

For `agreeOnClean`, require and prove a dedicated premise describing when clean
lookups in `res` are justified by available source facts. If this premise needs
all-members coverage, state it directly instead of forcing single-member transport.

## Red flag for fundamental formulation issue

If the proof requires deriving a property of the final joined result from a single
member `src` but that property can be changed by other members, the current theorem
shape is too weak. In that case, fix assumptions/statement rather than forcing the
proof.

## What to avoid

- Introducing semantic equality / setoid-style equivalence.
- Proving full permutation invariance of `joinTypeResults` up front.
- Planning to apply body IH to all alternatives in `results` without runtime
  termination evidence for those alternatives.

## Immediate next implementation steps

1. Prove the clean-backprop bridge used in both branches:
   `qtypCleanUnder (ctxAfter ctxᵢ res).regime res.qualType -> qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType`
   (or a variant specialized to `resultAgreesIfClean` needs).
2. In the clean branch of `resultAgreesIfClean`, use `_sync_extract_of_clean` output
   to run body IH with the shared closure witness and shared body, producing first/member-level postconditions.
3. Lift those first/member-level postconditions to `res` using existing `join_transport_*`
   lemmas and only minimal new side-condition lemmas where currently missing.
4. Close dirty fallback branch explicitly (show vacuous/typed agreement path without
   requiring clean synchronization).
5. Fill the remaining non-`resultAgreesIfClean` structured subgoals (typing, wf, instantiation,
   CWR, agreeOnClean, value consistency) using the same transport pipeline.
