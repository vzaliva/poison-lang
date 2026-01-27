# Issue 94 proposal (Option B)

This is a proposal for https://github.com/vzaliva/poison-lang/issues/94

## Suggested change
Adopt a deterministic weak update for assignment when the reference locset has
more than one element, and keep the current strong update for singleton
locsets.

- **Ott**: split assignment into two ordered rules (singleton first):
  - `assign_singleton` applies when `LS0 = {l}` and uses
    `G2[l |-> storedQt]` (strong update)
  - `assign_locset` applies when `LS0` has more than one element and uses
    `G2[LS0 |-> joinQt(G2(l), storedQt)]` for each `l ∈ LS0` (weak update)
- **Typechecker**: mirror the rule order, using the strong update only for
  singleton locsets and the join-update otherwise.

The weak update is componentwise: the stored type stays `ETyp.int`, poison is
joined with `joinPoison`, and predicates are joined with `joinPredicates` (both
in `LeanPoison/Typecheck.lean`). A concrete sketch is below.

```lean
-- Join two int-typed qualifiers in a weak update.
def joinQTyp (old new : QTyp) : QTyp :=
  ⟨ETyp.int, joinPoison old.poison new.poison, joinPredicates old.pred new.pred⟩

def updateLocsetWeak (env : MemoryTypeEnv) (ls : LocSet) (storedQt : QTyp) : MemoryTypeEnv :=
  LocSet.fold ls env (fun env l =>
    match env.get? l with
    | some qt => updateMemEnv env l (joinQTyp qt storedQt)
    | none => updateMemEnv env l storedQt)
```

In `typecheckAssign`, the change is a guarded update on `ls`, with the strong
update only when the locset is a singleton.

```lean
let storedQt : QTyp := ⟨ETyp.int, storedPoison, pred2⟩
let memEnv' :=
  if ls.isSingleton then
    updateMemEnv result2.memEnv' ls.some storedQt
  else
    updateLocsetWeak result2.memEnv' ls storedQt
```

Tag dependency invalidation remains unchanged and still ranges over the whole
locset.

## Soundness rationale (brief)
The runtime assignment updates exactly one concrete address determined by the
realisation map. For a locset with multiple logical locations, the typechecker
cannot know which logical location was realised. A weak update therefore makes
the post-typing environment a conservative approximation of all possible
outcomes.

- **No spurious cleanliness**: a clean write does not force all locations in a
  non-singleton locset to become clean; dirtiness is preserved via join. This
  prevents new agreement obligations on locations that were not necessarily
  updated.
- **Poison propagation is safe**: a poisoned write joins poison to all
  locations in the locset, which is conservative because any of those logical
  locations may have been realised.
- **Monotonicity**: poison and predicates only move towards less precise (more
  conservative) information under join, so the typing environment safely
  over-approximates runtime states.

Consequently, the post-context does not assert agreement on locations that
runtime has not necessarily touched, which is required for the StepFR
postcondition to hold.

## Expected impact
- The change is deterministic and executable.
- It reduces precision for non-singleton locsets but preserves precision for
  singleton locsets.
- Ott, the Lean typechecker, and dependent proofs will need aligned updates.
