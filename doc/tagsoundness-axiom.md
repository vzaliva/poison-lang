# Eliminating `tagSoundness` via `TagMeaning` Threading

## Problem Statement

`ExternTypingAssumptions.tagSoundness` currently bridges a gap between extern
typechecking and the fault-robustness proof:

```lean
tagSoundness :
  ∀ (tm : TagMeaning) (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (nextTag nextTag' : Tag),
    collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag') →
    TagMappingRespectsTagMeaning tm mapping preds env
```

Extern typechecking allocates fresh concrete tags and inserts them into
resolved predicates, but the proof-only `TagMeaning` is never updated. The
axiom papers over the gap by asking an arbitrary fixed `tm` to already know
what allocation will produce. For `tm = {}` and any non-trivial extern
predicate, that is unsatisfiable.

The fix has two parts:

- structural plumbing: thread `TagMeaning` through typechecking and extend it
  at every extern allocation site;
- a semantic extern delta: when a new extern guard descriptor is inserted,
  assume, for now globally, that `predSat` is lawful for that descriptor.

The first part should be proved. The second part is the remaining trust input.
To minimize proof-interface churn while the structural threading lands, this
document stages it as a temporary global axiom named `externPredSatDelta` in
`LeanProofs/ExternTypingAssumptions.lean`. The FFI registry design in
`doc/ffi-axioms.md` should later replace that axiom with per-extern evidence.

## Proposal Overview

The refactor introduces five pieces:

1. **Structural extension relation** `tm ⊑ tm'`: every entry of `tm`
   survives unchanged in `tm'`.
2. **Boundedness invariant** `TagMeaningBounded tm bound`: `tm` contains no
   entries at or above `bound`. Threaded alongside `wfTagMeaningCtx`.
3. **Extern batch extension predicate** describing the exact `TagMeaning`
   insertions caused by one `collectAndAllocExternTags` /
   `resolveSyntaxPred` batch.
4. **Temporary extern predicate-satisfaction axiom**
   `externPredSatDelta`: if `PredSatLaws predSat tm` holds before an extern
   batch, and the batch structurally extends `tm` to `tm'`, then
   `PredSatLaws predSat tm'` holds.
5. **Canonical-extension predicates**: an internal fuel-indexed
   `IsCanonicalExtensionAtFuel tm ctx e fuel res tm'` for induction over
   `typecheck`, and a public wrapper `IsCanonicalExtension tm ctx e res tm'`
   that hides fuel.

A typechecker change is also required: `applyFnTClosure` /
`applyPFnTClosure` must sequence `nextTag` through closure alternatives so
that allocation ranges are disjoint by construction.

## The Extension Relation `⊑`

```lean
def TagMeaningExtends (tm tm' : TagMeaning) : Prop :=
  ∀ k d, tm.lookup k = some d → tm'.lookup k = some d

infix:50 " ⊑ " => TagMeaningExtends
```

`tm ⊑ tm'` allows insertions at tags `tm` does not mention; overwrites and
removals are forbidden.

Lean's `Std`, Batteries, and Mathlib do not provide a standard "submap" /
"extends" relation for `ExtTreeMap`, `HashMap`, `Finmap`, or `Finsupp` over
arbitrary value types. Define a generic `ExtTreeMap.IsSubmap` in
`LeanProofs/Aux.lean` with reflexivity, transitivity, and
`IsSubmap_of_insert_fresh`:

```lean
m.lookup k = none → ExtTreeMap.IsSubmap m (m.insert k v)
```

Make `TagMeaningExtends` a one-line `abbrev` over it in
`RegimeConsistency.lean`. This keeps the relation reusable for future maps.

Internal well-formedness of each `GuardDesc` is enforced by Lean's record
fields. No separate `WfTagMeaning` predicate is needed.

## The Boundedness Invariant

```lean
def TagMeaningBounded (tm : TagMeaning) (bound : Tag) : Prop :=
  ∀ k d, tm.lookup k = some d → k < bound
```

`tm ⊑ tm'` after allocation is not automatic from context-side freshness:
`TagBoundedCtx` only bounds tags reachable from the context, and
`wfTagMeaningCtx` only requires reachable descriptors to be in `tm`. Neither
rules out a `tm` that already contains entries at tags `≥ ctx.nextTag` for
unrelated descriptors, which an allocation could overwrite.

`TagMeaningBounded tm ctx.nextTag` rules that out. It is threaded alongside
`wfTagMeaningCtx` through every step lemma, and must appear in both premise
and conclusion of the threading theorem. Otherwise composite cases (`if`,
`seq`, closure alternatives) cannot safely chain further allocations.

The trivial supply `tm = {}` is vacuously bounded. Do not bake this into the
theorem statement: callers may later want to seed pre-allocated extern
descriptors.

## Extern Batch Tag-Meaning Extensions

One call to `collectAndAllocExternTags` allocates a concrete tag for each
distinct `guardClosure` index in the batch. `guardOnly` entries do not create
new descriptors; they alias the tag allocated for a `guardClosure` in the same
batch.

The structural proof should name that batch-level extension:

```lean
/-- `tm'` is `tm` extended with the guard descriptors allocated while
    resolving one extern predicate batch against `env`. -/
inductive ExternBatchTagMeaningExtension :
    TagMeaning → Tag → TagMapping → List SyntaxPredicate →
    VarTypeEnv → Tag → TagMeaning → Prop
```

The predicate records:

- `collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')`;
- every pre-existing entry of `tm` is preserved in `tm'`;
- for every `SyntaxPredicate.guardClosure idx arg body` in `preds`, if
  `mapping.get? idx = some tag` and `body.toPExpr = .ok pbody`, then
  `tm'.lookup tag = some { argName := arg, body := pbody,
  capEnv := VarTypeEnv.toCaptured env }`;
- `guardOnly idx` contributes no descriptor of its own;
- no allocated tag overwrites a pre-existing `tm` entry, using
  `TagMeaningBounded tm nextTag`;
- `TagMeaningBounded tm' nextTag'` holds for the returned supply.

The batch extension provides the compatibility fact currently consumed by
resolved-predicate call sites, stated for the output table:

```lean
theorem ExternBatchTagMeaningExtension.respects
    {tm nextTag mapping preds env nextTag' tm'} :
    ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' →
    TagMappingRespectsTagMeaning tm' mapping preds env
```

This theorem is structural. It does not by itself say anything about
`predSat`; it only says the proof table contains the descriptors that
typechecking just allocated.

## Temporary Global Axiom `externPredSatDelta`

`PredSat` is opaque:

```lean
abbrev PredSat := Tag → Memory → Value → Prop
```

So the fact that `tm'` contains a new descriptor at tag `k` does not prove that
`predSat k μ v` has the meaning prescribed by that descriptor. That is the
real semantic trust input.

For this refactor, introduce a temporary global axiom in
`LeanProofs/ExternTypingAssumptions.lean`:

```lean
/-- Temporary global extern trust input.

    This axiom avoids threading a new evidence structure through the whole
    proof while `TagMeaning` threading is being implemented. It must be
    replaced by per-extern registry evidence; see `doc/ffi-axioms.md`. -/
axiom externPredSatDelta
    (predSat : PredSat)
    {tm tm' : TagMeaning}
    {nextTag nextTag' : Tag}
    {mapping : TagMapping}
    {preds : List SyntaxPredicate}
    {env : VarTypeEnv} :
    PredSatLaws predSat tm →
    ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' →
    PredSatLaws predSat tm'
```

This is stronger than the intended final API because it ranges over all extern
batches, not over trusted extern declarations in the program. That is
acceptable as a staging point: it isolates the semantic assumption behind one
named axiom while the structural threading work lands.

The registry version should replace this global axiom with id-indexed evidence:
each trusted extern entry supplies the descriptor laws for the guard descriptors
that its declared return/effect summaries can allocate.

## The Canonical-Extension Predicate

```lean
-- Internal recursive predicate: tm' is the canonical extension produced by
-- typechecking (ctx, tm, e) with this exact fuel, terminating with `res`.
-- Constructors mirror `typecheckExpr` step-for-step; non-allocating cases
-- carry tm' = tm; each extern allocation site uses
-- ExternBatchTagMeaningExtension.
inductive IsCanonicalExtensionAtFuel :
    TagMeaning → TypeContext → Expr → Nat → TypeResult → TagMeaning → Prop

-- Public wrapper used by StepFR and top-level statements. Fuel remains an
-- implementation detail of `typecheck`.
def IsCanonicalExtension
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (res : TypeResult) (tm' : TagMeaning) : Prop :=
  ∃ fuel,
    typecheckExpr ctx e fuel = .ok res ∧
    IsCanonicalExtensionAtFuel tm ctx e fuel res tm'

theorem IsCanonicalExtensionAtFuel.unique
    {tm ctx e fuel res tm₁ tm₂} :
    IsCanonicalExtensionAtFuel tm ctx e fuel res tm₁ →
    IsCanonicalExtensionAtFuel tm ctx e fuel res tm₂ →
    tm₁ = tm₂

theorem IsCanonicalExtension.unique
    {tm ctx e res tm₁ tm₂} :
    IsCanonicalExtension tm ctx e res tm₁ →
    IsCanonicalExtension tm ctx e res tm₂ →
    tm₁ = tm₂
```

Use the predicate plus uniqueness form. This keeps inversion and case analysis
local to the typecheck derivation and avoids making computed tag meanings
depend on proof terms.

Both canonical-extension predicates are structural. They do not carry
`PredSatLaws`; they only record what tag table typechecking produced.
The public wrapper's uniqueness theorem uses a fuel-coherence lemma: successful
typechecks of the same `(ctx, e)` that produce the same `res` also produce the
same canonical extension.

## Threading Theorems

The basic theorem is structural:

```lean
theorem typecheck_extends_tagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult) :
    wfTagMeaningCtx tm ctx →
    TagBoundedCtx ctx →
    TagMeaningBounded tm ctx.nextTag →
    typecheckExpr ctx e fuel = .ok res →
  ∃ tm',
    IsCanonicalExtensionAtFuel tm ctx e fuel res tm' ∧
    IsCanonicalExtension tm ctx e res tm' ∧
    tm ⊑ tm' ∧
    TagMeaningBounded tm' res.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    QTypRespectsTagMeaning tm' res.qualType
```

Non-allocating cases construct `tm' = tm` reflexively. Allocating extern cases
insert at tags in `[ctx.nextTag, res.nextTag')`; `tm ⊑ tm'` follows from input
boundedness and the fresh-key update lemma.

The semantic companion theorem streams `PredSatLaws` upward through exactly
the extern batches that typechecking allocates:

```lean
theorem typecheck_preserves_predSatLaws
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult) :
    PredSatLaws predSat tm →
    wfTagMeaningCtx tm ctx →
    TagBoundedCtx ctx →
    TagMeaningBounded tm ctx.nextTag →
    typecheckExpr ctx e fuel = .ok res →
  ∃ tm',
    IsCanonicalExtensionAtFuel tm ctx e fuel res tm' ∧
    IsCanonicalExtension tm ctx e res tm' ∧
    tm ⊑ tm' ∧
    TagMeaningBounded tm' res.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    QTypRespectsTagMeaning tm' res.qualType ∧
    PredSatLaws predSat tm'
```

This uses a streaming direction: the proof starts with laws for the current
table and obtains laws for the extended table after each allocation step. The
price is exactly the temporary global axiom `externPredSatDelta`.

## Joins, Branches, and Closure Alternatives

### `if`

The current typechecker already sequences branch allocation: the second branch
is typechecked with `nextTag` advanced to the first branch's `nextTag'`
(`LeanPoison/Typecheck.lean:1554`-style branch construction). Branch
allocation ranges are disjoint, and the proof composes transitively:

```text
tm  --then-->  tm2  --else-->  tm3   submap chain: tm ⊑ tm2 ⊑ tm3
```

`IsCanonicalExtension` for the `if` node is constructed by composing the two
per-branch witnesses. `PredSatLaws` composes in the same order using
`typecheck_preserves_predSatLaws`.

### Closure-Application Alternatives

`applyFnTClosure` (`LeanPoison/Typecheck.lean:1467`) and
`applyPFnTClosure` (`LeanPoison/Typecheck.lean:1484`) currently `mapM` over
the closure list with the same input supply. Each alternative starts from the
same post-function-typecheck supply (the `nextTag'` / `nextLoc'` carried by
`result1`, the function-typecheck result; see the implementation note below)
and may allocate, so two alternatives can claim the same concrete tag for
different descriptors. No single post-join `tm` can explain that.

**The plan adopts sequencing.** Replace each `mapM` with a fold that threads
`nextTag` between iterations: the second alternative starts where the first
ended, and so on. Allocation ranges become disjoint by construction, and the
proof composes transitively as for `if`.

Sequence only the fresh-supply fields (`nextTag`, `nextLoc`). One
alternative's semantic environment, regime, or other context fields must not
flow into the next. Alternatives remain independent typings of the same
closure body against the same caller environment.

#### Implementation note: where the supply lives

At the call site `LeanPoison/Typecheck.lean:1468`, `applyFnTClosure` receives
`result1` from the function typecheck, not `result2` from the argument
typecheck. `result2` was typechecked first and used to build `ctx'`. Inside
the helper the parameter happens to be named `result2`, but the data it
carries is the function-typecheck result.

The helper reads its fresh-tag supply from this parameter's `nextTag'` field
at e.g. `LeanPoison/Typecheck.lean:1312, 1331, 1407, 1426, 1437`. A naive fold
over the closure list will not route the threaded supply correctly because
each call still reads that field from the original function-typecheck result.

Two implementation options:

- **Refactor** the helpers to take an explicit cursor `(nextTag, nextLoc)`
  argument and report the advanced cursor in the result. The fold's
  accumulator is the cursor pair.
- **Shim** the existing helper signatures by feeding in a synthetic
  `TypeResult`-shaped record per iteration whose `nextTag'` / `nextLoc'` are
  the threaded cursor and whose remaining fields (`qualType`, `memEnv'`,
  `tagEnv'`, `regime'`) match the original function-typecheck result.

Pick one before threading the proof. Whichever option is chosen, ensure the
non-supply fields (`qualType`, `memEnv'`, `tagEnv'`, `regime'`) are identical
across iterations. Only the supply cursors should differ.

## Threading Through `StepFR`

`StepFR` is stated over the input tag table and returns the output tag table.
Fuel is hidden inside `IsCanonicalExtension`.

```text
tm  --typecheck/evaluate e-->  tm'
```

The step theorem should consume:

- the current `tm`;
- `wfTagMeaningCtx tm ctx`;
- `TagMeaningBounded tm ctx.nextTag`;
- `PredSatLaws predSat tm`.

The conclusion gains an existential post-`tm'` with:

```lean
IsCanonicalExtension tm ctx e res tm' ∧
tm ⊑ tm' ∧
TagMeaningBounded tm' res.nextTag' ∧
wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
QTypRespectsTagMeaning tm' res.qualType ∧
PredSatLaws predSat tm'
```

The ordinary FR postcondition should be stated at `tm'` where it mentions tag
meaning. Composite cases feed the output `tm'` and `PredSatLaws predSat tm'`
from one subproof into the next subproof.

Only extern allocation cases invoke `externPredSatDelta`; non-allocating cases
preserve laws unchanged.

The step theorem wrapper still quantifies over `fuel`, because `typecheck` is
fuel-indexed:

```lean
def TypeSystemEnforcesFaultRobustness_step_spec
    (e : Expr) (ctx : TypeContext)
    (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (fuel : Nat) (res : TypeResult),
    typecheckExpr ctx e fuel = .ok res →
      StepFR ctx e res predSat tm
```

The `fuel` from this wrapper is used to build
`IsCanonicalExtensionAtFuel`; `StepFR` consumes only the fuel-hidden
`IsCanonicalExtension`.

The single-run step predicates follow the same shape: they consume the input
`tm`, `wfTagMeaningCtx tm ctx`, `TagMeaningBounded tm ctx.nextTag`, and
`PredSatLaws predSat tm`, then return an existential `tm'` with
`IsCanonicalExtension tm ctx e res tm'`, boundedness, output
`wfTagMeaningCtx`, output `QTypRespectsTagMeaning`, and
`PredSatLaws predSat tm'` before their existing one-run postconditions.

## Top-Level Lemma Impact

The public FR theorem keeps the same successful-typecheck premise shape:

```lean
∃ fuel res,
  typecheck ctx e fuel = .ok res ∧
  ObsConstraints obs res
```

The public theorem adds one initial tag-meaning premise:

```lean
TagMeaningBounded tm ctx.nextTag
```

The tag-meaning assumptions at the FR boundary are:

```lean
wfTagMeaningCtx tm ctx →
TagMeaningBounded tm ctx.nextTag →
PredSatLaws predSat tm →
...
```

`tagSoundness` is not a public theorem input. The structural compatibility
fact for resolved extern predicates is proved for the output tag table, and
`PredSatLaws` is advanced through extern allocation by the temporary global
axiom `externPredSatDelta`.

`ExternTypingAssumptions.guardProvenance` remains a public FR input. The
temporary global axiom is not passed by theorem users.

The theorem does not expose `tm'`, `IsCanonicalExtension`, or typecheck fuel in
the postcondition. Those are proof-internal witnesses used to establish the
existing observable-equivalence conclusion.

## Implementation Ordering

Build artifacts in this order. Earlier items are independently useful and
later items depend on them.

1. `ExtTreeMap.IsSubmap` in `Aux.lean` (refl, trans, fresh-insert) and the
   `TagMeaningExtends` `abbrev`. `TagMeaningBounded` plus preservation lemmas.
   Transport lemmas for `EnvRespectsTagMeaning`, `wfTagMeaningCtx`, and
   `QTypRespectsTagMeaning` along `⊑`.
2. `ExternBatchTagMeaningExtension` plus the derived
   `TagMappingRespectsTagMeaning` projection for the output table.
3. The temporary global axiom `externPredSatDelta` in
   `LeanProofs/ExternTypingAssumptions.lean`, plus helper lemmas saying one
   extern batch extends `PredSatLaws`.
4. `IsCanonicalExtensionAtFuel` (inductive predicate) plus `unique`,
   per-constructor composition lemmas, and the `⊑` projection.
   `IsCanonicalExtension` wrapper plus fuel-erasure and uniqueness lemmas.
   `typecheck_extends_tagMeaning` and `typecheck_preserves_predSatLaws`.
5. Typechecker change: sequence `nextTag` through `applyFnTClosure` /
   `applyPFnTClosure`, picking refactor-vs-shim per the implementation note
   above. Update existing extern-allocation tests and rebuild.
6. `StepFR` interface change: thread the input `tm`, output `tm'`, and
   `PredSatLaws predSat tm'` through every per-operator lemma and the FR
   orchestrator. The step-theorem wrapper continues to supply fuel to the
   typecheck-threading lemmas.

## Expected Proof Surface

Threading lemmas, introduced before changing per-case proofs:

- `ExtTreeMap.IsSubmap` (`Aux.lean`) with refl, trans,
  `IsSubmap_of_insert_fresh`.
- `TagMeaningExtends` (notation `⊑`) as an `abbrev` over it.
- `TagMeaningBounded tm bound` plus preservation under non-allocating steps
  (`bound` unchanged) and allocating steps (`bound` advances).
- Lookup-after-update-at-fresh-key:
  `tm.lookup k = none → tm ⊑ tm.update k d`.
- Transport lemmas for `EnvRespectsTagMeaning`, `wfTagMeaningCtx`, and
  `QTypRespectsTagMeaning` along `⊑`.
- `ExternBatchTagMeaningExtension` for one extern allocation batch.
- `ExternBatchTagMeaningExtension.respects`, deriving
  `TagMappingRespectsTagMeaning` for the output `tm'`.
- `externPredSatDelta`, a temporary global axiom in
  `LeanProofs/ExternTypingAssumptions.lean`.
- `PredSatLaws.extend_extern_batch`, a small wrapper around
  `externPredSatDelta`.
- `IsCanonicalExtensionAtFuel` (deterministic inductive) with `unique`,
  per-case composition lemmas, and the `⊑` projection.
- `IsCanonicalExtension` wrapper hiding fuel, plus uniqueness.
- `typecheck_extends_tagMeaning` and `typecheck_preserves_predSatLaws`.
- Per-allocation helpers for `typecheckExternVal`, extern
  `applyFnTClosure`, and extern `applyPFnTClosure`.
- FR-boundary inputs: `tmInit`, `TagMeaningBounded tmInit ctxInit.nextTag`,
  and `PredSatLaws predSat tmInit`.
- `StepFR` interface change: conclusion gains `tm'`,
  `IsCanonicalExtension tm ctx e res tm'`, `tm ⊑ tm'`,
  `TagMeaningBounded`, `wfTagMeaningCtx`, `QTypRespectsTagMeaning`, and
  `PredSatLaws predSat tm'`.
- Typechecker change: sequencing fold over `applyFnTClosure` /
  `applyPFnTClosure`, supply cursors only.

## End State

- `collectAndAllocExternTags` remains an executable allocator for concrete
  tags.
- The proof constructs the corresponding `TagMeaning` extension at each
  allocation site using ordinary map-update lemmas.
- `tagSoundness` is no longer a public assumption; resolved-predicate
  compatibility is proved for the output table `tm'`.
- `PredSatLaws` is streamed forward from `tm` to `tm'` using the temporary
  global axiom `externPredSatDelta`.
- The public theorem does not require callers to predict a final tag table.
- Once the FFI registry design is implemented, `externPredSatDelta` should be
  replaced by per-extern registry evidence for the guard descriptors each
  trusted extern declaration can allocate.
- `ExternTypingAssumptions.guardProvenance` is unaffected.
