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
what allocation will produce — for `tm = {}` and any non-trivial extern
predicate, that is unsatisfiable.

The fix is structural. `TagMeaning` is proof-only ghost state, but the proof
of typechecking must thread it: at each allocation site, build the
corresponding `TagMeaning` extension explicitly. Once that threading is in
place, `tagSoundness` becomes a derived lemma about ordinary map updates.

## Proposal Overview

The refactor introduces four pieces:

1. **Structural extension relation** `tm ⊑ tm'`: every entry of `tm`
   survives unchanged in `tm'`.
2. **Boundedness invariant** `TagMeaningBounded tm bound`: `tm` contains no
   entries at or above `bound`. Threaded alongside `wfTagMeaningCtx`.
3. **Canonical-extension predicate** `IsCanonicalExtension tm ctx e fuel res
   tm'` (deterministic, with a uniqueness theorem) saying `tm'` is the
   unique extension produced by typechecking `e` against `(ctx, tm, fuel)`.
4. **Ambient `tmFinal`** committed to by the caller. The proof maintains
   `tmCurrent ⊑ tmFinal` throughout and derives `PredSatLaws predSat
   tmCurrent` *downward* from a single caller-supplied `PredSatLaws predSat
   tmFinal` premise. No upward closure assumption is needed.

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
"extends" relation for `ExtTreeMap`, `HashMap`, `Finmap`, or `Finsupp` (over
arbitrary value types) — the right notion is not canonical. Define a generic
`ExtTreeMap.IsSubmap` in `LeanProofs/Aux.lean` with reflexivity,
transitivity, and `IsSubmap_of_insert_fresh` (`m.lookup k = none → IsSubmap
m (m.insert k v)`). Make `TagMeaningExtends` a one-line `abbrev` over it in
`RegimeConsistency.lean`. This keeps the relation reusable for any future
map.

Internal well-formedness of each `GuardDesc` is enforced at the type level
by Lean's record fields. No separate `WfTagMeaning` predicate is needed.

## The Boundedness Invariant

```lean
def TagMeaningBounded (tm : TagMeaning) (bound : Tag) : Prop :=
  ∀ k d, tm.lookup k = some d → k < bound
```

`tm ⊑ tm'` after allocation is *not* automatic from context-side freshness:
`TagBoundedCtx` only bounds tags reachable from the context, and
`wfTagMeaningCtx` only requires reachable descriptors to be in `tm`. Neither
rules out a `tm` that already contains entries at tags `≥ ctx.nextTag` for
unrelated descriptors, which an allocation could overwrite.

`TagMeaningBounded tm ctx.nextTag` rules that out. It is threaded alongside
`wfTagMeaningCtx` through every step lemma, and must appear in *both*
premise and conclusion of the threading theorem — otherwise composite cases
(`if`, `seq`, closure alternatives) cannot safely chain further allocations.
The trivial supply `tm = {}` is vacuously bounded.

## The Canonical-Extension Predicate

```lean
-- Deterministic predicate: tm' is the canonical extension produced by
-- typechecking (ctx, tm, e) with `fuel`, terminating with `res`. The
-- constructors mirror `typecheckExpr` step-for-step; non-allocating cases
-- carry tm' = tm; each call to `collectAndAllocExternTags` contributes
-- one descriptor insertion per distinct `guardClosure` index in the batch
-- (a single batch may insert multiple descriptors).
inductive IsCanonicalExtension :
    TagMeaning → TypeContext → Expr → Nat → TypeResult → TagMeaning → Prop

theorem IsCanonicalExtension.unique
    {tm ctx e fuel res tm₁ tm₂} :
    IsCanonicalExtension tm ctx e fuel res tm₁ →
    IsCanonicalExtension tm ctx e fuel res tm₂ →
    tm₁ = tm₂
```

Prefer the **predicate plus uniqueness** form over an equality-proof-indexed
function `canonicalExtension tm ctx e fuel res h`. Predicates compose more
cleanly under inversion and case analysis; equality-proof-indexed functions
tend to be awkward in Lean (proof-term dependence and rewrite issues at
composite sites).

A relation alone (without uniqueness) would still be too loose: a fixed
`predSat` would have to be lawful for two distinct `tm'` extensions related
to the same `tm` via different shape-valid descriptor insertions at the
same fresh tag. Determinism of typechecking is what closes that gap.

## Ambient `tmFinal` and Downward Transport

The trust boundary is a *single fixed* `tmFinal` chosen by the caller for
the specific program being verified — *not* a closure assumption
universally quantified over typecheck inputs. Such a closure assumption
would still admit cross-program collisions: two unrelated programs starting
at `tm = {}, ctx.nextTag = 0` can canonically allocate at tag 0 with
incompatible descriptors.

The FR theorem accepts:

```lean
(tmInit : TagMeaning)
(hInitBounded : TagMeaningBounded tmInit ctxInit.nextTag)
(tmFinal : TagMeaning)
(hCanonical :
  IsCanonicalExtension tmInit ctxInit e fuelInit resInit tmFinal)
(hLaws : PredSatLaws predSat tmFinal)
```

`hInitBounded` is required at the boundary because the threading theorems
consume `TagMeaningBounded tm ctx.nextTag` as a premise. Do *not* bake in
`tmInit = {}`: callers may want to seed pre-allocated extern descriptors,
and an explicit boundedness premise keeps that option open.

`tmFinal` is uniquely determined (up to `IsCanonicalExtension.unique`) by
the program and its initial inputs.

Throughout the proof, the threading invariant is `tmCurrent ⊑ tmFinal`.
Allocation steps construct `tmCurrent'` and re-establish
`tmCurrent' ⊑ tmFinal` from:

```lean
-- Sub-typechecks of the program have canonical extensions that fit
-- inside the program's top-level canonical extension.
theorem IsCanonicalExtension.sub_extends_top
    {tmInit ctxInit eTop fuelInit resTop tmFinal} :
    IsCanonicalExtension tmInit ctxInit eTop fuelInit resTop tmFinal →
    ∀ {tm ctx e fuel res tm'},
      ReachableSubTypecheck tmInit ctxInit eTop fuelInit
        tm ctx e fuel res →
      IsCanonicalExtension tm ctx e fuel res tm' →
      tm' ⊑ tmFinal
```

When laws are needed at `tmCurrent`, they are derived from
`PredSatLaws predSat tmFinal` and `tmCurrent ⊑ tmFinal` via *downward*
transport:

```lean
theorem PredSatLaws.transport_⊑
    {predSat tmCurrent tmFinal} :
    tmCurrent ⊑ tmFinal →
    PredSatLaws predSat tmFinal →
    PredSatLaws predSat tmCurrent
```

This is provable, not assumed. `match_iff` references `tm` only through
`EnvRespectsTagMeaning tm σ Γ` (preserved upward by `⊑`); the remaining
laws (`mem_monotone`, etc.) do not reference `tm` directly.

The trust boundary is one `PredSatLaws` premise on a single fixed `tmFinal`
— same shape as today's `PredSatLaws`, just at a richer `tmFinal` the
caller commits to up-front. The caller's task is concrete: compute
`tmFinal` by walking the program's typecheck (or construct it directly),
then supply the laws for that specific tag-meaning.
`ExternTypingAssumptions.guardProvenance` remains a separate trust input,
unaffected.

### `ReachableSubTypecheck` design

`ReachableSubTypecheck` is the highest-risk proof object in the design. It
must be defined coherently with `IsCanonicalExtension` so that
`sub_extends_top` is provable without case-analysis gymnastics. Two
options, in order of preference:

- **Derivation-indexed**: `ReachableSubTypecheck` is an inductive predicate
  whose constructors mirror the recursive structure of `typecheckExpr` and
  `IsCanonicalExtension`. Membership of `(tm, ctx, e, fuel, res)` in the
  reachability relation is established by walking the same derivation that
  built `hTop`. This makes `sub_extends_top` a structural induction over
  joint constructors of `IsCanonicalExtension` and `ReachableSubTypecheck`.
- **Trace-indexed**: `ReachableSubTypecheck` is parameterized by a trace of
  derivation steps from the top-level call to the sub-call, with each step
  recording the rule applied. More verbose, but inversion is mechanical.

Avoid a *purely syntactic* definition (e.g., "`e` is a sub-expression of
`eTop`") — `sub_extends_top` becomes painful or impossible because
allocation order depends on the typecheck derivation, not on syntactic
nesting alone.

## Threading Theorems

Two theorems: a generic structural one, and an ambient corollary that adds
`tm' ⊑ tmFinal`.

### Generic Threading Theorem

```lean
theorem typecheck_extends_tagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
    wfTagMeaningCtx tm ctx →
    TagBoundedCtx ctx →
    TagMeaningBounded tm ctx.nextTag →
    typecheckExpr ctx e fuel = .ok res →
  ∃ tm',
    IsCanonicalExtension tm ctx e fuel res tm' ∧
    tm ⊑ tm' ∧
    TagMeaningBounded tm' res.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    QTypRespectsTagMeaning tm' res.qualType
```

Non-allocating cases construct `tm' = tm` reflexively. Allocating cases
insert at tags in `[ctx.nextTag, res.nextTag')`; `tm ⊑ tm'` follows from
input boundedness via the fresh-key update lemma.

### Ambient `tm' ⊑ tmFinal` Corollary

```lean
theorem typecheck_extends_tagMeaning_ambient
    {tmInit ctxInit eTop fuelInit resTop tmFinal}
    (hTop : IsCanonicalExtension tmInit ctxInit eTop fuelInit resTop tmFinal)
    (tm ctx e fuel res)
    (hReach :
      ReachableSubTypecheck tmInit ctxInit eTop fuelInit tm ctx e fuel res) :
    wfTagMeaningCtx tm ctx →
    TagBoundedCtx ctx →
    TagMeaningBounded tm ctx.nextTag →
    typecheckExpr ctx e fuel = .ok res →
  ∃ tm',
    IsCanonicalExtension tm ctx e fuel res tm' ∧
    tm ⊑ tm' ∧
    tm' ⊑ tmFinal ∧
    TagMeaningBounded tm' res.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    QTypRespectsTagMeaning tm' res.qualType
```

`tm' ⊑ tmFinal` does *not* follow from `tm ⊑ tmFinal` and a successful
sub-typecheck alone — counterexample: take `tmFinal = tm`, then the
sub-typecheck still allocates a fresh descriptor not in `tmFinal`. `hTop`
and `hReach` are essential: `hTop` pins `tmFinal` as the top-level
canonical extension; `hReach` says the current sub-call is one inside that
top-level derivation. `tm' ⊑ tmFinal` then follows from
`IsCanonicalExtension.sub_extends_top`.

Per-operator step lemmas use the ambient form. The generic form is useful
for unit-style reasoning where no top-level `tmFinal` is fixed.

## Joins, Branches, and Closure Alternatives

### `if`

The current typechecker already sequences branch allocation: the second
branch is typechecked with `nextTag` advanced to the first branch's
`nextTag'` (`LeanPoison/Typecheck.lean:1554`-style branch construction).
Branch allocation ranges are disjoint, and the proof composes
transitively:

```text
tm  --then-->  tm₂  --else-->  tm₃   ⊑-chain: tm ⊑ tm₂ ⊑ tm₃ ⇒ tm ⊑ tm₃
```

`IsCanonicalExtension` for the `if` node is constructed by composing the
two per-branch witnesses.

### Closure-Application Alternatives

`applyFnTClosure` (`LeanPoison/Typecheck.lean:1467`) and `applyPFnTClosure`
(`LeanPoison/Typecheck.lean:1484`) currently `mapM` over the closure list
with the same input supply. Each alternative starts from the same
post-function-typecheck supply (the `nextTag'` / `nextLoc'` carried by
`result1`, the function-typecheck result; see the Implementation note
below) and may allocate, so two alternatives can claim the same concrete
tag for different descriptors. No single post-join `tm` can explain that.

**The plan adopts sequencing.** Replace each `mapM` with a fold that
threads `nextTag` between iterations: the second alternative starts where
the first ended, and so on. Allocation ranges become disjoint by
construction, and the proof composes transitively as for `if`.

Sequence *only* the fresh-supply fields (`nextTag`, `nextLoc`). One
alternative's semantic environment, regime, or other context fields must
*not* flow into the next — alternatives must remain independent typings of
the same closure body against the same caller environment.

#### Implementation note: where the supply lives

At the call site `LeanPoison/Typecheck.lean:1468`, `applyFnTClosure`
receives `result1` from the *function* typecheck (not `result2` from the
argument typecheck — `result2` was typechecked first and used to build
`ctx'`). Inside the helper the parameter happens to be named `result2`,
but the data it carries is the function-typecheck result.

The helper reads its fresh-tag supply from this parameter's `nextTag'`
field at e.g. `LeanPoison/Typecheck.lean:1312, 1331, 1407, 1426, 1437`. A
naive fold over the closure list will not route the threaded supply
correctly because each call still reads that field from the original
function-typecheck result.

Two implementation options:

- **Refactor** the helpers to take an explicit cursor `(nextTag, nextLoc)`
  argument and report the advanced cursor in the result. The fold's
  accumulator is the cursor pair. Cleaner, matches the existing `if`
  discipline.
- **Shim** the existing helper signatures by feeding in a synthetic
  `TypeResult`-shaped record per iteration whose `nextTag'` / `nextLoc'`
  are the threaded cursor and whose remaining fields (`qualType`,
  `memEnv'`, `tagEnv'`, `regime'`) match the original function-typecheck
  result. Less invasive but adds a synthetic shim.

Pick one before threading the proof. Whichever option is chosen, ensure
the non-supply fields (`qualType`, `memEnv'`, `tagEnv'`, `regime'`) are
*identical* across iterations — only the supply cursors should differ.

The alternative to sequencing — proving disjointness or post-join
harmlessness — is significantly harder, since today's collisions are real
and the joinwise reasoning would have to argue about content-preserving
behavior of `joinTypeResults` on overlapping fresh descriptors.

## Threading Through `StepFR`

`StepFR` (`LeanProofs/StepFR.lean:223`) currently fixes one `tm` in both
premise and conclusion. After the refactor, the threading state has two
parts:

- a *current* `tm` that grows along allocation, with `tm ⊑ tmFinal` as an
  invariant;
- the ambient `tmFinal` plus its top-level `IsCanonicalExtension` witness,
  carried unchanged.

The current `StepFR` signature carries only `(ctx, e, res)` plus the
opaque `predSat`/`tm` parameters. The new conclusion
`IsCanonicalExtension tm ctx e fuel res tm'` references `fuel` directly, so
the interface must additionally carry either:

- the `fuel` value used by the typecheck call, plus the `typecheckExpr ctx
  e fuel = .ok res` equation as a premise (so that
  `IsCanonicalExtension`/`ReachableSubTypecheck` can be stated against a
  concrete `fuel`); or
- a packed witness object (e.g. `TypecheckCall ctx e res` carrying the
  fuel and equation internally), which keeps the surface smaller but adds
  a thin wrapper.

The first option is straightforward and matches `typecheckExpr`'s
existing signature; the second is preferable if the per-operator lemmas
end up with too many fuel-passing points. Pick before threading.

The conclusion gains an existential post-`tm'`, `IsCanonicalExtension tm
ctx e fuel res tm'`, `tm ⊑ tm'`, `tm' ⊑ tmFinal`, and
`TagMeaningBounded tm' res.nextTag'`. These are threaded into
`StepFRSingle...`, every per-operator step lemma, and the FR orchestrator.
Composition threads `⊑` transitively and composes `IsCanonicalExtension`
derivation-by-derivation; `sub_extends_top` re-establishes `tm' ⊑ tmFinal`
at each step.

The opaque-`predSat` premise is packaged in a structure for forward
extensibility:

```lean
structure PredSatLawsBundle (predSat : PredSat) (tmFinal : TagMeaning) : Prop where
  laws : PredSatLaws predSat tmFinal
```

The bundle is `tmCurrent`-independent and travels unchanged. Wherever the
proof needs `PredSatLaws predSat tmCurrent`, it is derived from
`bundle.laws` and the current `tmCurrent ⊑ tmFinal` via
`PredSatLaws.transport_⊑`. The bundle is one-field today; keeping it as a
structure lets future trust inputs (e.g. a `guardProvenance` reformulation)
land without re-threading.

## Implementation Ordering

Build artifacts in this order. Earlier items are independently useful and
testable; later ones depend on them.

1. `ExtTreeMap.IsSubmap` in `Aux.lean` (refl, trans, fresh-insert) and the
   `TagMeaningExtends` `abbrev`. `TagMeaningBounded` plus preservation
   lemmas. Transport lemmas for `EnvRespectsTagMeaning`, `wfTagMeaningCtx`,
   `QTypRespectsTagMeaning` along `⊑`. `PredSatLaws.transport_⊑`.
2. `IsCanonicalExtension` (inductive predicate) plus `unique`,
   per-constructor composition lemmas, and the `⊑` projection.
   `ReachableSubTypecheck` (derivation-indexed) plus `sub_extends_top`.
   `typecheck_extends_tagMeaning` and the ambient corollary.
3. Typechecker change: sequence `nextTag` through `applyFnTClosure` /
   `applyPFnTClosure`, picking refactor-vs-shim per the implementation note
   above. Update existing extern-allocation tests and rebuild.
4. `StepFR` interface change: thread ambient `tmFinal`, top-level
   `IsCanonicalExtension`, and `ReachableSubTypecheck` through every
   per-operator lemma; wire in `PredSatLawsBundle`; replace `tagSoundness`
   uses with derived lemmas.

## Expected Proof Surface

Threading lemmas, introduced before changing per-case proofs:

- `ExtTreeMap.IsSubmap` (`Aux.lean`) with refl, trans, `IsSubmap_of_insert_fresh`.
  `TagMeaningExtends` (notation `⊑`) as an `abbrev` over it.
- `TagMeaningBounded tm bound` plus preservation under non-allocating
  steps (`bound` unchanged) and allocating steps (`bound` advances).
- Lookup-after-update-at-fresh-key: `tm.lookup k = none → tm ⊑ tm.update k d`.
- Transport lemmas for `EnvRespectsTagMeaning`, `wfTagMeaningCtx`,
  `QTypRespectsTagMeaning` along `⊑`.
- `PredSatLaws.transport_⊑`: downward transport (provable, not assumed).
- `IsCanonicalExtension` (deterministic inductive) with `unique`,
  per-case composition lemmas, and the `⊑` projection.
- `ReachableSubTypecheck` (derivation-indexed; not purely syntactic) plus
  `sub_extends_top`.
- `typecheck_extends_tagMeaning` (generic) and
  `typecheck_extends_tagMeaning_ambient` (corollary).
- Per-allocation helpers for `typecheckExternVal`, extern
  `applyFnTClosure`, and extern `applyPFnTClosure`.
- `PredSatLawsBundle` packaging the caller's `PredSatLaws predSat tmFinal`
  premise.
- FR-boundary inputs: `tmInit`, `TagMeaningBounded tmInit ctxInit.nextTag`,
  `tmFinal`, `IsCanonicalExtension tmInit ctxInit e fuelInit resInit
  tmFinal`, `PredSatLawsBundle predSat tmFinal`.
- `StepFR` interface change: ambient `tmFinal`, top-level
  `IsCanonicalExtension`, `ReachableSubTypecheck`, the typecheck `fuel`,
  and the `typecheckExpr ctx e fuel = .ok res` equation (or a packed
  `TypecheckCall` witness) carried as parameters; conclusion gains `tm'`,
  `IsCanonicalExtension`, `tm ⊑ tm'`, `tm' ⊑ tmFinal`, `TagMeaningBounded`.
  Threaded through `StepFRSingle...`, every per-operator step lemma, and
  the FR orchestrator.
- Typechecker change: sequencing fold over `applyFnTClosure` /
  `applyPFnTClosure`, supply cursors only.

## End State

- `collectAndAllocExternTags` remains an executable allocator for concrete
  tags.
- The proof constructs the corresponding `TagMeaning` extension at each
  allocation site using ordinary map-update lemmas.
- `tagSoundness` disappears or becomes a derived lemma. The only remaining
  caller-supplied tag-soundness inputs are `tmFinal` (with its
  `IsCanonicalExtension` witness) and `PredSatLaws predSat tmFinal`, both
  at a single fixed `tmFinal` chosen for the program.
- `guardProvenance` is unaffected.
