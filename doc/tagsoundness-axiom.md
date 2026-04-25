# `tagSoundness`: Missing `TagMeaning` Threading

## Problem Statement

`ExternTypingAssumptions.tagSoundness` currently exists to bridge a gap between
extern typechecking and the fault-robustness proof:

```lean
tagSoundness :
  ∀ (tm : TagMeaning) (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (nextTag nextTag' : Tag),
    collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag') →
    TagMappingRespectsTagMeaning tm mapping preds env
```

This should be treated as a symptom of a proof-interface bug, not as the right
long-term contract.

Extern typechecking already allocates fresh concrete tags and inserts them into
resolved predicates. What is missing is the corresponding proof-only
`TagMeaning` update. The proof keeps using the old `tm`, then asks an axiom to
pretend the old `tm` already knew about the fresh tags.

So the issue is not that we need a stronger axiom. The issue is that this axiom
should not be needed once `TagMeaning` is threaded correctly as ghost state.
The current axiom is a ghost-state shortcut: typechecking is already a stateful
computation that threads concrete tag allocation, but the proof-side state that
interprets those tags is not threaded. Instead, the axiom postulates that an
arbitrary fixed `tm` already knows what allocation will produce. That is why
the fix is structural rather than a missing semantic fact.

## Why the Current Axiom Fails

`TagMappingRespectsTagMeaning` requires each allocated concrete tag for a
`guardClosure` syntax predicate to already be present in `tm` with exactly the
descriptor produced from the predicate body and captured type environment:

```lean
def TagMappingRespectsTagMeaning (tm : TagMeaning)
    (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : Prop :=
  ∀ idx tag, mapping.get? idx = some tag →
    ∀ arg body pbody,
      (SyntaxPredicate.guardClosure idx arg body) ∈ preds →
      body.toPExpr = .ok pbody →
      tm.lookup tag = some { argName := arg, body := pbody,
                             capEnv := VarTypeEnv.toCaptured env }
```

But `collectAndAllocExternTags` only returns a `TagMapping` and an advanced
`nextTag`. It does not update `TagMeaning`.

For example:

```lean
tm      := {}
preds   := [SyntaxPredicate.guardClosure ⟨0⟩ "x" (Expr.bool true)]
nextTag := 0
```

Tag allocation succeeds and maps symbolic index `0` to concrete tag `0`. The
current axiom then requires:

```lean
tm.lookup 0 =
  some { argName := "x",
         body := PExpr.bool true,
         capEnv := VarTypeEnv.toCaptured env }
```

For `tm = {}`, this is impossible.

The premise `wfTagMeaningCtx tm ctx` does not help. It only says that `tm`
explains guard descriptors already reachable from the old context. Fresh extern
tags are not reachable before the extern predicate has been resolved and placed
in the result type or memory summary.

## Intuition

For ordinary non-extern expressions, the proof can keep the same `tm`.
Variables, `let`, references, assignments, conditionals, and closures mostly
copy, erase, join, or reason about guard predicates that were already present in
the input context. They do not create a new guard descriptor from syntax.

Externs are different. An extern declaration such as:

```poison
extern val @122 : (int :> poisoned { 1, v => v >= 0 })
```

turns a source-level symbolic tag index into a fresh concrete tag:

```text
symbolic index 1
  -> fresh concrete tag k
  -> Predicate.guardClosure k "v" (v >= 0) capturedEnv
```

At that point the proof also needs:

```text
tm[k] = { argName = "v", body = v >= 0, capEnv = capturedEnv }
```

The executable typechecker does not need to carry this table. `TagMeaning` is
proof-only. But the proof of typechecking must still model the ghost update:

```text
old tm
  + fresh extern guard meanings
= new tm'
```

The current axiom skips this update and asks the old `tm` to contain future
fresh allocations.

## Fixing Direction

Remove `ExternTypingAssumptions.tagSoundness` as a fundamental axiom by making
the missing proof-side `TagMeaning` update explicit.

The executable typechecker can stay as it is. The proof interface should expose
that typechecking may extend the tag meaning. The design should not require a
global invariant saying `tm` is empty or well-formed above `ctx.nextTag`; `tm`
may contain arbitrary irrelevant entries there. Instead, preserve the portion
of `tm` below the current allocation bound and add meanings for tags allocated
by the step:

```lean
def TagMeaningPreservesBelow (tm tm' : TagMeaning) (bound : Tag) : Prop :=
  ∀ k d, k < bound → tm.lookup k = some d → tm'.lookup k = some d

-- Representative theorem shape; this is proof plumbing, not an executable API.
theorem typecheck_extends_tagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
    wfTagMeaningCtx tm ctx →
    TagBoundedCtx ctx →
    typecheck ctx e fuel = .ok res →
  ∃ tm',
    TagMeaningPreservesBelow tm tm' ctx.nextTag ∧
    wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
    QTypRespectsTagMeaning tm' res.qualType := ...
```

This commits to the reachability/bounded-preservation design, not the alternative
where `tm` itself gets a new global freshness invariant. Since
`TagBoundedCtx ctx` says all tags reachable from the old context are below
`ctx.nextTag`, preserving meanings below `ctx.nextTag` is enough to preserve all
old semantic obligations while still allowing arbitrary garbage at future tags
to be overwritten.

For non-allocation cases, prove this with `tm' = tm`.

For allocation cases, construct `tm'` by inserting the descriptors for the
freshly allocated guard closures. The needed fact then follows from ordinary map
lookup-after-insert lemmas, not from an axiom. The extension-introducing cases
are exactly the places that call `collectAndAllocExternTags`: currently
`typecheckExternVal`, the extern branch of `applyFnTClosure`, and the simple
return branch of extern `applyPFnTClosure`. Extern `fn` / `pfn` declarations
themselves only capture the existing environment; their return specifications
allocate tags later, when the extern closure is applied.

Do not try to fix this by pre-populating `TagMeaning` from a whole-program scan.
Extern tag allocation is context- and order-dependent: the same symbolic tag
index at two extern sites can intentionally receive two different concrete
tags. The proof-side `TagMeaning` update should follow the actual allocation
step, not a separate global collection pass.

This construction relies on the existing `TagBoundedCtx ctx` invariant: tags
already reachable from the old context are below `ctx.nextTag`, while extern
allocation starts at `ctx.nextTag`. That is what makes the newly allocated tags
fresh relative to the old context.

## Joins and Branches

The main threading question is conditionals. A problematic design would
typecheck both branches from the same `ctx.nextTag`, allowing each branch to
allocate the same concrete tag for different guard descriptors. Then no single
post-join `tm'` could explain both branches.

The current typechecker avoids that collision. In both predicate-aware and
standard `if` paths, the second branch is typechecked with `nextTag` advanced
to the first branch's `nextTag'`. Therefore branch allocation ranges are
disjoint. The proof should mirror that order:

```text
tm  -- typecheck then branch --> tm₂
tm₂ -- typecheck else branch --> tm₃
post-join uses tm₃
```

Even when the final type result joins memory/tag environments rather than
sequencing runtime effects, the ghost tag meaning can be threaded sequentially
because it only records allocated tag descriptors. `TagMeaningPreservesBelow`
is what preserves the first branch's newly allocated meanings while the second
branch allocates above the advanced bound.

## PredSat Laws

This likely requires threading `tm`/`tm'` through the relevant preservation or
`StepFR` layer. Today many statements use one fixed `tm`; after this change,
extern-producing cases should be allowed to return an extended `tm'`.

One additional proof obligation remains: postconditions that require
`PredSatLaws predSat tm'` need a way to obtain laws for the extended tag
meaning. That should be handled explicitly as part of the ghost-state threading,
not hidden inside `tagSoundness`.

The direction matters. A naive monotonicity lemma
`PredSatLaws predSat tm → PredSatLaws predSat tm'` is not obviously available
for newly allocated tags, because the old laws only apply to contexts whose
guards are explained by the old `tm`. The proof API should instead require or
provide a law package stable under the tag-meaning extensions generated by
typechecking, for example:

```lean
-- Sketch only.
def PredSatLawsForGeneratedExtensions (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ tm', GeneratedTagMeaningExtension tm tm' → PredSatLaws predSat tm'
```

This keeps the trust boundary explicit: extending `TagMeaning` is structural
map construction, while obtaining predicate-satisfaction laws for the extended
meaning is a separate proof/assumption about `predSat`.

## Expected Proof Surface

The implementation should introduce the threading lemmas before changing every
case proof. Expected helpers:

- `TagMeaningPreservesBelow` with reflexivity and transitivity lemmas.
- Lookup-after-insert helpers for allocated guard descriptors.
- `EnvRespectsTagMeaning` / `wfTagMeaningCtx` / `QTypRespectsTagMeaning`
  transport under bounded preservation.
- A generated-extension law package for `PredSatLaws`.
- A constructor theorem like `typecheck_extends_tagMeaning`.
- Per-allocation helpers for `typecheckExternVal`, extern `applyFnTClosure`,
  and extern `applyPFnTClosure`.

The expected end state is:

- `collectAndAllocExternTags` remains an executable allocator for concrete
  tags.
- The proof constructs the corresponding `TagMeaning` extension.
- `tagSoundness` disappears or becomes a derived lemma about that construction.
