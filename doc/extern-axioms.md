# Extern Functions: FR Contract Surface on `new-iofree`

This note records the semantic contract floor for extern typechecking on
`new-iofree`.

## 1. Motivation

Externs affect the fault-robustness proof only at the **typechecking
summary** layer, not at runtime. Raw extern syntax (`externVal`, `externFn`,
`externPfn`) is operationally unreachable: runtime evaluation fails on those
forms. The proof surface is therefore about what the typechecker states about
external code.

Two obligations arise:

1. **Typechecking-to-semantics coherence for fresh guards.**
   Extern typechecking resolves symbolic predicates using
   `collectAndAllocExternTags` and `resolveSyntaxPred`.  The resulting
   predicates may mention freshly allocated tags, so the proof needs a
   contract connecting those fresh tags to an arbitrary `TagMeaning`.
2. **Typechecking-to-semantics coherence for impure memory effects.**
   An impure extern summary may overwrite memory cells with resolved guard
   predicates. The FR proof needs a contract saying that trusted output
   cells do not manufacture trust out of nowhere.

Neither obligation is derivable from the syntactic shape of the typechecker
alone, so each is discharged by one axiom. Related obligations that *are*
structural — pure-extern memory preservation, the poison half of impure-extern
provenance, and `typecheckExternVal` lookup-origin preservation — are handled
by proved lemmas (`applyPFnTClosure_extern_memEnv_eq`,
`applyFnTClosure_extern_ok_memEnv_poison_origin`, and
`typecheckExternVal_preserves_lookup_origin` respectively).

## 2. Contracts

### 2.1 Contract A: Tag Meaning Soundness

**Plain English**

When extern typechecking allocates fresh tags and resolves symbolic
predicates, those fresh tags must already be interpreted correctly by the
chosen `TagMeaning`.  This is the semantic boundary behind all downstream
`QTypRespectsTagMeaning` corollaries for extern values, pure extern
applications, and impure extern applications.

**Exact axiom statement**

```lean
axiom externTagSoundness
  (tm : TagMeaning)
  (mapping : TagMapping)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag : Tag) (nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')) :
  TagMappingRespectsTagMeaning tm mapping preds env
```

**Explanation**

This is semantic because `tm` is universally quantified.  The ambient
well-formedness hypotheses constrain descriptors already present in the
typing context, but they do not force an arbitrary `TagMeaning` to assign
the right meaning to freshly allocated tags.  Given this contract, the rest
of the resolution pipeline is structural:
`resolveSyntaxPred_respectsTagMeaning` pushes the property through predicate
resolution, and the various extern corollaries push it through returned or
stored `QTyp`s.

### 2.2 Contract B: Guard Provenance for Impure Externs

**Plain English**

If an impure extern summary produces `r` under a poisoned pc, and a memory
cell is trusted in the output because it carries an active guard tag, that
trust must trace back to a corresponding guarded-and-active cell at the same
location in the input context.  In other words, impure extern type summaries
may move or preserve guarded trust, but they may not invent it.

The contract is **guard-only**: the poison analogue is structural (see §1)
and is not part of the axiom surface.

**Supporting definitions**

```lean
abbrev trustedGuardedCell (memEnv : MemoryTypeEnv) (regime : Regime)
    (l : Loc) (k : Tag) (qt : QTyp) : Prop :=
  memEnv.lookup l = some qt ∧
  qtypGuardTag qt = some k ∧
  regime.lookup? k = some true ∧
  qt.etyp.isFunctionType = false

abbrev ImpureExternCallOk (ctx : TypeContext) (r : TypeResult) : Prop :=
  ∃ st1 st2 p p1 argEtyp argPoison argPred result2 fuel
    x retSpec effects capturedEnv,
    applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r
```

**Exact axiom statement**

```lean
axiom externGuardProvenance
  (ctx : TypeContext) (r : TypeResult)
  (hcall : ImpureExternCallOk ctx r)
  (hpc : ctx.pc = true)
  (l : Loc) (k : Tag) (qt_out : QTyp)
  (hout : trustedGuardedCell r.memEnv' r.regime' l k qt_out) :
  ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
```

**Explanation**

The axiom reads directly: if `r` is the result of an impure extern call from
`ctx` under a poisoned pc, then every trusted guarded cell in the output
`(r.memEnv', r.regime')` traces back pointwise to a trusted guarded cell at
the same location in the input `(ctx.memEnv, ctx.regime)`.

`trustedGuardedCell memEnv regime l k qt` bundles the four-way conjunction
that characterises a cell trusted by guard `k`: the cell is present in
`memEnv` at `l` as `qt`, `qt` carries `k` as its guard tag, `k` is active in
`regime`, and `qt` is not a function type.  The function-type exclusion
matters because function-valued cells are handled separately: their trust
derives from the arrow's own regime and from closure regime consistency, not
from guard-tag provenance.

`ImpureExternCallOk ctx r` says that `r` is the result of *some* successful
`applyFnTClosure` call against an impure extern closure from context `ctx`.
The individual call-shape parameters (`st1`, `st2`, `argEtyp`, `effects`,
etc.) are existentially bound because they do not appear anywhere in the
axiom's conclusion — they are only witnesses that `r` came from an extern
call at all.

**Why this is semantic.** The effect loop can mint new guard predicates at
existing cells — `applyExternEffect` writes `effectSpecToQTyp effect.poison
resolvedPred`, where `resolvedPred` may be a `guardClosure` predicate with a
freshly allocated tag. Proving that any such minted guard, if later observed
as active in `r.regime'`, must correspond to a pre-existing active guard in
`ctx.regime` would require reasoning about the syntactic shape of effect specs
(which tags effects can introduce, which tags effects can promote to active)
that is not currently mechanized. Until that reasoning exists, guard
provenance is assumed.
