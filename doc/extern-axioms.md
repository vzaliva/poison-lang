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
axiom externTagMappingRespectsTagMeaning
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

An impure extern summary may write guarded cells into memory, but if a cell
is trusted in the output because it carries an active guard tag, that trust
must trace back to a corresponding guarded-and-active cell in the pre-call
context.  In other words, impure extern type summaries may move or preserve
guarded trust, but they may not invent it.

The contract is **guard-only**: the poison analogue is structural (see §1)
and is not part of the axiom surface.

**Exact axiom statement**

```lean
axiom applyFnTClosure_extern_ok_lookup_origin
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel = .ok r)
  (l : Loc) (qt_out : QTyp)
  (hlookup : r.memEnv'.lookup l = some qt_out)
  (hpc : ctx.pc = true)
  (k : Tag)
  (hguard : qtypGuardTag qt_out = some k)
  (hreg : r.regime'.lookup? k = some true)
  (hnotfun : qt_out.etyp.isFunctionType = false) :
  ∃ qt_in,
    ctx.memEnv.lookup l = some qt_in ∧
    qtypGuardTag qt_in = some k ∧
    ctx.regime.lookup? k = some true ∧
    qt_in.etyp.isFunctionType = false
```

**Explanation**

The hypotheses say:

- we are in the impure extern branch of `applyFnTClosure`
- the program counter is poisoned (`ctx.pc = true`)
- a particular output memory cell `l` is looked up as `qt_out`
- that output cell is trusted by an active guard tag `k`
- the cell is not itself a function type

The conclusion says that the same location already existed in the input
memory `ctx.memEnv` with a `QTyp` carrying the same guard tag, with the same
tag active in `ctx.regime`.

**Why the function-type exclusion.** Both pre- and post-image `QTyp`s are
required to satisfy `isFunctionType = false`. Function-valued cells are handled
separately: their trust derives from the arrow's own regime and from closure
regime consistency, not from guard-tag provenance, so they do not belong on
this particular obligation path.

**Why this is semantic.** The effect loop can mint new guard predicates at
existing cells — `applyExternEffect` writes `effectSpecToQTyp effect.poison
resolvedPred`, where `resolvedPred` may be a `guardClosure` predicate with a
freshly allocated tag. Proving that any such minted guard, if later observed
as active in `r.regime'`, must correspond to a pre-existing active guard in
`ctx.regime` would require reasoning about the syntactic shape of effect specs
(which tags effects can introduce, which tags effects can promote to active)
that is not currently mechanized. Until that reasoning exists, guard
provenance is assumed.
