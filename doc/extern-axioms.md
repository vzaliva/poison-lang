# Extern Functions: FR Contract Surface on `new-iofree`

This note records the residual semantic contract floor for extern
typechecking on `new-iofree`.

The proof reduction is complete.  What remains axiomatic is:

- Contract A: fresh-tag allocation for extern predicate resolution respects
  `TagMeaning`
- Contract B: impure extern application preserves **guard provenance**

The old poison-provenance half of Contract B is no longer axiomatic.  It is
now proved structurally by
`applyFnTClosure_extern_ok_memEnv_poison_origin`, and then threaded into the
whole-expression theorem
`typecheckExpr_lookup_origin_of_pc_true_split`.

## 1. Motivation

Externs matter to the fault-robustness proof only at the **typechecking
summary** layer, not at runtime.  Raw extern syntax (`externVal`,
`externFn`, `externPfn`) is operationally unreachable: runtime evaluation
fails on those forms.  The remaining proof surface is therefore about what
the typechecker says about external code.

That proof surface splits into two kinds of obligations:

1. **Typechecking-to-semantics coherence for fresh guards.**
   Extern typechecking resolves symbolic predicates using
   `collectAndAllocExternTags` and `resolveSyntaxPred`.  The resulting
   predicates may mention freshly allocated tags, so the proof needs a
   contract connecting those fresh tags to an arbitrary `TagMeaning`.
2. **Typechecking-to-semantics coherence for impure memory effects.**
   An impure extern summary may overwrite memory cells with resolved guard
   predicates.  The FR proof needs a contract saying that trusted output
   cells do not manufacture trust out of nowhere.

Not every externally-facing fact remained semantic.

- Pure externs require no provenance axiom because
  `applyPFnTClosure_extern_memEnv_eq` proves structurally that they do not
  modify memory.
- The poison half of the old impure-extern provenance contract is also now
  structural: under `ctx.pc = true`, every `applyExternEffect` write stores
  `poison = joinPoison true _ = true`, so any post-loop cell that remains
  clean must have been untouched by the effect loop.

What remains below is the actual residual contract floor.

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
  (mapping : Std.ExtTreeMap TagIndex Tag compare)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag : Tag) (nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')) :
  TagMappingRespectsTagMeaning tm mapping preds env
```

**Explanation**

This remains semantic because `tm` is universally quantified.  The ambient
well-formedness hypotheses constrain descriptors already present in the
typing context, but they do not force an arbitrary `TagMeaning` to assign
the right meaning to freshly allocated tags.  Once this contract is assumed,
the rest of the resolution pipeline is structural:
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

This is now a **guard-only** residual contract.  The poison analogue was
proved structurally and removed from the axiom surface.

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

This is the residual semantic boundary for impure extern provenance.

The hypotheses say:

- we are in the impure extern branch of `applyFnTClosure`
- the program counter is poisoned (`ctx.pc = true`)
- a particular output memory cell `l` is looked up as `qt_out`
- that output cell is trusted by an active guard tag `k`
- the cell is not itself a function type

The conclusion says that the same location already existed in the input
memory `ctx.memEnv` with a `QTyp` carrying the same guard tag, with the same
tag active in `ctx.regime`.

Why this remains semantic: the effect loop can overwrite cells with newly
resolved guard predicates while preserving the regime structure.  The proof
now handles poison structurally, but it does not yet derive this
guard-specific backward-origin fact from the shape of the extern summary
alone.
