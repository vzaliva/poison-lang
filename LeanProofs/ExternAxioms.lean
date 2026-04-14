/-
  ExternAxioms.lean — the semantic contract floor for extern typechecking
  in the fault-robustness proof.

  Extern type-checking has two obligations that cannot be discharged
  structurally:

  * fresh-tag coherence with an arbitrary `TagMeaning` (Contract A,
    `externTagSoundness`); and
  * guard provenance across impure extern summaries (Contract B,
    `externGuardProvenance`).

  See `doc/extern-axioms.md` for the detailed rationale.
-/
import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.RegimeConsistency

/-- Semantic predicate: the tag mapping produced by `collectAndAllocExternTags`
    is consistent with `tm`.  For every allocated tag that corresponds to a
    `guardClosure` predicate whose body successfully converts to `PExpr`, the
    tag meaning maps that tag to the expected guard descriptor. -/
def TagMappingRespectsTagMeaning (tm : TagMeaning)
    (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : Prop :=
  ∀ idx tag, mapping.get? idx = some tag →
    ∀ arg body pbody,
      (SyntaxPredicate.guardClosure idx arg body) ∈ preds →
      body.toPExpr = .ok pbody →
      tm.lookup tag = some { argName := arg, body := pbody,
                             capEnv := VarTypeEnv.toCaptured env }

/-- **Contract A: Tag Meaning Soundness.** The tag mapping produced by
    fresh-tag allocation respects any tag meaning `tm`.  This is the single
    semantic boundary for all extern `QTypRespectsTagMeaning` obligations: the
    claim that `tm` covers freshly allocated tags cannot be derived
    structurally because `tm` is universally quantified and `wfTagMeaningCtx`
    does not constrain it on fresh tags. -/
axiom externTagSoundness
  (tm : TagMeaning)
  (mapping : TagMapping)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag : Tag) (nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')) :
  TagMappingRespectsTagMeaning tm mapping preds env

/-- **Contract B: Guard Provenance for Impure Externs.** `FnTClosure.extern`
    preserves guard provenance: if an output memEnv cell is trusted by an
    active guard tag `k` and is not a function type, the same location already
    carried the same active guard in the input context.  The poison analogue
    is structural (`applyFnTClosure_extern_ok_memEnv_poison_origin`) and not
    part of this contract. -/
axiom externGuardProvenance
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
