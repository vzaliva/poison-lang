/-
  ExternAxioms.lean — the semantic contract floor for extern typechecking
  in the fault-robustness proof.

  Extern type-checking has two obligations that cannot be discharged
  structurally:

  * fresh-tag coherence with an arbitrary `TagMeaning` (Contract A,
    `externTagSoundness`); and
  * guard provenance across impure extern summaries (Contract B,
    `externGuardProvenance`).
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

/-- A memory cell is trusted by an active guard tag when it is present in
    `memEnv`, carries a guard tag `k` that is active in `regime`, and is not
    a function-valued cell. -/
abbrev trustedGuardedCell (memEnv : MemoryTypeEnv) (regime : Regime)
    (l : Loc) (k : Tag) (qt : QTyp) : Prop :=
  memEnv.lookup l = some qt ∧
  qtypGuardTag qt = some k ∧
  regime.lookup? k = some true ∧
  qt.etyp.isFunctionType = false

/-- `r` is the result of some successful `applyFnTClosure` call against an
    impure extern closure from context `ctx`. -/
abbrev ImpureExternCallOk (ctx : TypeContext) (r : TypeResult) : Prop :=
  ∃ st1 st2 p p1 argEtyp argPoison argPred result2 fuel
    x retSpec effects capturedEnv,
    applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r

/-- **Contract B: Guard Provenance for Impure Externs.** If `r` is the result
    of an impure extern call from `ctx` under a poisoned pc, every trusted
    guarded non-function cell in the output traces back pointwise to a trusted
    guarded non-function cell at the same location in the input.  The poison
    analogue is structural
    (`applyFnTClosure_extern_ok_memEnv_poison_origin`) and not part of this
    contract. -/
axiom externGuardProvenance
  (ctx : TypeContext) (r : TypeResult)
  (hcall : ImpureExternCallOk ctx r)
  (hpc : ctx.pc = true)
  (l : Loc) (k : Tag) (qt_out : QTyp)
  (hout : trustedGuardedCell r.memEnv' r.regime' l k qt_out) :
  ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
