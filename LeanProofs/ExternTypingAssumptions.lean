/-
  ExternTypingAssumptions.lean — the semantic contract floor for extern
  typechecking in the fault-robustness proof.

  Extern type-checking has a single semantic obligation supplied at the
  fault-robustness trust boundary:

  * `PredSatLaws` preservation across one structural extern allocation batch
    (`ExternTypingAssumptions.externPredSatDelta`).

  Guard-origin provenance is derived structurally: the typechecker erases
  predicates on extern effect writes under poisoned `pc` (mirroring assignment),
  making the guard-origin trace provable via
  `applyFnTClosure_extern_ok_memEnv_guard_origin` in `ExternTagMeaning.lean`.  See
  `doc/ffi-axioms.md` for the broader extern-boundary design.

  The contract lives as a field of `ExternTypingAssumptions`, threaded
  explicitly through the fault-robustness proof.  Callers must supply (or
  postulate) an `ExternTypingAssumptions` value to instantiate the FR
  theorem, making the trust boundary explicit at the public API.
-/

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.RegimeConsistency
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
open Std

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

/-- `tm'` is the canonical tag-meaning extension for one extern allocation
    batch produced by `collectAndAllocExternTags`.  This is a *structural*
    predicate: it records that `tm'` extends `tm`, is bounded by the new
    fresh-tag cursor, and matches every resolved `guardClosure` allocated by
    the batch.  It carries no `predSat` content; the semantic delta for
    `predSat` lives in `ExternTypingAssumptions.externPredSatDelta`. -/
def ExternBatchTagMeaningExtension
    (tm : TagMeaning) (nextTag : Tag)
    (mapping : TagMapping) (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (nextTag' : Tag) (tm' : TagMeaning) : Prop :=
  tm ⊑ tm' ∧
  TagMeaningBounded tm' nextTag' ∧
  TagMappingRespectsTagMeaning tm' mapping preds env ∧
  nextTag ≤ nextTag'

namespace ExternBatchTagMeaningExtension

/-- The submap projection. -/
theorem extends_tm
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    tm ⊑ tm' :=
  h.1

/-- The boundedness projection. -/
theorem bounded
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    TagMeaningBounded tm' nextTag' :=
  h.2.1

/-- The structural compatibility projection for the canonical extension. -/
theorem respects
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    TagMappingRespectsTagMeaning tm' mapping preds env :=
  h.2.2.1


end ExternBatchTagMeaningExtension

private def buildBatchTmStep (mapping : TagMapping) (env : VarTypeEnv)
    (acc : TagMeaning) (pred : SyntaxPredicate) : TagMeaning :=
  match pred with
  | SyntaxPredicate.guardClosure idx arg body =>
      match mapping.get? idx, body.toPExpr with
      | some tag, .ok pbody =>
          acc.update tag { argName := arg, body := pbody,
                           capEnv := VarTypeEnv.toCaptured env }
      | _, _ => acc
  | _ => acc

private def buildBatchTm (tm : TagMeaning) (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : TagMeaning :=
  preds.foldl (buildBatchTmStep mapping env) tm

private lemma TagMeaning.lookup_update_self
    (tm : TagMeaning) (tag : Tag) (desc : GuardDesc) :
    (tm.update tag desc).lookup tag = some desc := by
  show (tm.insert tag desc).get? tag = some desc
  rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert]
  simp

private lemma TagMeaning.lookup_update_ne
    (tm : TagMeaning) {tag tag' : Tag} (desc : GuardDesc)
    (hne : tag' ≠ tag) :
    (tm.update tag' desc).lookup tag = tm.lookup tag := by
  have hcmp : compare tag' tag ≠ Ordering.eq := by
    intro h
    exact hne (LawfulEqCmp.eq_of_compare h)
  show (tm.insert tag' desc).get? tag = tm.get? tag
  rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.get?_eq_getElem?]
  rw [ExtTreeMap.getElem?_insert]
  simp [hcmp]

private lemma buildBatchTm_fold_preserves_lookup
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag k : Tag} {d : GuardDesc}
    (hk_lt : k < nextTag)
    (h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag)
    (hlookup : acc.lookup k = some d) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup k = some d := by
  induction preds generalizing acc with
  | nil =>
      simpa using hlookup
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc hlookup
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc hlookup
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · rename_i tag _err
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · rename_i tag pbody
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have htag_ge : nextTag ≤ tag := h_alloc_ge idx tag hmap
            have hne : tag ≠ k := by
              intro hEq
              subst hEq
              exact Nat.not_le_of_gt hk_lt htag_ge
            have hlookup' : (acc.update tag desc).lookup k = some d := by
              rw [TagMeaning.lookup_update_ne acc desc hne]
              exact hlookup
            simpa [buildBatchTmStep, hmap', hbody, hdesc] using
              ih (acc.update tag desc) hlookup'

private lemma buildBatchTm_preserves_input_lookup
    (tm : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag : Tag}
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag) :
    tm ⊑ buildBatchTm tm mapping preds env := by
  intro k d hlookup
  exact buildBatchTm_fold_preserves_lookup tm mapping preds env
    (h_bounded k d hlookup) h_alloc_ge hlookup

private lemma TagMeaningBounded.update_lt
    {tm : TagMeaning} {bound tag : Tag} (h : TagMeaningBounded tm bound)
    (desc : GuardDesc) (htag : tag < bound) :
    TagMeaningBounded (tm.update tag desc) bound := by
  intro k d hlookup
  by_cases hEq : tag = k
  · subst hEq
    rw [TagMeaning.lookup_update_self] at hlookup
    cases hlookup
    exact htag
  · rw [TagMeaning.lookup_update_ne tm desc hEq] at hlookup
    exact h k d hlookup

private lemma buildBatchTm_fold_bounded
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {bound : Tag}
    (h_acc : TagMeaningBounded acc bound)
    (h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < bound) :
    TagMeaningBounded (preds.foldl (buildBatchTmStep mapping env) acc) bound := by
  induction preds generalizing acc with
  | nil =>
      simpa using h_acc
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc h_acc
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc h_acc
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · rename_i tag _err
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · rename_i tag pbody
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have h_acc' : TagMeaningBounded (acc.update tag desc) bound :=
              h_acc.update_lt desc (h_alloc_lt idx tag hmap)
            simpa [buildBatchTmStep, hmap', hbody, hdesc] using ih (acc.update tag desc) h_acc'

private lemma buildBatchTm_bounded
    (tm : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag nextTag' : Tag}
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_le : nextTag ≤ nextTag')
    (h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < nextTag') :
    TagMeaningBounded (buildBatchTm tm mapping preds env) nextTag' := by
  unfold buildBatchTm
  exact buildBatchTm_fold_bounded tm mapping preds env (h_bounded.mono h_le) h_alloc_lt

private lemma buildBatchTm_fold_preserves_lookup_of_compatible
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {tag : Tag} {desc : GuardDesc}
    (hlookup : acc.lookup tag = some desc)
    (hcompat : ∀ {idx : TagIndex} {arg : Name} {body : Expr} {pbody : PExpr},
      SyntaxPredicate.guardClosure idx arg body ∈ preds →
      mapping.get? idx = some tag →
      body.toPExpr = .ok pbody →
      desc = { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env }) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup tag = some desc := by
  induction preds generalizing acc with
  | nil =>
      simpa using hlookup
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      have hcompat_tail :
          ∀ {idx : TagIndex} {arg : Name} {body : Expr} {pbody : PExpr},
            SyntaxPredicate.guardClosure idx arg body ∈ rest →
            mapping.get? idx = some tag →
            body.toPExpr = .ok pbody →
            desc = { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } := by
        intro idx arg body pbody hmem hmap hbody
        exact hcompat (List.mem_cons_of_mem pred hmem) hmap hbody
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc hlookup hcompat_tail
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc hlookup hcompat_tail
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · rename_i tag' _err
            have hmap' : mapping[idx]? = some tag' := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · rename_i tag' pbody
            have hmap' : mapping[idx]? = some tag' := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc' : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc'
            have hlookup' : (acc.update tag' desc').lookup tag = some desc := by
              by_cases htag : tag' = tag
              · subst htag
                have hdesc_eq : desc = desc' := by
                  simpa [hdesc'] using
                    (hcompat (by simp) hmap hbody)
                rw [TagMeaning.lookup_update_self]
                exact congrArg some hdesc_eq.symm
              · rw [TagMeaning.lookup_update_ne acc desc' htag]
                exact hlookup
            simpa [buildBatchTmStep, hmap', hbody, hdesc'] using
              ih (acc.update tag' desc') hlookup' hcompat_tail

private lemma buildBatchTm_fold_lookup_of_guard_mem
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv)
    (h_cons : ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
      SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ preds →
      SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ preds →
      arg₁ = arg₂ ∧ body₁ = body₂)
    (h_inj : ∀ (idx₁ idx₂ : TagIndex) (tag : Tag),
      mapping.get? idx₁ = some tag → mapping.get? idx₂ = some tag → idx₁ = idx₂)
    {idx : TagIndex} {tag : Tag} {arg : Name} {body : Expr} {pbody : PExpr}
    (hmap : mapping.get? idx = some tag)
    (hmem : SyntaxPredicate.guardClosure idx arg body ∈ preds)
    (hbody : body.toPExpr = .ok pbody) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup tag =
      some { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } := by
  induction preds generalizing acc with
  | nil =>
      cases hmem
  | cons pred rest ih =>
      simp only [List.foldl]
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases pred with
        | noPred => cases hhead
        | guardOnly _ => cases hhead
        | guardClosure idx₀ arg₀ body₀ =>
            have h_eqs :=
              (SyntaxPredicate.guardClosure.injEq idx arg body idx₀ arg₀ body₀).mp hhead
            obtain ⟨hidx, harg, hbody_expr⟩ := h_eqs
            subst idx₀
            subst arg₀
            subst body₀
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have hlookup_head :
                (buildBatchTmStep mapping env acc
                    (SyntaxPredicate.guardClosure idx arg body)).lookup tag = some desc := by
              simp [buildBatchTmStep, hmap', hbody, hdesc, TagMeaning.lookup_update_self]
            have hcompat_tail :
                ∀ {idx' : TagIndex} {arg' : Name} {body' : Expr} {pbody' : PExpr},
                  SyntaxPredicate.guardClosure idx' arg' body' ∈ rest →
                  mapping.get? idx' = some tag →
                  body'.toPExpr = .ok pbody' →
                  desc = { argName := arg', body := pbody',
                           capEnv := VarTypeEnv.toCaptured env } := by
              intro idx' arg' body' pbody' hmem' hmap' hbody'
              have hidx' : idx' = idx := h_inj idx' idx tag hmap' hmap
              subst idx'
              have hhead_mem :
                  SyntaxPredicate.guardClosure idx arg body ∈
                    SyntaxPredicate.guardClosure idx arg body :: rest :=
                List.Mem.head rest
              have hagree := h_cons (List.mem_cons_of_mem _ hmem') hhead_mem
              have harg' : arg' = arg := hagree.1
              have hbody_expr' : body' = body := hagree.2
              subst arg'
              subst body'
              have hpbody : pbody' = pbody := by
                rw [hbody] at hbody'
                exact (Except.ok.inj hbody').symm
              subst pbody'
              rfl
            unfold buildBatchTmStep at hlookup_head
            simpa [hdesc] using
              buildBatchTm_fold_preserves_lookup_of_compatible
                (buildBatchTmStep mapping env acc (SyntaxPredicate.guardClosure idx arg body))
                mapping rest env hlookup_head hcompat_tail
      · have h_cons_tail :
            ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
              SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ rest →
              SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ rest →
              arg₁ = arg₂ ∧ body₁ = body₂ := by
          intro idx arg₁ arg₂ body₁ body₂ hmem₁ hmem₂
          exact h_cons (List.mem_cons_of_mem pred hmem₁) (List.mem_cons_of_mem pred hmem₂)
        exact ih (buildBatchTmStep mapping env acc pred) h_cons_tail htail

/-- Canonical extension for a general extern batch: given a successful
    `collectAndAllocExternTags` run and an input table bounded by the
    incoming fresh-tag cursor, construct the canonical tag-meaning table
    for the whole batch. -/
theorem ExternBatchTagMeaningExtension.canonical_general
    (tm : TagMeaning) (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (mapping : TagMapping) (nextTag nextTag' : Tag)
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_alloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')) :
    ∃ tm', ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' := by
  let tm' := buildBatchTm tm mapping preds env
  have h_le : nextTag ≤ nextTag' :=
    collectAndAllocExternTags_nextTag_ge preds nextTag mapping nextTag' h_alloc
  have h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag := by
    intro idx tag hget
    exact collectAndAllocExternTags_mapping_values_ge preds nextTag mapping nextTag'
      h_alloc idx tag hget
  have h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < nextTag' := by
    intro idx tag hget
    exact collectAndAllocExternTags_mapping_values_lt preds nextTag mapping nextTag'
      h_alloc idx tag hget
  have h_cons :
      ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
        SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ preds →
        SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ preds →
        arg₁ = arg₂ ∧ body₁ = body₂ := by
    intro idx arg₁ arg₂ body₁ body₂ hmem₁ hmem₂
    exact collectAndAllocExternTags_consistent_preds preds nextTag mapping nextTag'
      h_alloc hmem₁ hmem₂
  have h_inj :
      ∀ (idx₁ idx₂ : TagIndex) (tag : Tag),
        mapping.get? idx₁ = some tag → mapping.get? idx₂ = some tag → idx₁ = idx₂ := by
    intro idx₁ idx₂ tag hget₁ hget₂
    exact collectAndAllocExternTags_mapping_values_injective preds nextTag mapping nextTag'
      h_alloc idx₁ idx₂ tag hget₁ hget₂
  refine ⟨tm', ?_, ?_, ?_, h_le⟩
  · exact buildBatchTm_preserves_input_lookup tm mapping preds env h_bounded h_alloc_ge
  · exact buildBatchTm_bounded tm mapping preds env h_bounded h_le h_alloc_lt
  · intro idx tag hmap arg body pbody hmem hbody
    simpa [tm', buildBatchTm] using
      buildBatchTm_fold_lookup_of_guard_mem tm mapping preds env h_cons h_inj
        hmap hmem hbody

/-- Generic typing-side assumptions about the extern typechecking machinery:
    a single contract, preservation of `PredSatLaws` across one structural
    extern allocation batch.

    The fault-robustness theorem is relative to this assumption: callers must
    supply (or postulate) an `ExternTypingAssumptions` to instantiate it.  See
    `doc/ffi-axioms.md` for the extern-boundary design.

    The typechecker erases predicates on extern effect writes under poisoned `pc`
    (mirroring assignment), making the guard-origin trace structurally provable
    via `applyFnTClosure_extern_ok_memEnv_guard_origin`. -/
structure ExternTypingAssumptions where
  /-- **PredSat extension across one extern allocation batch.**
      When `tm` extends to `tm'` via a single extern batch (the structural
      `ExternBatchTagMeaningExtension` predicate) and `predSat` already satisfies
      `PredSatLaws` against `tm`, those laws survive in the extended table.

      This is a broad trust input: the field ranges over all extern batches
      rather than over only the trusted extern declarations a program names.  See
      `doc/ffi-axioms.md` for the extern-boundary design. -/
  externPredSatDelta :
    ∀ (predSat : PredSat)
      {tm tm' : TagMeaning}
      {nextTag nextTag' : Tag}
      {mapping : TagMapping}
      {preds : List SyntaxPredicate}
      {env : VarTypeEnv},
      PredSatLaws predSat tm →
      ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' →
      PredSatLaws predSat tm'

/-- Wrapper: stream `PredSatLaws` forward across one extern allocation batch
    using `ExternTypingAssumptions.externPredSatDelta`.  Provides the
    convenient name for use in the per-operator FR proofs. -/
theorem PredSatLaws.extend_extern_batch
    (extTyping : ExternTypingAssumptions) (predSat : PredSat)
    {tm tm' : TagMeaning}
    {nextTag nextTag' : Tag}
    {mapping : TagMapping}
    {preds : List SyntaxPredicate}
    {env : VarTypeEnv}
    (h : PredSatLaws predSat tm)
    (hbatch : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    PredSatLaws predSat tm' :=
  extTyping.externPredSatDelta predSat h hbatch
