/-
  ExternTagMeaning.lean - Extern-regime tag-meaning machinery.

  Lemmas about `resolveSyntaxPred`, `surfaceSpecToQTyp`, `typecheckExternVal`,
  `applyFnTClosure`/`applyPFnTClosure` extern effects, and the `forIn` effect loops
  establishing `QTypRespectsTagMeaning` / `wfTagMeaningCtx` / lookup-origin facts.
  These reason only about Typecheck functions and the tag-meaning predicates
  (`QTypRespectsTagMeaning`, `wfTagMeaningCtx`, `EnvRespectsTagMeaning` from
  RegimeConsistency), so the module sits below StepFR in the import graph: above
  {TypeSafety, SemanticsProperties, RegimeConsistency, TagFrame},
  and imported by TypecheckInduction and StepFR.
-/
import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.FaultRobustness
import LeanProofs.TypeSafety
import LeanProofs.Auxiliary
import LeanProofs.SemanticsProperties
import LeanProofs.RegimeConsistency
import LeanProofs.TagFrame
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

-- ── lookup / ofCaptured helpers + captured-extern QTypRespectsTagMeaning ──
private lemma foldr_insert_domain (tenv : List (Name × QTyp)) (y : Name) (qt : QTyp) :
    (tenv.foldr (fun entry (acc : Std.ExtTreeMap Name QTyp varTypeEnvCmp) =>
      acc.insert entry.1 entry.2) ∅)[y]? = some qt →
    ∃ qt', tenv.lookup y = some qt' := by
  intro hlookup
  induction tenv with
  | nil => simp [List.foldr] at hlookup
  | cons hd tl ih =>
    simp only [List.foldr] at hlookup
    rw [Std.ExtTreeMap.getElem?_insert] at hlookup
    simp only [List.lookup]
    split at hlookup
    · rename_i hcmp
      have hkey : hd.1 = y := (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mp hcmp
      rw [show (y == hd.1) = true from beq_iff_eq.mpr hkey.symm]
      exact ⟨hd.2, rfl⟩
    · rename_i hcmp
      have hne : hd.1 ≠ y := fun h => hcmp (h ▸ (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mpr rfl)
      rw [show (y == hd.1) = false from beq_eq_false_iff_ne.mpr (Ne.symm hne)]
      exact ih hlookup

private lemma foldr_insert_of_list_lookup (tenv : List (Name × QTyp)) (y : Name) (qt : QTyp) :
    tenv.lookup y = some qt →
    (tenv.foldr (fun entry (acc : Std.ExtTreeMap Name QTyp varTypeEnvCmp) =>
      acc.insert entry.1 entry.2) ∅)[y]? = some qt := by
  intro hlookup
  induction tenv with
  | nil => simp [List.lookup] at hlookup
  | cons hd tl ih =>
    simp only [List.foldr, List.lookup] at hlookup ⊢
    rw [Std.ExtTreeMap.getElem?_insert]
    split at hlookup
    · rename_i hbeq
      have hkey : y = hd.1 := beq_iff_eq.mp hbeq
      rw [show varTypeEnvCmp hd.1 y = .eq from
        (LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mpr hkey.symm]
      simpa using hlookup
    · rename_i hbeq
      have hne : y ≠ hd.1 := beq_eq_false_iff_ne.mp hbeq
      have hcmp_ne : ¬(varTypeEnvCmp hd.1 y = .eq) :=
        fun hcmp => hne ((LawfulEqCmp.compare_eq_iff_eq (cmp := varTypeEnvCmp)).mp hcmp).symm
      rw [ite_eq_right hcmp_ne]
      exact ih hlookup

private lemma list_lookup_exists_of_ofCaptured_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ∃ qt', tenv.lookup y = some qt' :=
  foldr_insert_domain tenv y qt

lemma ofCaptured_lookup_of_list_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    tenv.lookup y = some qt →
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt :=
  foldr_insert_of_list_lookup tenv y qt

lemma list_lookup_of_ofCaptured_lookup
    (tenv : CapturedVarEnv) (y : Name) (qt : QTyp) :
    (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    tenv.lookup y = some qt := by
  intro hlookup
  rcases list_lookup_exists_of_ofCaptured_lookup tenv y qt hlookup with ⟨qt', hlist⟩
  have hlookup' : (VarTypeEnv.ofCaptured tenv).lookup y = some qt' :=
    ofCaptured_lookup_of_list_lookup tenv y qt' hlist
  have hqt : qt' = qt := by
    have : some qt' = some qt := by simpa [hlookup'] using hlookup
    exact Option.some.inj this
  simpa [hqt] using hlist

/-- Bridge: `List.lookup` success implies list membership. -/
private lemma list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β)
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; simp at h; subst heq; subst h
      exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

/-- Captured-env transfer for nested fn return: all entries in `unifiedEnv` that came from
    `capturedEnv` or the arg binding respect `tm`.  Uses `list_lookup_of_ofCaptured_lookup`
    and `VarTypeEnv` update semantics.
    Note: QTyp poison is `p` (matching the arrow's internal poison) for compatibility
    with `QTypInQTyp_fn_extern_root_or_self`; callers use `QTypRespectsTagMeaning_noPred_poison_transport`
    to transport to other poisons. -/
private lemma QTypRespectsTagMeaning_fn_extern_ofCaptured
    (tm : TagMeaning)
    (capturedEnv : CapturedVarEnv) (argName : Name) (argQt : QTyp)
    (innerId : ExternId) (innerArg : Name) (st₁ st₂ : Typ) (p : Poison)
    (retSpec : ExternReturn) (effects : List Effect) (declaredArgQt : QTyp)
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm argQt) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.arrow st₁ st₂ p
        [FnTClosure.extern innerId innerArg retSpec effects
          (VarTypeEnv.toCaptured ((VarTypeEnv.ofCaptured capturedEnv).update argName argQt)) declaredArgQt captures],
        p, Predicate.noPred⟩ := by
  let ctx' : TypeContext :=
    { pc := true, regime := {}, memEnv := {},
      varEnv := (VarTypeEnv.ofCaptured capturedEnv).update argName argQt,
      tagEnv := {}, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := fun _ _ => none }
  intro qt' k d hinq hqd
  rcases QTypInQTyp_fn_extern_root_or_self ctx' innerId innerArg st₁ st₂ p retSpec effects hinq rfl
    with hEq | ⟨y, qtRoot, hlookup, hInRoot⟩
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · simp only [VarTypeEnv.update, VarTypeEnv.lookup, ctx',
      Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hlookup
    by_cases hEq : compare argName y = Ordering.eq
    · simp [hEq] at hlookup; subst hlookup
      exact hargTm hInRoot hqd
    · simp [hEq] at hlookup
      have hlistLookup := list_lookup_of_ofCaptured_lookup capturedEnv y qtRoot hlookup
      exact (hcapTm y qtRoot (list_lookup_mem capturedEnv y qtRoot hlistLookup)) hInRoot hqd

/-- Captured-env transfer for nested pfn return (analogous to fn version). -/
private lemma QTypRespectsTagMeaning_pfn_extern_ofCaptured
    (tm : TagMeaning)
    (capturedEnv : CapturedVarEnv) (argName : Name) (argQt : QTyp)
    (innerId : ExternId) (innerArg : Name) (st₁ st₂ : Typ) (p : Poison)
    (retSpec : ExternReturn) (declaredArgQt : QTyp) (captures : List Capture)
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm argQt) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.parrow st₁ st₂ p
        [PFnTClosure.extern innerId innerArg retSpec
          (VarTypeEnv.toCaptured ((VarTypeEnv.ofCaptured capturedEnv).update argName argQt)) declaredArgQt captures],
        p, Predicate.noPred⟩ := by
  let ctx' : TypeContext :=
    { pc := true, regime := {}, memEnv := {},
      varEnv := (VarTypeEnv.ofCaptured capturedEnv).update argName argQt,
      tagEnv := {}, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := fun _ _ => none }
  intro qt' k d hinq hqd
  rcases QTypInQTyp_pfn_extern_root_or_self ctx' innerId innerArg st₁ st₂ p retSpec hinq rfl
    with hEq | ⟨y, qtRoot, hlookup, hInRoot⟩
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · simp only [VarTypeEnv.update, VarTypeEnv.lookup, ctx',
      Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hlookup
    by_cases hEq : compare argName y = Ordering.eq
    · simp [hEq] at hlookup; subst hlookup
      exact hargTm hInRoot hqd
    · simp [hEq] at hlookup
      have hlistLookup := list_lookup_of_ofCaptured_lookup capturedEnv y qtRoot hlookup
      exact (hcapTm y qtRoot (list_lookup_mem capturedEnv y qtRoot hlistLookup)) hInRoot hqd

-- ── extern-regime tag-meaning cluster ──
section ExternTagMeaningSig
variable (predSat : PredSat) (tm : TagMeaning) (fuel : Nat)

/-- Structural lemma: when the tag mapping respects `tm` and `resolveSyntaxPred`
    succeeds, the resolved predicate respects `tm`.  This is proved by case
    analysis on `pred` — the `guardClosure` case uses `TagMappingRespectsTagMeaning`
    directly; the other cases are vacuous. -/
lemma resolveSyntaxPred_respectsTagMeaning
    (tm : TagMeaning)
    (pred : SyntaxPredicate) (env : VarTypeEnv)
    (mapping : TagMapping)
    (preds : List SyntaxPredicate)
    (resolvedPred : Predicate)
    (hcompat : TagMappingRespectsTagMeaning tm mapping preds env)
    (hmember : pred ∈ preds)
    (hresolve : resolveSyntaxPred pred env mapping = .ok resolvedPred) :
    PredRespectsTagMeaning tm resolvedPred := by
  cases pred with
  | noPred =>
    simp [resolveSyntaxPred, pure, Except.pure] at hresolve
    subst hresolve
    intro _ _ _ _ h; cases h
  | guardOnly idx =>
    simp only [resolveSyntaxPred] at hresolve
    split at hresolve
    · simp [pure, Except.pure] at hresolve; subst hresolve
      intro _ _ _ _ h; cases h
    · simp at hresolve
  | guardClosure idx arg body =>
    simp only [resolveSyntaxPred, bind, Except.bind] at hresolve
    split at hresolve
    · rename_i tag htag
      cases htoPExpr : body.toPExpr with
      | error e => simp [htoPExpr] at hresolve
      | ok pbody =>
        simp only [htoPExpr, pure, Except.pure, Except.ok.injEq] at hresolve
        subst hresolve
        intro k' arg' pb' ve' hgc
        have heq := (Predicate.guardClosure.injEq _ _ _ _ _ _ _ _).mp hgc
        rcases heq with ⟨hk, harg, hpb, hve⟩
        subst hk; subst harg; subst hpb; subst hve
        exact hcompat idx tag htag arg body pbody hmember htoPExpr
    · simp at hresolve

/-- Helper: `surfaceSpecToQTyp` produces non-function ETyps. -/
private lemma surfaceSpecToQTyp_etyp_nonFunction (typ : Typ) (poison : Bool)
    (resolvedPred : Predicate) (ctx : TypeContext)
    (qt : QTyp) (ctx' : TypeContext)
    (hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx = .ok (qt, ctx')) :
    qt.etyp.isFunctionType = false := by
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure] at hsurf
  cases typ with
  | int | bool | unit | string =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsurf
    rw [← hsurf.1]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  | ref _ => simp at hsurf
  | arrow _ _ => simp at hsurf

/-- Helper: `surfaceSpecToQTyp` preserves the predicate in the result QTyp. -/
private lemma surfaceSpecToQTyp_pred_preserves (typ : Typ) (poison : Bool)
    (resolvedPred : Predicate) (ctx : TypeContext)
    (qt : QTyp) (ctx' : TypeContext)
    (hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx = Except.ok (qt, ctx')) :
    qt.pred = resolvedPred := by
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure] at hsurf
  split at hsurf
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at hsurf; rw [← hsurf.1])
    | (simp at hsurf)

/-- Helper: `returnSpecToQTyp` produces non-function ETyps. -/
private lemma returnSpecToQTyp_etyp_nonFunction (typ : Typ) (poison : Bool)
    (resolvedPred : Predicate) (nextLoc : Loc)
    (retQt : QTyp) (nextLoc' : Loc)
    (h : returnSpecToQTyp typ poison resolvedPred nextLoc = .ok (retQt, nextLoc')) :
    retQt.etyp.isFunctionType = false := by
  unfold returnSpecToQTyp at h
  simp [bind, Except.bind, pure, Except.pure] at h
  cases typ with
  | int | bool | unit | string =>
    simp [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  | ref _ => simp at h
  | arrow _ _ => simp at h

/-- Helper: `returnSpecToQTyp` preserves the predicate. -/
private lemma returnSpecToQTyp_pred_preserves (typ : Typ) (poison : Bool)
    (resolvedPred : Predicate) (nextLoc : Loc)
    (retQt : QTyp) (nextLoc' : Loc)
    (h : returnSpecToQTyp typ poison resolvedPred nextLoc = .ok (retQt, nextLoc')) :
    retQt.pred = resolvedPred := by
  unfold returnSpecToQTyp at h
  simp [bind, Except.bind, pure, Except.pure] at h
  cases typ <;> simp at h <;> (try exact h.1 ▸ rfl)

-- --------------------------------------------------------------------------
-- typecheckExternVal / simple-return tag-meaning corollaries
-- --------------------------------------------------------------------------

/-- `typecheckExternVal` result `QTyp` respects tag meaning when the allocation
    batch has already been shown structurally compatible with the table. -/
private lemma typecheckExternVal_QTypRespectsTagMeaning_of_respects
    (tm : TagMeaning) (ctx : TypeContext) (id : ExternId) (typ : Typ) (poison : Bool)
    (pred : SyntaxPredicate) (fuel : Nat) (res : TypeResult)
    (hcompatOfAlloc : ∀ (tagMapping : TagMapping) (nextTag' : Tag),
      collectAndAllocExternTags [pred] ctx.nextTag = .ok (tagMapping, nextTag') →
      TagMappingRespectsTagMeaning tm tagMapping [pred] ctx.varEnv)
    (htc : typecheckExternVal ctx id typ poison pred fuel = .ok res) :
    QTypRespectsTagMeaning tm res.qualType := by
  obtain ⟨_, tagMapping, nextTag', resolvedPred, ⟨qt, ctx'⟩, halloc, hresolved, hsurface, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  simp only
  have hcompat := hcompatOfAlloc tagMapping nextTag' halloc
  have hpredTm := resolveSyntaxPred_respectsTagMeaning tm pred ctx.varEnv tagMapping [pred]
    resolvedPred hcompat (List.Mem.head _) hresolved
  -- The surface spec preserves the predicate and produces a non-function ETyp
  have hsurfPred := surfaceSpecToQTyp_pred_preserves typ poison resolvedPred ctx qt ctx' hsurface
  have hsurfNotFun := surfaceSpecToQTyp_etyp_nonFunction typ poison resolvedPred ctx qt ctx' hsurface
  -- Lift PredRespectsTagMeaning to QTypRespectsTagMeaning
  rw [← hsurfPred] at hpredTm
  -- Destructure qt and prove directly
  obtain ⟨qt_e, qt_p, qt_pred⟩ := qt
  intro qt' k d hinq hqd
  have hEq := QTypInQTyp_eq_of_nonFunctionTarget hinq hsurfNotFun
  subst hEq
  cases qt_pred with
  | noPred => simp [qtypGuardDesc?] at hqd
  | guardOnly _ => simp [qtypGuardDesc?] at hqd
  | guardClosure k0 arg pb cap =>
    simp [qtypGuardDesc?] at hqd
    rcases hqd with ⟨hk, hd⟩; subst hk; subst hd
    exact hpredTm k0 arg pb cap rfl

/-- QTypRespectsTagMeaning is insensitive to poison when pred = noPred,
    because all deep guard descriptors come from the etyp (closures), not the pred. -/
private lemma QTypRespectsTagMeaning_noPred_poison_transport
    (tm : TagMeaning) (etyp : ETyp) (p1 p2 : Poison)
    (h : QTypRespectsTagMeaning tm ⟨etyp, p1, Predicate.noPred⟩) :
    QTypRespectsTagMeaning tm ⟨etyp, p2, Predicate.noPred⟩ := by
  intro qt' k d hinq hqd
  rcases QTypInQTyp_transport_etyp hinq (show (⟨etyp, p2, Predicate.noPred⟩ : QTyp).etyp =
      (⟨etyp, p1, Predicate.noPred⟩ : QTyp).etyp from rfl) with hEq | hinq'
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · exact h hinq' hqd

/-- Pure extern result QTyp respects tag meaning (all `ExternReturn` cases)
    when any simple-return allocation has a structural compatibility witness.
    Nested cases use captured-env transfer and do not allocate return tags. -/
lemma applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_of_respects
    (tm : TagMeaning)
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (_hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
    (hcompatSimple :
      ∀ {typ : Typ} {poison : Bool} {spred : SyntaxPredicate},
        retSpec = ExternReturn.simple typ poison spred →
        ∀ (tagMapping : TagMapping) (nextTag' : Tag),
          collectAndAllocExternTags [spred] result2.nextTag' = .ok (tagMapping, nextTag') →
          TagMappingRespectsTagMeaning tm tagMapping [spred]
            (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩))
    (declaredArgQt : QTyp)
    (happly : applyPFnTClosure (PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
    QTypRespectsTagMeaning tm r.qualType := by
  cases fuel with
  | zero => simp [applyPFnTClosure] at happly
  | succ n =>
    unfold applyPFnTClosure at happly
    simp only [bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    simp only [pure, Except.pure] at happly
    cases retSpec with
    | simple typ poison spred =>
      -- Simple return: use the structural compatibility witness `hcompatSimple`
      -- Reduce the ExternReturn match after cases
      simp only [] at happly
      split at happly
      · simp at happly
      · rename_i tagres halloc
        obtain ⟨tagMapping, nextTag'⟩ := tagres
        split at happly
        · simp at happly
        · rename_i resolvedPred hresolved
          split at happly
          · simp at happly
          · rename_i retres hret
            obtain ⟨retQt, nextLoc'⟩ := retres
            simp only [Except.ok.injEq] at happly; subst happly
            let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
            have hcompat : TagMappingRespectsTagMeaning tm tagMapping [spred] unifiedEnv := by
              simpa [unifiedEnv] using
                hcompatSimple rfl tagMapping nextTag' halloc
            have hpredTm := resolveSyntaxPred_respectsTagMeaning tm spred unifiedEnv tagMapping
              [spred] resolvedPred hcompat (List.Mem.head _) hresolved
            have hretPred := returnSpecToQTyp_pred_preserves typ poison resolvedPred result2.nextLoc'
              retQt nextLoc' hret
            have hretNotFun := returnSpecToQTyp_etyp_nonFunction typ poison resolvedPred
              result2.nextLoc' retQt nextLoc' hret
            obtain ⟨ret_e, ret_p, ret_pred⟩ := retQt
            simp only at hretNotFun hpredTm hretPred
            simp only [normalizeAppResultByProvenance]
            split
            · intro qt' k d hinq hqd
              have hEq := QTypInQTyp_eq_of_nonFunctionTarget hinq hretNotFun
              subst hEq; simp [qtypGuardDesc?] at hqd
            · rw [← hretPred] at hpredTm
              intro qt' k d hinq hqd
              have hEq := QTypInQTyp_eq_of_nonFunctionTarget hinq hretNotFun
              subst hEq
              cases ret_pred with
              | noPred => simp [qtypGuardDesc?] at hqd
              | guardOnly _ => simp [qtypGuardDesc?] at hqd
              | guardClosure k0 arg pb cap =>
                simp [qtypGuardDesc?] at hqd
                rcases hqd with ⟨hk, hd⟩; subst hk; subst hd
                exact hpredTm k0 arg pb cap rfl
    | nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
      -- Nested fn return: noPred + arrow type — use captured-env transfer
      simp only [] at happly
      split at happly
      · simp at happly
      · next v hresolve =>
        simp only [Except.ok.injEq] at happly; subst happly; simp only
        simp only [normalizeAppResultByProvenance]
        split <;> {
          intro qt' k d hinq hqd
          exact (QTypRespectsTagMeaning_noPred_poison_transport tm _ ctx.pc _
            (QTypRespectsTagMeaning_fn_extern_ofCaptured tm capturedEnv x
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              innerId innerArg innerArgTyp (parseReturnType innerRet) ctx.pc innerRet innerEffects v.1
              hcapTm hargTm)) hinq hqd }
    | nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
      -- Nested pfn return: noPred + parrow type — use captured-env transfer
      simp only [] at happly
      split at happly
      · simp at happly
      · next v hresolve =>
        simp only [Except.ok.injEq] at happly; subst happly; simp only
        simp only [normalizeAppResultByProvenance]
        split <;> {
          intro qt' k d hinq hqd
          have hpfnTm : QTypRespectsTagMeaning tm
              ⟨ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                [PFnTClosure.extern innerId innerArg innerRet
                  (VarTypeEnv.toCaptured
                    (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                      ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)) v.1 innerCaptures],
                ctx.pc, Predicate.noPred⟩ :=
            QTypRespectsTagMeaning_pfn_extern_ofCaptured tm capturedEnv x
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              innerId innerArg innerArgTyp (parseReturnType innerRet) ctx.pc innerRet v.1 innerCaptures
              hcapTm hargTm
          exact (QTypRespectsTagMeaning_noPred_poison_transport tm _ ctx.pc _ hpfnTm) hinq hqd }

/-- Canonical tag-meaning extension for a successful pure extern closure with
    a simple return specification. -/
lemma applyPFnTClosure_extern_simple_canonical_batch
    (tm : TagMeaning)
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (typ : Typ) (poison : Bool) (spred : SyntaxPredicate)
    (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
    (h_bounded : TagMeaningBounded tm result2.nextTag')
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
    (declaredArgQt : QTyp)
    (happly : applyPFnTClosure
      (PFnTClosure.extern id x (ExternReturn.simple typ poison spred) capturedEnv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
    ∃ (tm' : TagMeaning) (tagMapping : TagMapping) (nextTag' : Tag),
      let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      ExternBatchTagMeaningExtension tm result2.nextTag' tagMapping [spred] unifiedEnv
        nextTag' tm' ∧
      WithinLog tm r.tagLog' tm' ∧
      TagMeaningBounded tm' r.nextTag' ∧
      wfTagMeaningCtx tm' (ctxAfter ctx r) ∧
      QTypRespectsTagMeaning tm' r.qualType := by
  cases fuel with
  | zero => simp [applyPFnTClosure] at happly
  | succ n =>
    unfold applyPFnTClosure at happly
    simp only [bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    rename_i hgate
    rw [Bool.not_eq_true, Bool.not_eq_false'] at hgate
    simp only [pure, Except.pure] at happly
    cases halloc : collectAndAllocExternTags [spred] result2.nextTag' with
    | error err => simp [halloc] at happly
    | ok tagres =>
      obtain ⟨tagMapping, nextTag'⟩ := tagres
      simp only [halloc] at happly
      cases hresolved : resolveSyntaxPred spred
          (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
          tagMapping with
      | error err => simp [hresolved] at happly
      | ok resolvedPred =>
        simp only [hresolved] at happly
        cases hret : returnSpecToQTyp typ poison resolvedPred result2.nextLoc' with
        | error err => simp [hret] at happly
        | ok retres =>
          obtain ⟨retQt, nextLoc'⟩ := retres
          simp only [hret] at happly
          simp only [Except.ok.injEq] at happly
          subst happly
          let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          obtain ⟨tm', hbatch⟩ :=
            ExternBatchTagMeaningExtension.canonical_general tm [spred] unifiedEnv
              tagMapping result2.nextTag' nextTag' h_bounded halloc
          let outQt : QTyp :=
            normalizeAppResultByProvenance (joinPoison p1 p)
              ⟨retQt.etyp, joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison)),
                retQt.pred⟩
          let outRes : TypeResult :=
            { qualType := outQt, memEnv' := result2.memEnv',
              tagEnv' := installReturnGuard result2.tagEnv' resolvedPred
                (applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping) n,
              nextLoc' := nextLoc', nextTag' := nextTag',
              regime' := applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping,
              declared' := result2.declared',
              tagLog' := externTagLog [spred] unifiedEnv tagMapping }
          refine ⟨tm', tagMapping, nextTag', hbatch, hbatch.within, ?_, ?_, ?_⟩
          · simpa [outRes] using ExternBatchTagMeaningExtension.bounded hbatch
          · have hwf' : wfTagMeaningCtx tm' (ctxAfter ctx result2) :=
              wfTagMeaningCtx_mono (ExternBatchTagMeaningExtension.extends_tm hbatch) hwf
            have hmem := applyPFnTClosure_extern_memEnv_eq ctx st1 st2 p p1
              argEtyp argPoison argPred result2 outRes
              (Nat.succ n) id x (ExternReturn.simple typ poison spred) capturedEnv declaredArgQt
              (captures := captures) (by
                unfold applyPFnTClosure
                simp [hgate, halloc, hresolved, hret, outRes, outQt, unifiedEnv, bind, Except.bind,
                  pure, Except.pure])
            simp only [wfTagMeaningCtx, ctxAfter] at hwf' ⊢
            simpa [hmem] using hwf'
          · exact
              applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_of_respects
                (tm := tm') (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
                (result2 := result2) (fuel := Nat.succ n) (id := id) (x := x)
                (retSpec := ExternReturn.simple typ poison spred) (capturedEnv := capturedEnv)
                (declaredArgQt := declaredArgQt) (captures := captures) (r := outRes)
                (wfTagMeaningCtx_mono (ExternBatchTagMeaningExtension.extends_tm hbatch) hwf)
                (fun name qt hmem =>
                  QTypRespectsTagMeaning_mono
                    (ExternBatchTagMeaningExtension.extends_tm hbatch) (hcapTm name qt hmem))
                (QTypRespectsTagMeaning_mono
                  (ExternBatchTagMeaningExtension.extends_tm hbatch) hargTm)
                (fun hspec tagMapping' nextTag'' halloc' => by
                  cases hspec
                  rw [halloc] at halloc'
                  cases halloc'
                  exact ExternBatchTagMeaningExtension.respects hbatch)
                (by
                  unfold applyPFnTClosure
                  simp [hgate, halloc, hresolved, hret, outRes, outQt, unifiedEnv, bind, Except.bind,
                    pure, Except.pure])

-- --------------------------------------------------------------------------
-- Impure extern corollary
-- --------------------------------------------------------------------------

/-- The assign-shaped memEnv update (singleton strong / non-singleton weak)
    preserves "all cells respect tag meaning", given the stored predicate respects
    tag meaning.  This is the assignment-shaped update used by
    `applyExternEffect`. -/
private lemma assign_memEnv_formula_allCellsRespect
    (tm : TagMeaning) (env : MemoryTypeEnv) (ls : LocSet)
    (storedPoison : Poison) (storedPred : Predicate)
    (hinit : ∀ l qt, env.lookup l = some qt → QTypRespectsTagMeaning tm qt)
    (hstored : PredRespectsTagMeaning tm storedPred) :
    ∀ l qt, (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 ⟨ETyp.int, storedPoison, storedPred⟩
      | _ => updateLocsetWeak env ls storedPoison storedPred).lookup l = some qt →
      QTypRespectsTagMeaning tm qt := by
  have hEnvInit : EnvRespectsTagMeaning tm {} env :=
    EnvRespectsTagMeaning.intro fun ⟨qtDeep, k0, d0, hqte0, hqd0⟩ => by
      rcases hqte0 with ⟨_, _, xv, _, qtRoot, hlookupVar, _⟩ | ⟨_, _, loc, _, qtRoot, hlookupMem, hinq⟩
      · simp [VarTypeEnv.lookup] at hlookupVar
      · exact (hinit loc qtRoot hlookupMem) hinq hqd0
  have hQt : QTypRespectsTagMeaning tm ⟨ETyp.int, storedPoison, storedPred⟩ :=
    QTypRespectsTagMeaning_int_of_predRespects tm storedPoison storedPred hstored
  have hEnvPost : EnvRespectsTagMeaning tm {} (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 ⟨ETyp.int, storedPoison, storedPred⟩
      | _ => updateLocsetWeak env ls storedPoison storedPred) := by
    cases hls : Std.ExtTreeSet.toList ls with
    | nil =>
        simpa using EnvRespectsTagMeaning_updateLocsetWeak tm {} env ls storedPoison storedPred hEnvInit hstored
    | cons x xs =>
        cases xs with
        | nil =>
            simpa using EnvRespectsTagMeaning_updateMemEnv tm {} env x
              ⟨ETyp.int, storedPoison, storedPred⟩ (by simp) hEnvInit hQt
        | cons y ys =>
            simpa using EnvRespectsTagMeaning_updateLocsetWeak tm {} env ls storedPoison storedPred hEnvInit hstored
  intro loc qtRoot hlookup qtDeep k d hinq hqd
  rcases hEnvPost with ⟨hPost⟩
  exact hPost (GuardDescInEnvsDeep.intro qtDeep k d
    (QTypInEnvs.inMem {} _ loc qtDeep qtRoot hlookup hinq) hqd)

/-- Per-step: `applyExternEffect` preserves the all-cells-respect-tm invariant. -/
private lemma applyExternEffect_preserves_allCellsRespect
    (tm : TagMeaning) (effect : Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (allPreds : List SyntaxPredicate)
    (pc : Poison) (memEnv memEnv' : MemoryTypeEnv)
    (hcompat : TagMappingRespectsTagMeaning tm tagMapping allPreds unifiedEnv)
    (hpred : effect.pred ∈ allPreds)
    (hinit : ∀ l qt, memEnv.lookup l = some qt → QTypRespectsTagMeaning tm qt)
    (happly : applyExternEffect effect unifiedEnv tagMapping pc memEnv = .ok memEnv') :
    ∀ l qt, memEnv'.lookup l = some qt → QTypRespectsTagMeaning tm qt := by
  unfold applyExternEffect at happly
  simp only [bind, Except.bind] at happly
  split at happly
  · rename_i qtVar _hlookup
    split at happly
    · rename_i ls _hls
      split at happly
      · simp at happly
      · rename_i resolvedPred hresolve
        simp [pure, Except.pure] at happly; subst happly
        have hpredTm := resolveSyntaxPred_respectsTagMeaning tm effect.pred unifiedEnv
          tagMapping allPreds resolvedPred hcompat hpred hresolve
        -- The effect update mirrors assignment.  Under a poisoned target ref
        -- (`qtVar.poison`) or a poisoned `pc`, the stored predicate is `noPred`
        -- (respecting tag meaning vacuously); otherwise it is the resolved pred.
        apply assign_memEnv_formula_allCellsRespect tm memEnv ls _ _ hinit
        split
        · intro k an pb ve hEq; cases hEq
        · simpa [effectSpecToQTyp] using hpredTm
    · simp at happly
  · simp at happly

-- --------------------------------------------------------------------------
-- Per-entry-point corollaries
-- --------------------------------------------------------------------------

/-- Helper: each effect's pred is in `collectExternPreds retSpec effects`. -/
private lemma effect_pred_mem_collectExternPreds
    (retSpec : ExternReturn) (effects : List Effect)
    (effect : Effect) (hmem : effect ∈ effects) :
    effect.pred ∈ collectExternPreds retSpec effects := by
  cases retSpec with
  | simple _ _ pred =>
    simp only [collectExternPreds]
    exact List.mem_append_right _ (List.mem_map_of_mem hmem)
  | nestedFn _ _ _ _ =>
    simp only [collectExternPreds]
    exact List.mem_map_of_mem hmem
  | nestedPfn _ _ _ =>
    simp only [collectExternPreds]
    exact List.mem_map_of_mem hmem

/-- Inner helper: all cells in the result of the impure extern effect loop respect tm.
    The `hloop` parameter uses the exact form produced by simp-unfolding `applyFnTClosure`. -/
private lemma extern_loop_allCellsRespect
    (tm : TagMeaning)
    (effects : List Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (allPreds : List SyntaxPredicate)
    (pc : Poison)
    (memEnv memEnv' : MemoryTypeEnv)
    (hcompat : TagMappingRespectsTagMeaning tm tagMapping allPreds unifiedEnv)
    (hpreds : ∀ effect, effect ∈ effects → effect.pred ∈ allPreds)
    (hinit : ∀ l qt, memEnv.lookup l = some qt → QTypRespectsTagMeaning tm qt)
    (hloop : forIn effects memEnv (fun effect r =>
        match applyExternEffect effect unifiedEnv tagMapping pc r with
        | Except.error err => Except.error err
        | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnv') :
    ∀ l qt, memEnv'.lookup l = some qt → QTypRespectsTagMeaning tm qt := by
  induction effects generalizing memEnv with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hloop
    subst hloop; exact hinit
  | cons h t ih =>
    simp only [List.forIn_cons, bind, Except.bind] at hloop
    split at hloop
    · simp at hloop
    · rename_i step heq
      split at hloop
      · -- ForInStep.done: impossible (we always produce yield)
        rename_i _b
        split at heq
        · simp at heq
        · rename_i _v _happly; simp at heq
      · rename_i memEnv1
        have happly1 : applyExternEffect h unifiedEnv tagMapping pc memEnv = .ok memEnv1 := by
          split at heq
          · simp at heq
          · rename_i v happly1
            simp only [Except.ok.injEq, ForInStep.yield.injEq] at heq; subst heq; exact happly1
        apply ih memEnv1
        · intro effect hmem; exact hpreds effect (List.Mem.tail _ hmem)
        · exact applyExternEffect_preserves_allCellsRespect tm h unifiedEnv tagMapping allPreds
            pc memEnv memEnv1 hcompat (hpreds h (List.Mem.head _)) hinit happly1
        · exact hloop

/-- Conjunct 1: all cells in the post-loop memEnv of an impure extern application
    respect tag meaning.  Only requires `hwf` (input wf) and `happly`. -/
private lemma applyFnTClosure_extern_ok_memCellsRespect_of_respects
    (tm : TagMeaning)
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
    (hcompatBatch :
      ∀ (tagMapping : TagMapping) (nextTag' : Tag),
        collectAndAllocExternTags (collectExternPreds retSpec effects) result2.nextTag' =
          .ok (tagMapping, nextTag') →
        TagMappingRespectsTagMeaning tm tagMapping (collectExternPreds retSpec effects)
          (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩))
    (declaredArgQt : QTyp)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r) :
    ∀ (l : Loc) (qt : QTyp), r.memEnv'.lookup l = some qt → QTypRespectsTagMeaning tm qt := by
  cases fuel with
  | zero => simp [applyFnTClosure] at happly
  | succ n =>
    simp only [applyFnTClosure, bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    simp only [pure, Except.pure] at happly
    split at happly
    · simp at happly
    · rename_i allocRes hcollect
      -- The for loop: extract memEnvLoop and hloop
      -- Setup: unifiedEnv and hcompat
      set unifiedEnv := (VarTypeEnv.ofCaptured capturedEnv).update x
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred }
        with hunifiedEnv
      have hcompat : TagMappingRespectsTagMeaning tm allocRes.1
          (collectExternPreds retSpec effects) unifiedEnv :=
        by
          simpa [unifiedEnv] using hcompatBatch allocRes.1 allocRes.2 hcollect
      -- Initial cells from hwf
      have hinit : ∀ l qt, result2.memEnv'.lookup l = some qt → QTypRespectsTagMeaning tm qt := by
        intro l qt hlookup qtDeep k d hinq hqd
        rcases hwf with ⟨hwf'⟩
        exact hwf' (GuardDescInEnvsDeep.intro qtDeep k d
          (QTypInEnvs.inMem ctx.varEnv result2.memEnv' l qtDeep qt hlookup hinq) hqd)
      split at happly
      · simp at happly
      · rename_i memEnvLoop hloop
        -- All three retSpec cases use `r.memEnv' = memEnvLoop`
        have hmem_eq : r.memEnv' = memEnvLoop := by
          split at happly
          · -- simple: happly involves resolveSyntaxPred and returnSpecToQTyp
            split at happly
            · simp at happly
            · rename_i _vpred _heqpred
              split at happly
              · simp at happly
              · simp only [Except.ok.injEq] at happly
                subst happly; rfl
          · -- nestedFn
            split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
          · -- nestedPfn
            split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
        rw [hmem_eq]
        -- Normalize hloop to the form expected by extern_loop_allCellsRespect
        have hloop' : forIn effects result2.memEnv' (fun effect r =>
            match applyExternEffect effect unifiedEnv allocRes.1
                (joinPoison p (joinPoison p1 ctx.pc)) r with
            | Except.error err => Except.error err
            | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnvLoop := by
          convert hloop using 2
          funext effect r
          split <;> simp_all
        -- Apply the loop invariant
        exact extern_loop_allCellsRespect tm effects unifiedEnv allocRes.1
          (collectExternPreds retSpec effects) (joinPoison p (joinPoison p1 ctx.pc))
          result2.memEnv' memEnvLoop
          hcompat
          (fun effect hmem => effect_pred_mem_collectExternPreds retSpec effects effect hmem)
          hinit hloop'

-- --------------------------------------------------------------------------
-- Pointwise poison origin for impure extern effects.
-- --------------------------------------------------------------------------

/-- Per-step pointwise: if a location has a clean lookup in the post-effect memEnv
    under `pc = true`, the same location was clean in the pre-effect memEnv.
    Justification: under `pc = true`, every written cell gets
    `poison = joinPoison true _ = true`, so a clean hit cannot have been written. -/
private lemma applyExternEffect_preserves_clean_lookup
    (effect : Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (memEnv memEnv' : MemoryTypeEnv)
    (happly : applyExternEffect effect unifiedEnv tagMapping true memEnv = .ok memEnv')
    (l : Loc) (qt : QTyp)
    (hlookup : memEnv'.lookup l = some qt)
    (hpoison : qt.poison = false) :
    ∃ qt_in, memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
  unfold applyExternEffect at happly
  simp only [bind, Except.bind] at happly
  split at happly
  · rename_i qtVar _hlookup_var
    split at happly
    · rename_i ls _hls
      split at happly
      · simp at happly
      · rename_i resolvedPred _hresolve
        simp [pure, Except.pure] at happly
        subst happly
        -- The effect update mirrors assignment.  Under `pc = true` the written
        -- cells carry `storedPoison = joinPoison true _ = true`, so any post-cell
        -- that is unpoisoned must not have been written.
        by_cases hmem : l ∈ ls
        · -- Written cell: poison = true, contradicting hpoison
          have hprops := assign_memEnv_formula_lookup_mem_props memEnv ls _ _ l hmem qt hlookup
          have hpt := hprops.1 (by simp [joinPoison])
          rw [hpt] at hpoison
          exact absurd hpoison (by decide)
        · -- Not written: lookup unchanged
          exact ⟨qt, (assign_memEnv_formula_lookup_eq_of_not_mem memEnv ls _ _ l hmem).symm.trans hlookup,
            hpoison⟩
    · simp at happly
  · simp at happly

/-- Guard-tag analogue of `applyExternEffect_preserves_clean_lookup`.  Under
    `pc = true`, `applyExternEffect` erases the stored predicate to `noPred`,
    so any post-cell with a guard tag must not have been written.  The
    conclusion gives the *same* `qt` (a lookup equality), which lets
    downstream consumers transport any property of `qt` (etyp, regime, etc.)
    backward without re-deriving it. -/
private lemma applyExternEffect_preserves_guard_lookup
    (effect : Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (memEnv memEnv' : MemoryTypeEnv)
    (happly : applyExternEffect effect unifiedEnv tagMapping true memEnv = .ok memEnv')
    (l : Loc) (qt : QTyp) (k : Tag)
    (hlookup : memEnv'.lookup l = some qt)
    (htag : qtypGuardTag qt = some k) :
    memEnv.lookup l = some qt := by
  unfold applyExternEffect at happly
  simp only [bind, Except.bind] at happly
  split at happly
  · rename_i qtVar _hlookup_var
    split at happly
    · rename_i ls _hls
      split at happly
      · simp at happly
      · rename_i resolvedPred _hresolve
        simp [pure, Except.pure] at happly
        subst happly
        -- Under `pc = true` the effect update erases the stored predicate to
        -- `noPred`, so any post-cell with a guard tag must not have been written.
        by_cases hmem : l ∈ ls
        · -- Written cell: stored pred is noPred, contradicting htag
          have hprops := assign_memEnv_formula_lookup_mem_props memEnv ls _ _ l hmem qt hlookup
          have hpred := hprops.2 (by simp)
          simp [qtypGuardTag, hpred] at htag
        · -- Not written: lookup unchanged
          exact (assign_memEnv_formula_lookup_eq_of_not_mem memEnv ls _ _ l hmem).symm.trans hlookup
    · simp at happly
  · simp at happly

/-- Pointwise loop: the `forIn` effect loop in `applyFnTClosure` (impure extern), under
    `pc = true`, preserves clean-lookup at a fixed location `l` (backward direction). -/
private lemma forIn_effects_loop_preserves_clean_lookup
    (effects : List Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (memEnv memEnv' : MemoryTypeEnv)
    (hloop : forIn effects memEnv (fun effect r =>
        match applyExternEffect effect unifiedEnv tagMapping true r with
        | Except.error err => Except.error err
        | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnv')
    (l : Loc) (qt : QTyp)
    (hlookup : memEnv'.lookup l = some qt)
    (hpoison : qt.poison = false) :
    ∃ qt_in, memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
  induction effects generalizing memEnv with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hloop
    subst hloop; exact ⟨qt, hlookup, hpoison⟩
  | cons h t ih =>
    simp only [List.forIn_cons, bind, Except.bind] at hloop
    split at hloop
    · simp at hloop
    · rename_i step heq
      split at hloop
      · -- ForInStep.done: impossible (we always produce yield)
        rename_i _b
        split at heq
        · simp at heq
        · rename_i _v _; simp at heq
      · rename_i memEnv1
        have happly1 : applyExternEffect h unifiedEnv tagMapping true memEnv = .ok memEnv1 := by
          split at heq
          · simp at heq
          · rename_i v happly1
            simp only [Except.ok.injEq, ForInStep.yield.injEq] at heq; subst heq; exact happly1
        rcases ih memEnv1 hloop with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
        exact applyExternEffect_preserves_clean_lookup h unifiedEnv tagMapping
          memEnv memEnv1 happly1 l qt_mid hlookup_mid hpoison_mid

/-- Poison origin for impure externs: under a dirty extern-effect pc, a clean
    cell in the post-extern memEnv traces back pointwise to a clean cell in
    `result2.memEnv'` (the pre-extern memEnv passed into `applyFnTClosure`).
    The remaining step from `result2.memEnv'` to `ctx.memEnv` is handled at
    the call site by the IH-based `hbackToCtx_poison` helper. -/
lemma applyFnTClosure_extern_ok_memEnv_poison_origin_of_effect_pc_true
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (declaredArgQt : QTyp)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r)
    (heffectPc : joinPoison p (joinPoison p1 ctx.pc) = true)
    (l : Loc) (qt_out : QTyp)
    (hlookup : r.memEnv'.lookup l = some qt_out)
    (hpoison : qt_out.poison = false) :
    ∃ qt_mid, result2.memEnv'.lookup l = some qt_mid ∧ qt_mid.poison = false := by
  cases fuel with
  | zero => simp [applyFnTClosure] at happly
  | succ n =>
    simp only [applyFnTClosure, bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    simp only [pure, Except.pure] at happly
    split at happly
    · simp at happly
    · rename_i allocRes _hcollect
      set unifiedEnv := (VarTypeEnv.ofCaptured capturedEnv).update x
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred }
        with _hunifiedEnv
      split at happly
      · simp at happly
      · rename_i memEnvLoop hloop
        -- All three retSpec cases use `r.memEnv' = memEnvLoop`
        have hmem_eq : r.memEnv' = memEnvLoop := by
          split at happly
          · split at happly
            · simp at happly
            · rename_i _vpred _heqpred
              split at happly
              · simp at happly
              · simp only [Except.ok.injEq] at happly
                subst happly; rfl
          · split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
          · split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
        rw [hmem_eq] at hlookup
        -- Normalize hloop to the simpler form consumed by the loop lemma
        have hloop' : forIn effects result2.memEnv' (fun effect r =>
            match applyExternEffect effect unifiedEnv allocRes.1
                (joinPoison p (joinPoison p1 ctx.pc)) r with
            | Except.error err => Except.error err
            | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnvLoop := by
          convert hloop using 2
          funext effect r
          split <;> simp_all
        rw [heffectPc] at hloop'
        exact forIn_effects_loop_preserves_clean_lookup effects unifiedEnv allocRes.1
          result2.memEnv' memEnvLoop hloop' l qt_out hlookup hpoison

/-- Specialisation for callers that know the caller pc is dirty (`ctx.pc = true`). -/
lemma applyFnTClosure_extern_ok_memEnv_poison_origin
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    {declaredArgQt : QTyp}
    (r : TypeResult)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r)
    (hpc : ctx.pc = true)
    (l : Loc) (qt_out : QTyp)
    (hlookup : r.memEnv'.lookup l = some qt_out)
    (hpoison : qt_out.poison = false) :
    ∃ qt_mid, result2.memEnv'.lookup l = some qt_mid ∧ qt_mid.poison = false :=
  applyFnTClosure_extern_ok_memEnv_poison_origin_of_effect_pc_true
    ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuel id x retSpec effects capturedEnv
    r declaredArgQt happly (by simp [hpc, joinPoison]) l qt_out hlookup hpoison

/-- Guard-tag analogue of `forIn_effects_loop_preserves_clean_lookup`.  Returns
    a lookup equality (same `qt`) so downstream consumers can transport any
    property of `qt` backward through the loop. -/
private lemma forIn_effects_loop_preserves_guard_lookup
    (effects : List Effect)
    (unifiedEnv : VarTypeEnv)
    (tagMapping : TagMapping)
    (memEnv memEnv' : MemoryTypeEnv)
    (hloop : forIn effects memEnv (fun effect r =>
        match applyExternEffect effect unifiedEnv tagMapping true r with
        | Except.error err => Except.error err
        | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnv')
    (l : Loc) (qt : QTyp) (k : Tag)
    (hlookup : memEnv'.lookup l = some qt)
    (htag : qtypGuardTag qt = some k) :
    memEnv.lookup l = some qt := by
  induction effects generalizing memEnv with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hloop
    subst hloop; exact hlookup
  | cons h t ih =>
    simp only [List.forIn_cons, bind, Except.bind] at hloop
    split at hloop
    · simp at hloop
    · rename_i step heq
      split at hloop
      · rename_i _b
        split at heq
        · simp at heq
        · rename_i _v _; simp at heq
      · rename_i memEnv1
        have happly1 : applyExternEffect h unifiedEnv tagMapping true memEnv = .ok memEnv1 := by
          split at heq
          · simp at heq
          · rename_i v happly1
            simp only [Except.ok.injEq, ForInStep.yield.injEq] at heq; subst heq; exact happly1
        have hlookup_mid : memEnv1.lookup l = some qt := ih memEnv1 hloop
        exact applyExternEffect_preserves_guard_lookup h unifiedEnv tagMapping
          memEnv memEnv1 happly1 l qt k hlookup_mid htag

/-- Guard origin for impure externs: under a dirty extern-effect pc, a guard-tagged
    cell in the post-extern memEnv traces back pointwise to a guard-tagged
    cell in `result2.memEnv'`.  The remaining step from `result2.memEnv'`
    to `ctx.memEnv` is handled at the call site (parallel to the poison
    origin lemma).  Guard provenance is derived structurally here rather than
    trusted as an extern-typing assumption. -/
lemma applyFnTClosure_extern_ok_memEnv_guard_origin_of_effect_pc_true
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (declaredArgQt : QTyp)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r)
    (heffectPc : joinPoison p (joinPoison p1 ctx.pc) = true)
    (l : Loc) (qt_out : QTyp) (k : Tag)
    (hlookup : r.memEnv'.lookup l = some qt_out)
    (htag : qtypGuardTag qt_out = some k) :
    result2.memEnv'.lookup l = some qt_out := by
  cases fuel with
  | zero => simp [applyFnTClosure] at happly
  | succ n =>
    simp only [applyFnTClosure, bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    simp only [pure, Except.pure] at happly
    split at happly
    · simp at happly
    · rename_i allocRes _hcollect
      set unifiedEnv := (VarTypeEnv.ofCaptured capturedEnv).update x
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred }
        with _hunifiedEnv
      split at happly
      · simp at happly
      · rename_i memEnvLoop hloop
        have hmem_eq : r.memEnv' = memEnvLoop := by
          split at happly
          · split at happly
            · simp at happly
            · rename_i _vpred _heqpred
              split at happly
              · simp at happly
              · simp only [Except.ok.injEq] at happly
                subst happly; rfl
          · split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
          · split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly; subst happly; rfl
        rw [hmem_eq] at hlookup
        have hloop' : forIn effects result2.memEnv' (fun effect r =>
            match applyExternEffect effect unifiedEnv allocRes.1
                (joinPoison p (joinPoison p1 ctx.pc)) r with
            | Except.error err => Except.error err
            | Except.ok v => Except.ok (ForInStep.yield v)) = Except.ok memEnvLoop := by
          convert hloop using 2
          funext effect r
          split <;> simp_all
        rw [heffectPc] at hloop'
        exact forIn_effects_loop_preserves_guard_lookup effects unifiedEnv allocRes.1
          result2.memEnv' memEnvLoop hloop' l qt_out k hlookup htag

/-- Specialisation for callers that know the caller pc is dirty (`ctx.pc = true`). -/
lemma applyFnTClosure_extern_ok_memEnv_guard_origin
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    {declaredArgQt : QTyp}
    (r : TypeResult)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r)
    (hpc : ctx.pc = true)
    (l : Loc) (qt_out : QTyp) (k : Tag)
    (hlookup : r.memEnv'.lookup l = some qt_out)
    (htag : qtypGuardTag qt_out = some k) :
    result2.memEnv'.lookup l = some qt_out :=
  applyFnTClosure_extern_ok_memEnv_guard_origin_of_effect_pc_true
    ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuel id x retSpec effects capturedEnv
    r declaredArgQt happly (by simp [hpc, joinPoison]) l qt_out k hlookup htag

/-- Conjunct 2: the result QTyp of an impure extern application respects tag meaning.
    Requires `hcapTm` (captured env entries respect tm) and `hargTm` (arg QTyp respects tm)
    in addition to `hwf` and `happly`. -/
private lemma applyFnTClosure_extern_ok_qualTypeRespects_of_respects
    (tm : TagMeaning)
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (_hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
    (hcompatBatch :
      ∀ (tagMapping : TagMapping) (nextTag' : Tag),
        collectAndAllocExternTags (collectExternPreds retSpec effects) result2.nextTag' =
          .ok (tagMapping, nextTag') →
        TagMappingRespectsTagMeaning tm tagMapping (collectExternPreds retSpec effects)
          (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩))
    (declaredArgQt : QTyp)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r) :
    QTypRespectsTagMeaning tm r.qualType := by
  cases fuel with
  | zero => simp [applyFnTClosure] at happly
  | succ n =>
    simp only [applyFnTClosure, bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    simp only [pure, Except.pure] at happly
    split at happly
    · simp at happly
    · rename_i allocRes hcollect
      split at happly
      · simp at happly
      · rename_i _memEnvLoop _hloop
        -- Establish the tag mapping compat for each retSpec case
        cases retSpec with
        | simple typ poison spred =>
          -- collectExternPreds (simple ...) effects = [spred] ++ effects.map(·.pred)
          simp only [] at happly
          split at happly
          · simp at happly
          · rename_i resolvedPred hresolved
            split at happly
            · simp at happly
            · rename_i retres hret
              obtain ⟨retQt, nextLoc'⟩ := retres
              simp only [Except.ok.injEq] at happly; subst happly
              have hcompat : TagMappingRespectsTagMeaning tm allocRes.1
                  (collectExternPreds (ExternReturn.simple typ poison spred) effects)
                  ((VarTypeEnv.ofCaptured capturedEnv).update x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) :=
                by
                  simpa using hcompatBatch allocRes.1 allocRes.2 hcollect
              have hspredMem : spred ∈
                  collectExternPreds (ExternReturn.simple typ poison spred) effects :=
                by simp only [collectExternPreds]; exact List.Mem.head _
              have hpredTm := resolveSyntaxPred_respectsTagMeaning tm spred
                ((VarTypeEnv.ofCaptured capturedEnv).update x
                  ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
                allocRes.1
                (collectExternPreds (ExternReturn.simple typ poison spred) effects)
                resolvedPred hcompat hspredMem hresolved
              have hretPred := returnSpecToQTyp_pred_preserves typ poison resolvedPred result2.nextLoc'
                retQt nextLoc' hret
              have hretNotFun := returnSpecToQTyp_etyp_nonFunction typ poison resolvedPred
                result2.nextLoc' retQt nextLoc' hret
              obtain ⟨ret_e, ret_p, ret_pred⟩ := retQt
              simp only at hretNotFun hpredTm hretPred
              simp only [normalizeAppResultByProvenance]
              split
              · intro qt' k d hinq hqd
                have hEq := QTypInQTyp_eq_of_nonFunctionTarget hinq hretNotFun
                subst hEq; simp [qtypGuardDesc?] at hqd
              · rw [← hretPred] at hpredTm
                intro qt' k d hinq hqd
                have hEq := QTypInQTyp_eq_of_nonFunctionTarget hinq hretNotFun
                subst hEq
                cases ret_pred with
                | noPred => simp [qtypGuardDesc?] at hqd
                | guardOnly _ => simp [qtypGuardDesc?] at hqd
                | guardClosure k0 arg pb cap =>
                  simp [qtypGuardDesc?] at hqd
                  rcases hqd with ⟨hk, hd⟩; subst hk; subst hd
                  exact hpredTm k0 arg pb cap rfl
        | nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
          simp only [] at happly
          split at happly
          · simp at happly
          · next v hresolve =>
            simp only [Except.ok.injEq] at happly; subst happly; simp only
            simp only [normalizeAppResultByProvenance]
            split <;> {
              intro qt' k d hinq hqd
              exact (QTypRespectsTagMeaning_noPred_poison_transport tm _ ctx.pc _
                (QTypRespectsTagMeaning_fn_extern_ofCaptured tm capturedEnv x
                  ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  innerId innerArg innerArgTyp (parseReturnType innerRet) ctx.pc innerRet innerEffects v.1
                  hcapTm hargTm)) hinq hqd }
        | nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
          simp only [] at happly
          split at happly
          · simp at happly
          · next v hresolve =>
            simp only [Except.ok.injEq] at happly; subst happly; simp only
            simp only [normalizeAppResultByProvenance]
            split <;> {
              intro qt' k d hinq hqd
              exact (QTypRespectsTagMeaning_noPred_poison_transport tm _ ctx.pc _
                (QTypRespectsTagMeaning_pfn_extern_ofCaptured tm capturedEnv x
                  ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  innerId innerArg innerArgTyp (parseReturnType innerRet) ctx.pc innerRet v.1 innerCaptures
                  hcapTm hargTm)) hinq hqd }

/-- Canonical tag-meaning extension for a successful impure extern closure
    application.  The allocated batch is `collectExternPreds retSpec effects`;
    the memory-loop and result-`QTyp` obligations are discharged by the
    structural `_of_respects` helpers above. -/
lemma applyFnTClosure_extern_canonical_batch
    (tm : TagMeaning)
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (result2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
    (r : TypeResult)
    (hwf : wfTagMeaningCtx tm (ctxAfter ctx result2))
    (h_bounded : TagMeaningBounded tm result2.nextTag')
    (hcapTm : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt)
    (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
    (declaredArgQt : QTyp)
    (happly : applyFnTClosure (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 fuel = .ok r) :
    ∃ (tm' : TagMeaning) (tagMapping : TagMapping) (nextTag' : Tag),
      let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      ExternBatchTagMeaningExtension tm result2.nextTag' tagMapping
        (collectExternPreds retSpec effects) unifiedEnv nextTag' tm' ∧
      WithinLog tm r.tagLog' tm' ∧
      TagMeaningBounded tm' r.nextTag' ∧
      wfTagMeaningCtx tm' (ctxAfter ctx r) ∧
      QTypRespectsTagMeaning tm' r.qualType := by
  -- Preserve the original closure-equation for the downstream `_of_respects` helpers,
  -- which re-unfold `applyFnTClosure` themselves.
  have happly0 := happly
  cases fuel with
  | zero => simp [applyFnTClosure] at happly
  | succ n =>
    simp only [applyFnTClosure, bind, Except.bind] at happly
    -- Leading argument-condition gate: throw branch is impossible on .ok.
    split at happly
    · simp at happly
    rename_i hgate
    rw [Bool.not_eq_true, Bool.not_eq_false'] at hgate
    simp only [pure, Except.pure] at happly
    cases hcollect : collectAndAllocExternTags (collectExternPreds retSpec effects)
        result2.nextTag' with
    | error err => simp [hcollect] at happly
    | ok allocRes =>
      obtain ⟨tagMapping, nextTag'⟩ := allocRes
      let unifiedEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      obtain ⟨tm', hbatch⟩ :=
        ExternBatchTagMeaningExtension.canonical_general tm
          (collectExternPreds retSpec effects) unifiedEnv tagMapping
          result2.nextTag' nextTag' h_bounded hcollect
      have hcompatBatch :
          ∀ (tagMapping' : TagMapping) (nextTag'' : Tag),
            collectAndAllocExternTags (collectExternPreds retSpec effects) result2.nextTag' =
              .ok (tagMapping', nextTag'') →
            TagMappingRespectsTagMeaning tm' tagMapping'
              (collectExternPreds retSpec effects) unifiedEnv := by
        intro tagMapping' nextTag'' hcollect'
        rw [hcollect] at hcollect'
        cases hcollect'
        exact ExternBatchTagMeaningExtension.respects hbatch
      have hwf' : wfTagMeaningCtx tm' (ctxAfter ctx result2) :=
        wfTagMeaningCtx_mono (ExternBatchTagMeaningExtension.extends_tm hbatch) hwf
      have hcapTm' : ∀ (name : Name) (qt : QTyp), (name, qt) ∈ capturedEnv →
          QTypRespectsTagMeaning tm' qt := by
        intro name qt hmem
        exact QTypRespectsTagMeaning_mono
          (ExternBatchTagMeaningExtension.extends_tm hbatch) (hcapTm name qt hmem)
      have hargTm' :
          QTypRespectsTagMeaning tm' ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
        QTypRespectsTagMeaning_mono (ExternBatchTagMeaningExtension.extends_tm hbatch) hargTm
      refine ⟨tm', tagMapping, nextTag', hbatch, ?_, ?_, ?_, ?_⟩
      · have hlog_eq : r.tagLog' = externTagLog (collectExternPreds retSpec effects)
            unifiedEnv tagMapping := by
          simp only [hcollect] at happly
          split at happly
          · simp at happly
          · cases retSpec <;> simp only [] at happly
            · split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · simp only [Except.ok.injEq] at happly
                  rw [← happly]
            · split at happly
              · simp at happly
              · simp only [Except.ok.injEq] at happly
                rw [← happly]
            · split at happly
              · simp at happly
              · simp only [Except.ok.injEq] at happly
                rw [← happly]
        rw [hlog_eq]
        exact hbatch.within
      · have htag_eq : r.nextTag' = nextTag' := by
          simp only [hcollect] at happly
          split at happly
          · simp at happly
          · cases retSpec <;> simp only [] at happly
            · split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · simp only [Except.ok.injEq] at happly
                  rw [← happly]
            · split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                rw [← happly]
                have : v.2 = nextTag' := by
                  simp only [resolveArgCondQTyp, bind, Except.bind] at hresolve
                  split at hresolve
                  · simp at hresolve
                  · simp only [pure, Except.pure, Except.ok.injEq] at hresolve; rw [← hresolve]
                exact this
            · split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                rw [← happly]
                have : v.2 = nextTag' := by
                  simp only [resolveArgCondQTyp, bind, Except.bind] at hresolve
                  split at hresolve
                  · simp at hresolve
                  · simp only [pure, Except.pure, Except.ok.injEq] at hresolve; rw [← hresolve]
                exact this
        rw [htag_eq]
        exact ExternBatchTagMeaningExtension.bounded hbatch
      · unfold wfTagMeaningCtx
        simp only [ctxAfter]
        exact EnvRespectsTagMeaning.intro fun ⟨qt, _, _, hqte, hqd⟩ => by
          cases hqte with
          | inVar =>
              rename_i xv qtRoot hqtinqt hlookup_var
              rcases hwf' with ⟨hwf''⟩
              exact hwf'' (GuardDescInEnvsDeep.intro qt _ _
                (QTypInEnvs.inVar ctx.varEnv result2.memEnv' xv qt qtRoot hlookup_var hqtinqt)
                hqd)
          | inMem =>
              rename_i l qtRoot hqtinqt hlookup_mem
              exact
                (applyFnTClosure_extern_ok_memCellsRespect_of_respects
                  (tm := tm') (ctx := ctx) (st1 := st1) (st2 := st2) (p := p)
                  (p1 := p1) (argEtyp := argEtyp) (argPoison := argPoison)
                  (argPred := argPred) (result2 := result2) (fuel := Nat.succ n)
                  (id := id) (x := x) (retSpec := retSpec) (effects := effects)
                  (capturedEnv := capturedEnv) (r := r) (declaredArgQt := declaredArgQt)
                  hwf' hcompatBatch happly0)
                  l qtRoot hlookup_mem hqtinqt hqd
      · exact
          applyFnTClosure_extern_ok_qualTypeRespects_of_respects
            (tm := tm') (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
            (result2 := result2) (fuel := Nat.succ n) (id := id) (x := x) (retSpec := retSpec)
            (effects := effects) (capturedEnv := capturedEnv) (r := r) (declaredArgQt := declaredArgQt)
            hwf' hcapTm' hargTm' hcompatBatch happly0

/-- Helper: surfaceSpecToQTyp preserves EnvRespectsTagMeaning (only adds noPred int cell). -/
private lemma surfaceSpecToQTyp_preserves_EnvRespectsTagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : Predicate)
    (qt : QTyp) (ctx' : TypeContext)
    (hwf : EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv)
    (hsurface : surfaceSpecToQTyp typ poison pred ctx = .ok (qt, ctx')) :
    EnvRespectsTagMeaning tm ctx.varEnv ctx'.memEnv := by
  cases typ with
  | int =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsurface
    rw [← hsurface.2]; exact hwf
  | bool =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsurface
    rw [← hsurface.2]; exact hwf
  | unit =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsurface
    rw [← hsurface.2]; exact hwf
  | string =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsurface
    rw [← hsurface.2]; exact hwf
  | ref _ =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp [bind, Except.bind] at hsurface
  | arrow _ _ =>
    simp only [surfaceSpecToQTyp] at hsurface
    simp [Except.map, Functor.map] at hsurface

/-- Structural preservation: typecheckExternVal preserves wfTagMeaningCtx.
    This follows from the fact that surfaceSpecToQTyp only modifies memEnv
    by inserting a noPred cell (for ref int), which trivially respects any TagMeaning. -/
private lemma typecheckExternVal_preserves_wfTagMeaningCtx
  (tm : TagMeaning) (ctx : TypeContext) (id : ExternId) (typ : Typ) (poison : Bool)
  (pred : SyntaxPredicate) (fuel : Nat) (res : TypeResult)
  (hwf : wfTagMeaningCtx tm ctx)
  (htc : typecheckExternVal ctx id typ poison pred fuel = .ok res) :
  wfTagMeaningCtx tm (ctxAfter ctx res) := by
  obtain ⟨_, _, _, resolvedPred, ⟨qt, ctx'⟩, _, _, hsurface, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  simp only [wfTagMeaningCtx, ctxAfter]
  exact surfaceSpecToQTyp_preserves_EnvRespectsTagMeaning
    tm ctx typ poison resolvedPred qt ctx' hwf hsurface

/-- `typecheckExternVal` constructs a genuine post-allocation tag table for
    its successful result.  This is the extern-value case needed by
    `typecheck_preserves_predSatLaws` (`TypecheckInduction.lean`). -/
lemma typecheckExternVal_canonical_batch
    (tm : TagMeaning) (ctx : TypeContext) (id : ExternId)
    (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (fuel : Nat)
    (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (htc : typecheckExternVal ctx id typ poison pred fuel = .ok res) :
    ∃ (tm' : TagMeaning) (tagMapping : TagMapping) (nextTag' : Tag),
      ExternBatchTagMeaningExtension tm ctx.nextTag tagMapping [pred] ctx.varEnv nextTag' tm' ∧
      WithinLog tm res.tagLog' tm' ∧
      IsCanonicalExtension tm ctx (Expr.externVal id typ poison pred) res tm' := by
  obtain ⟨_, tagMapping, nextTag', _, _, halloc, _, _, rfl⟩ := typecheckExternVal_ok_shape htc
  obtain ⟨tm', hbatch⟩ :=
    ExternBatchTagMeaningExtension.canonical_general tm [pred] ctx.varEnv
      tagMapping ctx.nextTag nextTag' h_bounded halloc
  refine ⟨tm', tagMapping, nextTag', hbatch, hbatch.within, ?_, ?_, ?_, ?_⟩
  · exact ExternBatchTagMeaningExtension.extends_tm hbatch
  · simpa using ExternBatchTagMeaningExtension.bounded hbatch
  · exact
      wfTagMeaningCtx_mono
        (ExternBatchTagMeaningExtension.extends_tm hbatch)
        (typecheckExternVal_preserves_wfTagMeaningCtx tm ctx id typ poison pred fuel _ hwf htc)
  · exact
      typecheckExternVal_QTypRespectsTagMeaning_of_respects tm' ctx id typ poison pred fuel _
        (fun _tagMapping _nextTag' halloc' => by
          simp only [halloc] at halloc'
          cases halloc'
          exact ExternBatchTagMeaningExtension.respects hbatch)
        htc

/-- Helper: surfaceSpecToQTyp preserves memEnv at existing locations when wfTypeContext holds.
    For non-ref types, memEnv is unchanged. For ref int, the new allocation is at ctx.nextLoc
    which is distinct from all existing locations. -/
private lemma surfaceSpecToQTyp_preserves_existing_lookup
    (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : Predicate)
    (qt : QTyp) (ctx' : TypeContext)
    (_hwf : wfTypeContext ctx)
    (hsurf : surfaceSpecToQTyp typ poison pred ctx = .ok (qt, ctx'))
    (l : Loc) (qt_out : QTyp)
    (_hpre : ctx.memEnv.contains l)
    (hlookup : ctx'.memEnv.lookup l = some qt_out) :
    ctx.memEnv.lookup l = some qt_out := by
  simp only [surfaceSpecToQTyp] at hsurf
  cases typ with
  | int | bool | unit | string =>
    simp [pure, Except.pure, bind, Except.bind] at hsurf
    obtain ⟨_, rfl⟩ := hsurf; exact hlookup
  | ref _ =>
    simp [bind, Except.bind] at hsurf
  | arrow _ _ =>
    simp [Except.map, Functor.map] at hsurf

/-- `typecheckExternVal` preserves the lookup-origin property for existing
    memEnv entries: with `wfTypeContext ctx`, existing entries are unchanged,
    and the regime changes only at the fresh tags of the declaration, which no
    existing entry carries (`TagBoundedCtx`). -/
lemma typecheckExternVal_preserves_lookup_origin
  (ctx : TypeContext) (id : ExternId) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheckExternVal ctx id typ poison pred fuel = .ok res)
  (hwf : wfTypeContext ctx) (hbnd : TagBoundedCtx ctx)
  (_hpc : ctx.pc = true) (l : Loc) (qt_out : QTyp)
  (hpre : ctx.memEnv.contains l)
  (hlookup : res.memEnv'.lookup l = some qt_out) :
  (qt_out.poison = false → ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false) ∧
  ∀ (k : Tag),
    qtypGuardTag qt_out = some k →
    res.regime'.lookup? k = some true →
    qt_out.etyp.isFunctionType = false →
    ∃ qt_in,
      ctx.memEnv.lookup l = some qt_in ∧
      qtypGuardTag qt_in = some k ∧
      ctx.regime.lookup? k = some true ∧
      qt_in.etyp.isFunctionType = false := by
  obtain ⟨_, tagMapping, _, resolvedPred, surfResult, halloc, _, hsurf, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  -- res.memEnv' = surfResult.2.memEnv, and existing entries are preserved
  have hlookup' := surfaceSpecToQTyp_preserves_existing_lookup
    ctx typ poison resolvedPred surfResult.1 surfResult.2 hwf hsurf l qt_out hpre hlookup
  refine ⟨fun h => ⟨qt_out, hlookup', h⟩,
    fun k htag hreg hnotfun => ⟨qt_out, hlookup', htag, ?_, hnotfun⟩⟩
  -- The policy changes the regime only at fresh tags, above every existing guard tag.
  rcases applyExternRegimePolicy_lookup_spec ctx.regime id ctx.externRegime tagMapping k with
    heq | ⟨idx, hidx⟩
  · rw [← heq]; exact hreg
  · exact absurd (collectAndAllocExternTags_mapping_values_ge _ _ _ _ halloc idx k hidx)
      (Nat.not_le.mpr (TagBoundedCtx_memEnv_guardTag_lt hbnd hlookup' htag))

end ExternTagMeaningSig
