/-
  TypecheckInduction.lean — typecheck-preservation and lookup-origin inductions.

  Heavy `typecheckExpr` structural inductions that sit BELOW `StepFR` in the import
  graph: `joinTypeResults`/`typecheckExpr` preservation of `regimeConsistentWithCtx`
  (+ masked / MaskedTagsAbsent variants), `typecheck_preserves_predSatLaws`, the
  `*_byIH` closure-application bridges, the `joinTypeResults_lookup_member_*`
  transport lemmas, and the clean lookup-origin family. Imports `ExternTagMeaning`
  because the `*_byIH` and lookup-origin lemmas consume its captured-extern
  `QTypRespectsTagMeaning` machinery.
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
import LeanProofs.ExternTagMeaning
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet.Lemmas

open List
open List.Mem
open Std
open scoped MemoryTypeEnv


-- ── Standalone helper lemmas (explicit binders) ──

lemma List_lookup_some_mem
    {α β : Type} [BEq α] [LawfulBEq α]
    (x : α) (y : β) (l : List (α × β)) :
    List.lookup x l = some y → (x, y) ∈ l := by
  intro hlookup
  induction l with
  | nil =>
      simp [List.lookup] at hlookup
  | cons hd tl ih =>
      cases hd with
      | mk x' y' =>
          by_cases hEq : x == x'
          · simp [List.lookup, hEq] at hlookup
            have hx : x = x' := LawfulBEq.eq_of_beq hEq
            subst hx
            subst hlookup
            simp
          · simp [List.lookup, hEq] at hlookup
            exact List.mem_cons_of_mem _ (ih hlookup)

lemma list_fold_joinPredicates_init_noPred
  (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) :
  ((xs.foldl
      (fun acc l0 =>
        match env[l0]? with
        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
        | none => (acc.1, Predicate.noPred))
      (storedPoison, Predicate.noPred)).2) = Predicate.noPred := by
  induction xs generalizing storedPoison with
  | nil =>
      simp
  | cons x xs ih =>
      cases hget : env[x]? with
      | none =>
          simpa [List.foldl, hget] using ih storedPoison
      | some qtX =>
          simpa [List.foldl, hget, joinPredicates] using ih (joinPoison storedPoison qtX.poison)

lemma typecheckDeref_etyp_int
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref ctx e fuel = .ok res → res.qualType.etyp = ETyp.int := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e fuel' with
      | error err =>
          simp [h_tc1] at h_typecheck
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt : result1.qualType with
          | mk etyp poisonRef predRef =>
              rw [h_qt] at h_typecheck
              simp at h_typecheck
              cases etyp <;> simp at h_typecheck
              -- only ref case can succeed; in ref branch split on ls.isEmpty
              rename_i ls
              split at h_typecheck
              · -- ls.isEmpty = true: typecheck throws, contradicts .ok res
                cases h_typecheck
              · -- ls.isEmpty = false: foldM runs, then if poisonRef / else match mergedPred
                cases h_fold : LocSet.foldM (m := Except String) ls (false, none)
                  (fun (accPoison, accPred?) l => do
                    match result1.memEnv'.lookup l with
                    | some qt =>
                        pure (joinPoison accPoison qt.poison,
                          match accPred? with
                          | none => some qt.pred
                          | some p => some (joinPredicates p qt.pred))
                    | none => throw (toString "Location " ++ toString l ++ toString " not found in memory environment"))
                with
                | error err =>
                    erw [h_fold] at h_typecheck
                    cases h_typecheck
                | ok v =>
                    erw [h_fold] at h_typecheck
                    by_cases h_poison : poisonRef = true
                    · simp [h_poison] at h_typecheck
                      cases h_typecheck
                      rfl
                    · simp [h_poison] at h_typecheck
                      cases hpred : v.2.getD Predicate.noPred with
                      | noPred =>
                          simp [hpred, pure, Except.pure] at h_typecheck
                          cases h_typecheck
                          rfl
                      | guardOnly k =>
                          simp [hpred] at h_typecheck
                          cases htag : result1.tagEnv'[k]? with
                          | none => simp [htag, pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                          | some tv => cases tv with | mk b _ => cases b <;> simp [htag, pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      | guardClosure k _ _ _ =>
                          simp [hpred] at h_typecheck
                          cases htag : result1.tagEnv'[k]? with
                          | none => simp [htag, pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                          | some tv => cases tv with | mk b _ => cases b <;> simp [htag, pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl

-- fold function used by typecheckDeref (exposed for local reasoning)
-- Uses MemoryTypeEnv.lookup which returns Option QTyp (etyp = int for memory).
def derefFoldF (mem : MemoryTypeEnv) (acc : Bool × Option Predicate) (l : Loc) :
    Except String (Bool × Option Predicate) :=
  match mem.lookup l with
  | some qt =>
      Except.ok
        (joinPoison acc.1 qt.poison,
          match acc.2 with
          | none => some qt.pred
          | some p => some (joinPredicates p qt.pred))
  | none =>
      throw
        (toString "Location " ++ toString l ++ toString " not found in memory environment")

private lemma list_foldlM_derefFoldF_pred_eq_guardClosure_from_some
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (accPoison : Bool) (p0 : Predicate) (joined : Bool) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    List.foldlM (derefFoldF mem) (accPoison, some p0) xs = Except.ok (joined, pred?) →
    pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
    p0 = Predicate.guardClosure k arg_name pred_body var_env ∧
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  induction xs with
  | nil =>
      intro accPoison p0 joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      have hpred? : pred? = some p0 := by
        simpa using hfold.2.symm
      subst hpred?
      have hp0 : p0 = Predicate.guardClosure k arg_name pred_body var_env := by
        simpa using hpred
      refine ⟨hp0, ?_⟩
      intro l hl
      cases hl
  | cons x xs ih =>
      intro accPoison p0 joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem (accPoison, some p0) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          -- Unpack the head cell: derefFoldF uses mem.lookup which returns Option QTyp.
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_pred : acc'.2 = some (joinPredicates p0 qt.pred) := by
                simpa using (congrArg Prod.snd hfx).symm
              have htail_fold :
                  List.foldlM (derefFoldF mem) (acc'.1, some (joinPredicates p0 qt.pred)) xs =
                    Except.ok (joined, pred?) := by
                cases acc' with
                | mk accPoison' accPred' =>
                    have haccPred : accPred' = some (joinPredicates p0 qt.pred) := by
                      simpa using hacc'_pred
                    simpa [haccPred] using hfold
              have hih :=
                ih acc'.1 (joinPredicates p0 qt.pred) joined pred? k arg_name pred_body var_env htail_fold hpred
              have hjoin := joinPredicates_eq_guardClosure (p := p0) (q := qt.pred)
                (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env) hih.1
              refine ⟨hjoin.1, ?_⟩
              intro l hl
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · refine ⟨qt, hlookup, ?_⟩
                exact hjoin.2
              · exact hih.2 l hltail

private lemma list_foldlM_derefFoldF_pred_eq_guardClosure
  (mem : MemoryTypeEnv) :
  ∀ (xs : List Loc) (joined : Bool) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    List.foldlM (derefFoldF mem) (false, (none : Option Predicate)) xs = Except.ok (joined, pred?) →
    pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
    (∀ l ∈ xs, ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  cases xs with
  | nil =>
      intro joined pred? k arg_name pred_body var_env _hfold _hpred l hl
      cases hl
  | cons x xs =>
      intro joined pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : derefFoldF mem (false, none) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : mem.lookup x with
          | none =>
              simp [derefFoldF, hlookup] at hfx
          | some qt =>
              simp [derefFoldF, hlookup] at hfx
              have hacc'_pred : acc'.2 = some qt.pred := by
                  simpa using (congrArg Prod.snd hfx).symm
              have htail_fold :
                    List.foldlM (derefFoldF mem) (acc'.1, some qt.pred) xs =
                      Except.ok (joined, pred?) := by
                cases acc' with
                | mk accPoison' accPred' =>
                    have haccPred : accPred' = some qt.pred := by
                      simpa using hacc'_pred
                    simpa [haccPred] using hfold
              have hres :=
                list_foldlM_derefFoldF_pred_eq_guardClosure_from_some mem xs acc'.1 qt.pred joined pred?
                  k arg_name pred_body var_env htail_fold hpred
              have hhead_pred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env :=
                hres.1
              have htail_cells := hres.2
              intro l hl
              rcases (List.mem_cons.mp hl) with rfl | hltail
              · refine ⟨qt, hlookup, hhead_pred⟩
              · exact htail_cells l hltail

lemma deref_foldM_pred_eq_guardClosure
  (mem : MemoryTypeEnv) (ls : LocSet) (joined : Bool) (pred? : Option Predicate)
  (hfold : LocSet.foldM ls (false, (none : Option Predicate)) (derefFoldF mem) =
    Except.ok (joined, pred?))
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv}
  (hpred : pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env)
  (l : Loc) (hl : l ∈ ls) :
  ∃ qt, mem.lookup l = some qt ∧ qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact list_foldlM_derefFoldF_pred_eq_guardClosure mem ls.toList joined pred? k arg_name pred_body var_env hfold hpred l hl'

lemma typecheckDeref_qtypRespects
  (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat)
  (res res1 : TypeResult)
  (hwfTmAfter : wfTagMeaningCtx tm (ctxAfter ctx res1))
  (htc1 : typecheckExpr ctx e fuel = .ok res1)
  (htc : typecheckDeref ctx e (Nat.succ fuel) = .ok res) :
  QTypRespectsTagMeaning tm res.qualType := by
  have hres_etyp_int : res.qualType.etyp = ETyp.int :=
    typecheckDeref_etyp_int ctx e (Nat.succ fuel) res htc
  have hnotfun : res.qualType.etyp.isFunctionType = false := by
    simp [hres_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  intro qt' k d hinq hqd
  have hself : qt' = res.qualType := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
  subst hself
  cases hqres : res.qualType with
  | mk etyp poison pred =>
      have hetyp_int : etyp = ETyp.int := by simpa [hqres] using hres_etyp_int
      cases hpred_res : pred with
      | noPred =>
          have : False := by
            simp [qtypGuardDesc?, hqres, hpred_res] at hqd
          exact False.elim this
      | guardOnly k0 =>
          have : False := by
            simp [qtypGuardDesc?, hqres, hpred_res] at hqd
          exact False.elim this
      | guardClosure k0 arg_name pred_body var_env =>
          have hpair : (k0, { argName := arg_name, body := pred_body, capEnv := var_env }) = (k, d) := by
            exact Option.some.inj (by simpa [qtypGuardDesc?, hqres, hpred_res] using hqd)
          cases hpair
          have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
            have htc' := htc
            simp [typecheckDeref, htc1, bind, Except.bind] at htc'
            cases hq1 : res1.qualType with
            | mk etyp1 poison1 pred1 =>
                cases etyp1 <;> simp [hq1] at htc'
                rename_i ls
                exact ⟨ls, rfl⟩
          rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
          have hls_nonempty : ls0 ≠ ∅ := by
            intro hls
            have htc_bad := htc
            cases hq1 : res1.qualType with
            | mk etyp1 poison1 pred1 =>
                have h_etyp1 : etyp1 = ETyp.ref ls0 := by
                  simpa [hq1] using hres1_etyp0
                simp [typecheckDeref, htc1, hq1, h_etyp1, hls, bind, Except.bind] at htc_bad
          have hexists_l : ∃ l, l ∈ ls0 := by
            by_contra hno
            push Not at hno
            exact hls_nonempty ((Std.ExtTreeSet.eq_empty_iff_forall_not_mem).2 hno)
          rcases hexists_l with ⟨l0, hl0⟩
          have htc' := htc
          cases hq1 : res1.qualType with
          | mk etyp1 poison1 pred1 =>
              have h_etyp1 : etyp1 = ETyp.ref ls0 := by
                simpa [hq1] using hres1_etyp0
              simp [typecheckDeref, htc1, hq1, h_etyp1, bind, Except.bind] at htc'
              by_cases hls : ls0 = ∅
              · simp [hls] at htc'
              · simp [hls] at htc'
                cases hfold :
                    ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                      match res1.memEnv'.lookup l with
                      | some qt =>
                          pure (joinPoison x.1 qt.poison,
                            match x.2 with
                            | none => some qt.pred
                            | some p => some (joinPredicates p qt.pred))
                      | none =>
                          throw (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                | error err =>
                    erw [hfold] at htc'
                    cases htc'
                | ok v =>
                    erw [hfold] at htc'
                    cases hp : poison1 with
                    | true =>
                        simp [hp, pure, Except.pure] at htc'
                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                        have : False := by
                          simp [hqres, hpred_res] at hpred_out
                        exact False.elim this
                    | false =>
                        simp [hp] at htc'
                        cases hpred_fold : v.2.getD Predicate.noPred with
                        | noPred =>
                            simp [hpred_fold, pure, Except.pure] at htc'
                            have hpred_out : res.qualType.pred = Predicate.noPred := by
                              simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                            have : False := by
                              simp [hqres, hpred_res] at hpred_out
                            exact False.elim this
                        | guardOnly k1 =>
                            cases htagopt : res1.tagEnv'.get? k1 with
                            | some tv =>
                                cases tv with
                                | mk b deps =>
                                    have htagopt' : res1.tagEnv'[k1]? = some ⟨b, deps⟩ := by
                                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                    cases hb : b with
                                    | true =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                                    | false =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                            | none =>
                                have htagopt' : res1.tagEnv'[k1]? = none := by
                                  simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                simp [hpred_fold, htagopt', pure, Except.pure] at htc'
                                have hpred_out : res.qualType.pred = Predicate.guardOnly k1 := by
                                  simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                have : False := by
                                  simp [hqres, hpred_res] at hpred_out
                                exact False.elim this
                        | guardClosure k1 arg1 body1 env1 =>
                            cases htagopt : res1.tagEnv'.get? k1 with
                            | some tv =>
                                cases tv with
                                | mk b deps =>
                                    have htagopt' : res1.tagEnv'[k1]? = some ⟨b, deps⟩ := by
                                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                    cases hb : b with
                                    | true =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                                    | false =>
                                        simp [hb, hpred_fold, htagopt', pure, Except.pure] at htc'
                                        have hpred_out : res.qualType.pred = Predicate.noPred := by
                                          simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                        have : False := by
                                          simp [hqres, hpred_res] at hpred_out
                                        exact False.elim this
                            | none =>
                                have htagopt' : res1.tagEnv'[k1]? = none := by
                                  simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                                simp [hpred_fold, htagopt', pure, Except.pure] at htc'
                                have hpred_out : res.qualType.pred = Predicate.guardClosure k1 arg1 body1 env1 := by
                                  simpa using congrArg (fun r : TypeResult => r.qualType.pred) (Eq.symm htc')
                                have hpred_eq_pred : pred = Predicate.guardClosure k1 arg1 body1 env1 := by
                                  simpa [hqres] using hpred_out
                                have hclos_eq :
                                    Predicate.guardClosure k1 arg1 body1 env1 =
                                      Predicate.guardClosure k arg_name pred_body var_env := by
                                  calc
                                    Predicate.guardClosure k1 arg1 body1 env1 = pred := by symm; exact hpred_eq_pred
                                    _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_res
                                injection hclos_eq with hk1 harg1 hbody1 henv1
                                subst k1
                                subst harg1
                                subst hbody1
                                subst henv1
                                have hpred_eq :
                                    v.2.getD Predicate.noPred = Predicate.guardClosure k arg1 body1 env1 := by
                                  simp [hpred_fold]
                                obtain ⟨qtCell, hlookupCell, hpredCell⟩ :=
                                  deref_foldM_pred_eq_guardClosure res1.memEnv' ls0 v.1 v.2 hfold hpred_eq l0 hl0
                                have hlookup_ctx :
                                    (ctxAfter ctx res1).memEnv.lookup l0 = some qtCell := by
                                  simp only [ctxAfter]
                                  exact hlookupCell
                                have hqtTm :
                                    QTypRespectsTagMeaning tm qtCell :=
                                  wfTagMeaningCtx_mem_lookup_qtyp tm (ctxAfter ctx res1) l0 qtCell hwfTmAfter hlookup_ctx
                                exact hqtTm (QTypInQTyp.self qtCell) (by simp [qtypGuardDesc?, hpredCell])

section TypecheckInductionSig
variable (predSat : PredSat) (tm : TagMeaning) (fuel : Nat)

-- Shared typecheck preservation lemmas for tag meaning/regime consistency.
lemma applyFnTClosure_regular_structure
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate) (result2 : TypeResult) (fuel : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (_happly : applyFnTClosure (FnTClosure.regular x body tenv) st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok first) :
  ∃ fuelBody, fuel = Nat.succ fuelBody := by
  cases fuel with
  | zero =>
      simp [applyFnTClosure] at _happly
  | succ fuelBody =>
      exact ⟨fuelBody, rfl⟩

-- Inversion for regular closures: successful application exposes the body typing
-- derivation and successful return-type erasure check.
lemma applyFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyFnTClosure (FnTClosure.regular x body tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        bindEnv := BindEnv.bindParam tenv x result2.nextBind'
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextBind := result2.nextBind' + 1
        nextLoc := result2.nextLoc'
        regime := result2.regime'
        externRefAllowed := false
        declaredExternRefs := result2.declared' } body fuelBody = .ok result3 ∧
    isErasureOf st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
        declared' := result2.declared' } := by
  unfold applyFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        bindEnv := BindEnv.bindParam tenv x result2.nextBind'
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextBind := result2.nextBind' + 1
        nextLoc := result2.nextLoc'
        regime := result2.regime'
        externRefAllowed := false
        declaredExternRefs := result2.declared' } body fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isErasureOf st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isErasureOf st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isErasureOf st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
                        declared' := result2.declared' } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
                      declared' := result2.declared' } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

lemma applyClosuresThreaded_ok_mem_output_exists_input
  {α : Type}
  (applyOne : α → Tag × Loc → Nat → TypecheckM TypeResult)
  {xs : List α} {cursor : Tag × Loc} {bn : Nat} {results : List TypeResult} {y : TypeResult}
  (hthread : applyClosuresThreaded applyOne xs cursor bn = .ok results)
  (hmem : y ∈ results) :
  ∃ x, x ∈ xs ∧ ∃ cursor' bn', applyOne x cursor' bn' = .ok y := by
  induction xs generalizing cursor bn results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      cases hmem
  | cons x xs ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne x cursor bn with
      | error _ =>
          simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne xs (first.nextTag', first.nextLoc')
              first.nextBind' with
          | error _ =>
              simp [hrest] at hthread
          | ok rest =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              simp at hmem
              cases hmem with
              | inl hy =>
                  subst hy
                  exact ⟨x, by simp, cursor, bn, hfirst⟩
              | inr hy =>
                  rcases ih hrest hy with ⟨x', hx', cursor', bn', happly⟩
                  exact ⟨x', by simp [hx'], cursor', bn', happly⟩

/-- Tag analog of `applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound`: each output
    closure result comes from an input whose cursor tag is `≥ base`, given that each applied closure
    only grows the tag (`base ≤ cursor.1 → base ≤ result.nextTag'`). -/
lemma applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
  {α : Type}
  (applyOne : α → Tag × Loc → Nat → TypecheckM TypeResult)
  (base : Tag)
  (hmono : ∀ item cursor bn result,
    base ≤ cursor.1 → applyOne item cursor bn = .ok result → base ≤ result.nextTag')
  {xs : List α} {cursor : Tag × Loc} {bn : Nat} {results : List TypeResult} {y : TypeResult}
  (hbase : base ≤ cursor.1)
  (hthread : applyClosuresThreaded applyOne xs cursor bn = .ok results)
  (hmem : y ∈ results) :
  ∃ x, x ∈ xs ∧ ∃ cursor' bn', base ≤ cursor'.1 ∧ applyOne x cursor' bn' = .ok y := by
  induction xs generalizing cursor bn results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      cases hmem
  | cons x xs ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne x cursor bn with
      | error _ => simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne xs (first.nextTag', first.nextLoc')
              first.nextBind' with
          | error _ => simp [hrest] at hthread
          | ok rest =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              simp at hmem
              cases hmem with
              | inl hy =>
                  subst hy
                  exact ⟨x, by simp, cursor, bn, hbase, hfirst⟩
              | inr hy =>
                  have hbase' : base ≤ first.nextTag' := hmono x cursor bn first hbase hfirst
                  rcases ih hbase' hrest hy with ⟨x', hx', cursor', bn', hcursor', happly⟩
                  exact ⟨x', by simp [hx'], cursor', bn', hcursor', happly⟩

/-- Combined tag+loc cursor-bound (output→input): each threaded output closure result comes from an
    input whose cursor satisfies both `baseTag ≤ cursor'.1` and `baseLoc ≤ cursor'.2`. -/
private lemma applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bounds
  {α : Type}
  (applyOne : α → Tag × Loc → Nat → TypecheckM TypeResult)
  (baseTag : Tag) (baseLoc : Loc)
  (hmono : ∀ item cursor bn result,
    baseTag ≤ cursor.1 → baseLoc ≤ cursor.2 → applyOne item cursor bn = .ok result →
    baseTag ≤ result.nextTag' ∧ baseLoc ≤ result.nextLoc')
  {xs : List α} {cursor : Tag × Loc} {bn : Nat} {results : List TypeResult} {y : TypeResult}
  (hbaseTag : baseTag ≤ cursor.1) (hbaseLoc : baseLoc ≤ cursor.2)
  (hthread : applyClosuresThreaded applyOne xs cursor bn = .ok results)
  (hmem : y ∈ results) :
  ∃ x, x ∈ xs ∧ ∃ cursor' bn', baseTag ≤ cursor'.1 ∧ baseLoc ≤ cursor'.2 ∧
    applyOne x cursor' bn' = .ok y := by
  induction xs generalizing cursor bn results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      cases hmem
  | cons x xs ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne x cursor bn with
      | error _ => simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne xs (first.nextTag', first.nextLoc')
              first.nextBind' with
          | error _ => simp [hrest] at hthread
          | ok rest =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              simp at hmem
              cases hmem with
              | inl hy =>
                  subst hy
                  exact ⟨x, by simp, cursor, bn, hbaseTag, hbaseLoc, hfirst⟩
              | inr hy =>
                  obtain ⟨hbt, hbl⟩ := hmono x cursor bn first hbaseTag hbaseLoc hfirst
                  rcases ih hbt hbl hrest hy with ⟨x', hx', cursor', bn', hct', hcl', happly⟩
                  exact ⟨x', by simp [hx'], cursor', bn', hct', hcl', happly⟩

private lemma QTypRespectsTagMeaning_of_arrow_captured_lookup
  (tm : TagMeaning)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun y : Name) (body : Expr) (σcap : CapturedVarEnv) (qtCap : QTyp)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls)
  (hlookup : σcap.lookup y = some qtCap) :
  QTypRespectsTagMeaning tm qtCap := by
  intro qt k d hinq hqd
  rw [CapturedVarEnv.lookup_eq] at hlookup
  obtain ⟨⟨q, n⟩, hl, hq⟩ := Option.map_eq_some_iff.1 hlookup
  simp only at hq
  subst hq
  have hcapMem : (y, q, n) ∈ σcap := List_lookup_some_mem y (q, n) σcap hl
  have hroot :
      QTypInQTyp q qtRes :=
    QTypInQTyp.in_arrow q qtRes st1 st2 p tcls
      (FnTClosure.regular xFun body σcap) y (n := n)
      hetyp hmem (by simpa [fnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt q qtRes hinq hroot) hqd

private lemma wfTagMeaningCtx_ofCaptured_from_arrow
  (tm : TagMeaning) (ctxMem : TypeContext)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun : Name) (body : Expr) (σcap : CapturedVarEnv)
  (hctxTm : wfTagMeaningCtx tm ctxMem)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls) :
  wfTagMeaningCtx tm { ctxMem with varEnv := VarTypeEnv.ofCaptured σcap } := by
  unfold wfTagMeaningCtx at hctxTm ⊢
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hm⟩
  cases hinq with
  | inVar _ _ y _qt qtRoot hlookup hinqRoot =>
      have hlookupCap : σcap.lookup y = some qtRoot :=
        list_lookup_of_ofCaptured_lookup σcap y qtRoot (by simpa using hlookup)
      have hrootTm : QTypRespectsTagMeaning tm qtRoot :=
        QTypRespectsTagMeaning_of_arrow_captured_lookup
          tm qtRes st1 st2 p tcls xFun y body σcap qtRoot
          hresTm hetyp hmem hlookupCap
      exact hrootTm hinqRoot hm
  | inMem _ _ l _qt qtRoot hlookup hinqRoot =>
      exact hctxTm.1 (GuardDescInEnvsDeep.intro qt k d
        (QTypInEnvs.inMem ctxMem.varEnv ctxMem.memEnv l qt qtRoot hlookup hinqRoot) hm)

lemma wfTagMeaningCtx_closure_body
  (tm : TagMeaning) (ctx : TypeContext) (result1 : TypeResult)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (xFun : Name) (body : Expr) (σcap : CapturedVarEnv)
  (xArg : Name) (argQt : QTyp)
  (hctxTm : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem : FnTClosure.regular xFun body σcap ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm argQt) :
  wfTagMeaningCtx tm
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } := by
  let ctxCap : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.ofCaptured σcap }
  have hctxCapTm : wfTagMeaningCtx tm ctxCap := by
    have hcapTm :
        wfTagMeaningCtx tm { (ctxAfter ctx result1) with varEnv := VarTypeEnv.ofCaptured σcap } :=
      wfTagMeaningCtx_ofCaptured_from_arrow
        tm (ctxAfter ctx result1) qtRes st1 st2 p tcls xFun body σcap
        hctxTm hresTm hetyp hmem
    simpa [ctxCap, ctxAfter] using! hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

private lemma QTypRespectsTagMeaning_of_parrow_captured_lookup
  (tm : TagMeaning)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun y : Name) (pbody : PExpr) (σcap : CapturedVarEnv) (qtCap : QTyp)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls)
  (hlookup : σcap.lookup y = some qtCap) :
  QTypRespectsTagMeaning tm qtCap := by
  intro qt k d hinq hqd
  rw [CapturedVarEnv.lookup_eq] at hlookup
  obtain ⟨⟨q, n⟩, hl, hq⟩ := Option.map_eq_some_iff.1 hlookup
  simp only at hq
  subst hq
  have hcapMem : (y, q, n) ∈ σcap := List_lookup_some_mem y (q, n) σcap hl
  have hroot :
      QTypInQTyp q qtRes :=
    QTypInQTyp.in_parrow q qtRes st1 st2 p tcls
      (PFnTClosure.regular xFun pbody σcap) y (n := n)
      hetyp hmem (by simpa [pfnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt q qtRes hinq hroot) hqd

private lemma wfTagMeaningCtx_ofCaptured_from_parrow
  (tm : TagMeaning) (ctxMem : TypeContext)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun : Name) (pbody : PExpr) (σcap : CapturedVarEnv)
  (hctxTm : wfTagMeaningCtx tm ctxMem)
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls) :
  wfTagMeaningCtx tm { ctxMem with varEnv := VarTypeEnv.ofCaptured σcap } := by
  unfold wfTagMeaningCtx at hctxTm ⊢
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hm⟩
  cases hinq with
  | inVar _ _ y _qt qtRoot hlookup hinqRoot =>
      have hlookupCap : σcap.lookup y = some qtRoot :=
        list_lookup_of_ofCaptured_lookup σcap y qtRoot (by simpa using hlookup)
      have hrootTm : QTypRespectsTagMeaning tm qtRoot :=
        QTypRespectsTagMeaning_of_parrow_captured_lookup
          tm qtRes st1 st2 p tcls xFun y pbody σcap qtRoot
          hresTm hetyp hmem hlookupCap
      exact hrootTm hinqRoot hm
  | inMem _ _ l _qt qtRoot hlookup hinqRoot =>
      exact hctxTm.1 (GuardDescInEnvsDeep.intro qt k d
        (QTypInEnvs.inMem ctxMem.varEnv ctxMem.memEnv l qt qtRoot hlookup hinqRoot) hm)

lemma wfTagMeaningCtx_pclosure_body
  (tm : TagMeaning) (ctx : TypeContext) (result1 : TypeResult)
  (qtRes : QTyp) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (xFun : Name) (pbody : PExpr) (σcap : CapturedVarEnv)
  (xArg : Name) (argQt : QTyp)
  (hctxTm : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm : QTypRespectsTagMeaning tm qtRes)
  (hetyp : qtRes.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem : PFnTClosure.regular xFun pbody σcap ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm argQt) :
  wfTagMeaningCtx tm
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } := by
  let ctxCap : TypeContext :=
    { ctx with
      memEnv := result1.memEnv'
      tagEnv := result1.tagEnv'
      nextLoc := result1.nextLoc'
      nextTag := result1.nextTag'
      regime := result1.regime'
      varEnv := VarTypeEnv.ofCaptured σcap }
  have hctxCapTm : wfTagMeaningCtx tm ctxCap := by
    have hcapTm :
        wfTagMeaningCtx tm { (ctxAfter ctx result1) with varEnv := VarTypeEnv.ofCaptured σcap } :=
      wfTagMeaningCtx_ofCaptured_from_parrow
        tm (ctxAfter ctx result1) qtRes st1 st2 p tcls xFun pbody σcap
        hctxTm hresTm hetyp hmem
    simpa [ctxCap, ctxAfter] using! hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

private lemma regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag
    (masked : Tag → Prop)
    (ctx₁ ctx₂ : TypeContext)
    (htag : ctx₂.tagEnv = ctx₁.tagEnv)
    (hreg : ctx₂.regime = ctx₁.regime)
    (_hnt : ctx₂.nextTag = ctx₁.nextTag)
    (h : regimeConsistentWithCtxMasked masked ctx₁) :
    regimeConsistentWithCtxMasked masked ctx₂ := by
  simp only [regimeConsistentWithCtxMasked] at h ⊢
  rw [htag, hreg]
  exact h

lemma joinTypeResults_tagEnvConsistentWithRegime'
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        tagEnvConsistentWithRegime acc.2.2.2.2.1 acc.2.2.2.2.2.1 →
        (∀ r ∈ rs', regimeConsistentWithCtx (ctxAfter ctx r)) →
        tagEnvConsistentWithRegime acc'.2.2.2.2.1 acc'.2.2.2.2.2.1 := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx :
                regimeConsistentWithCtx (ctxAfter ctx x) :=
              hrs x (by simp)
            have hx_tag : tagEnvConsistentWithRegime x.tagEnv' x.regime' := by
              simpa [regimeConsistentWithCtx, ctxAfter] using hx
            have hacc1 :
                tagEnvConsistentWithRegime acc1.2.2.2.2.1 acc1.2.2.2.2.2.1 := by
              simpa [acc1] using
                (tagEnvConsistentWithRegime_join
                  acc.2.2.2.2.1 x.tagEnv' acc.2.2.2.2.2.1 x.regime'
                  hacc hx_tag)
            have hrs_tail :
                ∀ r ∈ xs, regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro r hr
              exact hrs r (by simp [hr])
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_tag :
                  tagEnvConsistentWithRegime first.tagEnv' first.regime' := by
                simpa [regimeConsistentWithCtx, ctxAfter] using h_first
              exact
                h_fold_tag rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag')
                  a hfold h_first_tag h_rest

private lemma joinTypeResults_tagEnvConsistentWithRegimeMasked'
  (masked : Tag → Prop)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtxMasked masked (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtxMasked masked (ctxAfter ctx r)) :
  tagEnvConsistentWithRegimeMasked masked (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        tagEnvConsistentWithRegimeMasked masked acc.2.2.2.2.1 acc.2.2.2.2.2.1 →
        (∀ r ∈ rs', regimeConsistentWithCtxMasked masked (ctxAfter ctx r)) →
        tagEnvConsistentWithRegimeMasked masked acc'.2.2.2.2.1 acc'.2.2.2.2.2.1 := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx :
                regimeConsistentWithCtxMasked masked (ctxAfter ctx x) :=
              hrs x (by simp)
            have hx_tag : tagEnvConsistentWithRegimeMasked masked x.tagEnv' x.regime' := by
              simpa [regimeConsistentWithCtxMasked, ctxAfter] using hx
            have hacc1 :
                tagEnvConsistentWithRegimeMasked masked acc1.2.2.2.2.1 acc1.2.2.2.2.2.1 := by
              simpa [acc1] using
                (tagEnvConsistentWithRegimeMasked_join
                  masked acc.2.2.2.2.1 x.tagEnv' acc.2.2.2.2.2.1 x.regime'
                  hacc hx_tag)
            have hrs_tail :
                ∀ r ∈ xs, regimeConsistentWithCtxMasked masked (ctxAfter ctx r) := by
              intro r hr
              exact hrs r (by simp [hr])
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_tag :
                  tagEnvConsistentWithRegimeMasked masked first.tagEnv' first.regime' := by
                simpa [regimeConsistentWithCtxMasked, ctxAfter] using h_first
              exact
                h_fold_tag rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_tag h_rest

private lemma joinTypeResults_regimeConsistentWithCtxMasked
  (masked : Tag → Prop)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtxMasked masked (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtxMasked masked (ctxAfter ctx r)) :
  regimeConsistentWithCtxMasked masked (ctxAfter ctx res) := by
  exact joinTypeResults_tagEnvConsistentWithRegimeMasked' masked ctx first rest res h_join h_first h_rest

private lemma MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
    {masked : Tag → Prop} {ctx₁ ctx₂ : TypeContext}
    (htag : ctx₂.tagEnv = ctx₁.tagEnv)
    (h : MaskedTagsAbsentFromTrueTagEnv masked ctx₁) :
    MaskedTagsAbsentFromTrueTagEnv masked ctx₂ := by
  intro k deps hmasked hget
  exact h k deps hmasked (by simpa [htag] using hget)

private lemma joinTypeResults_MaskedTagsAbsentFromTrueTagEnv'
  (masked : Tag → Prop)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r)) :
  MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx res) := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        (∀ k deps, masked k → acc.2.2.2.2.1.get? k = some ⟨true, deps⟩ → False) →
        (∀ r ∈ rs', MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r)) →
        ∀ k deps, masked k → acc'.2.2.2.2.1.get? k = some ⟨true, deps⟩ → False := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx :
                MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx x) :=
              hrs x (by simp)
            have hx_tag :
                ∀ k deps, masked k → x.tagEnv'.get? k = some ⟨true, deps⟩ → False := by
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hx
            have hacc1 :
                ∀ k deps, masked k → acc1.2.2.2.2.1.get? k = some ⟨true, deps⟩ → False := by
              simpa [acc1] using
                (MaskedTagsAbsentFromTrueTagEnvs_join hacc hx_tag)
            have hrs_tail :
                ∀ r ∈ xs, MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r) := by
              intro r hr
              exact hrs r (by simp [hr])
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_tag :
                  ∀ k deps, masked k → first.tagEnv'.get? k = some ⟨true, deps⟩ → False := by
                simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using h_first
              have hres :=
                h_fold_tag rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_tag h_rest
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hres

private lemma typecheckExpr_preserves_regimeConsistentWithCtxMasked_main :
    ∀ (fuel : Nat) (masked : Tag → Prop) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    regimeConsistentWithCtxMasked masked ctx →
    typecheck ctx e fuel = .ok res →
    regimeConsistentWithCtxMasked masked (ctxAfter ctx res) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro masked ctx e res hreg htc
    have IH' :
        ∀ m < fuel, ∀ (masked' : Tag → Prop) (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
          regimeConsistentWithCtxMasked masked' ctx' →
          typecheck ctx' e' m = .ok res' →
          regimeConsistentWithCtxMasked masked' (ctxAfter ctx' res') := by
      intro m hm masked' ctx' e' res' hreg' htc'
      exact IH m hm masked' ctx' e' res' hreg' htc'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc
        simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | bool _b =>
            unfold typecheckBool at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | unit =>
            unfold typecheckUnit at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | str _s =>
            unfold typecheckString at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | var x =>
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                cases pred with
                | noPred =>
                    simp [pure, Except.pure] at htc
                    cases htc
                    simpa [ctxAfter, regimeConsistentWithCtxMasked]
                | guardOnly k =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          simpa [ctxAfter, regimeConsistentWithCtxMasked]
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                simpa [ctxAfter, regimeConsistentWithCtxMasked]
                | guardClosure k tcls ptcls body_t =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          simpa [ctxAfter, regimeConsistentWithCtxMasked]
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | fn _ _ _ _ =>
            have hfn := typecheckFn_ok_eq htc
            subst hfn
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ =>
                simp [h_topexpr, pure, Except.pure] at htc
                subst htc
                simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | externVal id typ poison pred =>
            have htc' : typecheckExternVal ctx id typ poison pred fuel' = .ok res := htc
            obtain ⟨_, tagMapping, _, _, _, _, _, _, rfl⟩ := typecheckExternVal_ok_shape htc'
            simp only [ctxAfter, regimeConsistentWithCtxMasked, tagEnvConsistentWithRegimeMasked]
            intro k deps hk
            rcases installReturnGuard_get?_cases _ _ _ _ k _ hk with hold | ⟨hR, _⟩
            · rcases hreg k deps hold with hm | hR
              · exact Or.inl hm
              · exact Or.inr (applyExternRegimePolicy_lookup_preserve_some _ _ _ _ k true hR)
            · exact Or.inr hR
        | externRef _ _ _ _ _ =>
            simp only [typecheckExternRef] at htc
            simp [Bind.bind, Except.bind, pure, Except.pure] at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            cases htc
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | externFn id arg argTyp argPoison argPred retSpec effects cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternFn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec effects res htc
            rw [hres]
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | externPfn id arg argTyp argPoison argPred retSpec cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternPfn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec res htc
            rw [hres]
            simpa [ctxAfter, regimeConsistentWithCtxMasked]
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, htag, _, hnextTag, hreg', _, _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH ⊢
            rw [htag, hreg']; exact hIH
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH ⊢
            rw [htag, hreg']; exact hIH
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, _, _, _, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH ⊢
            rw [htag, hreg']; exact hIH
        | op e1 op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
            rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, _, htag, _, hnextTag, hregime', _, _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtxMasked masked (updateCtxFromResult ctx result1) := by
              apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            have hIH2 := IH' (fuel' - 1) (by omega) masked (updateCtxFromResult ctx result1) e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH2 ⊢
            rw [htag, hregime']; exact hIH2
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', res, htc1, hctx', htc2, rfl⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtxMasked masked ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok res := by simpa using! htc2
            exact IH' (fuel' - 1) (by omega) masked ctx' e2 res hreg_mid htc2'
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, htag, _, hnextTag, hregime', _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtxMasked masked ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter ctx result1)
              · simp [ctxAfter]
              · simp [ctxAfter]
              · simp [ctxAfter]
              · exact hIH1
            have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok result2 := by simpa using! htc2
            have hIH2 := IH' (fuel' - 1) (by omega) masked ctx' e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH2 ⊢
            rw [htag, hregime']; exact hIH2
        | assign e1 e2 =>
            unfold typecheckAssign at htc
            cases fuel' with
            | zero => simp at htc
            | succ fuel'' =>
                simp only [bind, Except.bind] at htc
                cases h_tc1 : typecheckExpr ctx e1 fuel'' with
                | error _ => simp [h_tc1] at htc
                | ok result1 =>
                    simp only [h_tc1] at htc
                    have htc1' : typecheck ctx e1 fuel'' = .ok result1 := by simpa using! h_tc1
                    have hIH1 := IH' fuel'' (by omega) masked ctx e1 result1 hreg htc1'
                    cases h_qt1 : result1.qualType with
                    | mk etyp1 p1 pred1 =>
                        rw [h_qt1] at htc
                        simp at htc
                        cases etyp1 <;> simp at htc
                        case ref ls =>
                            let memEnv2 := result1.memEnv'
                            let tagEnv2 := result1.tagEnv'
                            let nextLoc2 := result1.nextLoc'
                            let nextTag2 := result1.nextTag'
                            let regime2 := result1.regime'
                            let ctx2 : TypeContext :=
                              { pc := ctx.pc, regime := regime2, memEnv := memEnv2, varEnv := ctx.varEnv, bindEnv := ctx.bindEnv,
                                tagEnv := tagEnv2, nextLoc := nextLoc2, nextTag := nextTag2, nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                declaredExternRefs := result1.declared' }
                            have hreg2 : regimeConsistentWithCtxMasked masked ctx2 := by
                              simpa [ctxAfter, ctx2, tagEnv2, regime2, regimeConsistentWithCtxMasked] using hIH1
                            cases h_tc2 : typecheckExpr ctx2 e2 fuel'' with
                            | error err =>
                                have h_tc2_explicit :
                                    typecheckExpr
                                      { pc := ctx.pc, regime := result1.regime', memEnv := result1.memEnv',
                                        varEnv := ctx.varEnv, bindEnv := ctx.bindEnv, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                        nextTag := result1.nextTag', nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                        externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                        declaredExternRefs := result1.declared' }
                                      e2 fuel'' = .error err := by
                                  simpa [ctx2, memEnv2, tagEnv2, nextLoc2, nextTag2, regime2] using h_tc2
                                rw [h_tc2_explicit] at htc
                                simp at htc
                            | ok result2 =>
                                have htc2' : typecheck ctx2 e2 fuel'' = .ok result2 := by simpa using! h_tc2
                                have hIH2 := IH' fuel'' (by omega) masked ctx2 e2 result2 hreg2 htc2'
                                have h_tc2_explicit :
                                    typecheckExpr
                                      { pc := ctx.pc, regime := result1.regime', memEnv := result1.memEnv',
                                        varEnv := ctx.varEnv, bindEnv := ctx.bindEnv, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                        nextTag := result1.nextTag', nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                        externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                        declaredExternRefs := result1.declared' }
                                      e2 fuel'' = .ok result2 := by
                                  simpa [ctx2, memEnv2, tagEnv2, nextLoc2, nextTag2, regime2] using h_tc2
                                rw [h_tc2_explicit] at htc
                                simp at htc
                                cases h_qt2 : result2.qualType with
                                | mk etyp2 p2 pred2 =>
                                    rw [h_qt2] at htc
                                    simp at htc
                                    by_cases h_etyp2_int : etyp2 = ETyp.int
                                    · subst h_etyp2_int
                                      simp at htc
                                      cases htc
                                      simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH2 ⊢
                                      exact invalidateRegimeDeps_preserves_true_masked masked result2.tagEnv' result2.regime' ls hIH2
                                    · simp [h_etyp2_int] at htc
        | ite e1 e2 e3 =>
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            rcases hstruct with h1 | h2 | hstd
            · rcases h1 with ⟨k, deps, _, hRk, res1, _, _, res2, _, htc2, _, _hmem, htag, _, _, hregEq, _, _⟩
              let ctxT := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                     nextTag := res1.nextTag', nextBind := res1.nextBind',
                                     declaredExternRefs := res1.declared' }
              have hreg_true : regimeConsistentWithCtxMasked masked ctxT := by
                exact tagEnvConsistentWithRegimeMasked_insert_true masked ctx.tagEnv ctx.regime k deps hreg hRk
              have htc2' : typecheck ctxT e2 (fuel' - 1) = .ok res2 := by
                simpa [ctxT] using! htc2
              have hIH2 := IH' (fuel' - 1) (by omega) masked ctxT e2 res2 hreg_true htc2'
              simp only [ctxAfter, regimeConsistentWithCtxMasked, ctxT] at hIH2 ⊢
              rw [htag, hregEq]; exact hIH2
            · rcases h2 with ⟨k, deps, _, _, res1, _, _, res2, res3, _, htc3, _hmem, htag, _, _, hregEq, _, _⟩
              have hreg_false : regimeConsistentWithCtxMasked masked { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } := by
                exact tagEnvConsistentWithRegimeMasked_insert_false masked ctx.tagEnv ctx.regime k deps hreg
              let ctxF := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                     nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind',
                                     declaredExternRefs := res2.declared' }
              have htc3' : typecheck ctxF e3 (fuel' - 1) = .ok res3 := by simpa [ctxF] using! htc3
              have hIH3 := IH' (fuel' - 1) (by omega) masked ctxF e3 res3 hreg_false htc3'
              simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH3 ⊢
              rw [htag, hregEq]; exact hIH3
            · obtain ⟨_hstdCase, res1, htc1, _, res2, htc2, res3, htc3,
                _hmem, htag, _, hnextTag, hregEq, _, _, _⟩ := hstd
              have htc1' : typecheck ctx e1 (fuel' - 1) = .ok res1 := by simpa using! htc1
              have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 res1 hreg htc1'
              set ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                     nextLoc := res1.nextLoc', nextTag := res1.nextTag', nextBind := res1.nextBind', regime := res1.regime',
                                     declaredExternRefs := res1.declared' }
              have hreg1 : regimeConsistentWithCtxMasked masked ctx' := by
                apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter ctx res1)
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · exact hIH1
              set ctx'' := { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
              have hreg1' : regimeConsistentWithCtxMasked masked ctx'' := hreg1
              have htc2' : typecheck ctx'' e2 (fuel' - 1) = .ok res2 := by simpa using! htc2
              have hIH2 := IH' (fuel' - 1) (by omega) masked ctx'' e2 res2 hreg1' htc2'
              set ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind', declaredExternRefs := res2.declared' }
              have hIH1_tagEnv : tagEnvConsistentWithRegimeMasked masked res1.tagEnv' res1.regime' := by
                have h := hIH1
                simp only [ctxAfter, regimeConsistentWithCtxMasked] at h
                exact h
              have hreg2 : regimeConsistentWithCtxMasked masked ctxForE3 := by
                show tagEnvConsistentWithRegimeMasked masked ctxForE3.tagEnv ctxForE3.regime
                simp only [ctxForE3, ctx'', ctx']
                exact hIH1_tagEnv
              have htc3' : typecheck ctxForE3 e3 (fuel' - 1) = .ok res3 := by simpa using! htc3
              have hIH3 := IH' (fuel' - 1) (by omega) masked ctxForE3 e3 res3 hreg2 htc3'
              have hIH2' : regimeConsistentWithCtxMasked masked (ctxAfter ctx'' res2) := hIH2
              simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH2' hIH3 ⊢
              rw [htag, hregEq]
              exact tagEnvConsistentWithRegimeMasked_join
                  masked res2.tagEnv' res3.tagEnv' res2.regime' res3.regime' hIH2' hIH3
        | app e1 e2 =>
            simp at htc
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
                rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
                  ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩
                have hIH2 := IH' fuel'' (by omega) masked ctx e2 result2 hreg htc2
                have hreg' : regimeConsistentWithCtxMasked masked
                    (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, ctx.bindEnv, result2.tagEnv',
                      result2.nextLoc', result2.nextTag', result2.nextBind', ctx.pureCtx, ctx.externRegime,
                      ctx.externRefAllowed, result2.declared'⟩ : TypeContext) := by
                  apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter ctx result2)
                  · simp [ctxAfter]
                  · simp [ctxAfter]
                  · simp [ctxAfter]
                  · exact hIH2
                have hIH1 := IH' fuel'' (by omega) masked _ e1 result1 hreg' htc1
                have hIH1_tagEnv : tagEnvConsistentWithRegimeMasked masked result1.tagEnv' result1.regime' := by
                  have h := hIH1
                  simp [ctxAfter, regimeConsistentWithCtxMasked] at h
                  exact h
                have h_fn_closure_reg :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
                      (results : List TypeResult),
                      applyClosuresThreaded
                        (fun tcl cursor bn =>
                          applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                        tcls (result1.nextTag', result1.nextLoc') result1.nextBind' = .ok results →
                      ∀ r, r ∈ results → regimeConsistentWithCtxMasked masked (ctxAfter ctx r) := by
                  intro st1 st2 p p1 tcls results hthread r hr
                  rcases applyClosuresThreaded_ok_mem_output_exists_input
                      (applyOne := fun tcl cursor bn =>
                        applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                      (hthread := hthread) (hmem := hr) with
                    ⟨tcl, _htcl_mem, cursor, bn, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                              cases hqt3 : result3.qualType with
                              | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    have hreg_body : regimeConsistentWithCtxMasked masked
                                          { ctx with
                                            pc := joinPoison p (joinPoison p1 ctx.pc),
                                            memEnv := result1.memEnv',
                                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                            bindEnv := BindEnv.bindParam env x bn,
                                            tagEnv := result1.tagEnv', nextTag := cursor.1, nextBind := bn + 1,
                                            nextLoc := cursor.2, regime := result1.regime',
                                            externRefAllowed := false,
                                            declaredExternRefs := result1.declared' } := by
                                        exact hIH1_tagEnv
                                    have htcBody' : typecheck
                                        { ctx with
                                          pc := joinPoison p (joinPoison p1 ctx.pc),
                                          memEnv := result1.memEnv',
                                          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                            ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                          bindEnv := BindEnv.bindParam env x bn,
                                          tagEnv := result1.tagEnv', nextTag := cursor.1, nextBind := bn + 1,
                                          nextLoc := cursor.2, regime := result1.regime',
                                          externRefAllowed := false,
                                          declaredExternRefs := result1.declared' }
                                        body k = .ok result3 := by simpa using! htcBody
                                    have hIH_body := IH' k (by omega) masked _ body result3 hreg_body htcBody'
                                    simp only [ctxAfter, regimeConsistentWithCtxMasked] at hIH_body ⊢
                                    exact hIH_body
                  | extern id x retSpec effects capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                      have happly_old :
                          applyFnTClosure (.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
                            etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyFnTClosure
                        unfold applyFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      simp only [regimeConsistentWithCtxMasked, ctxAfter, tagEnvConsistentWithRegimeMasked]
                      intro k deps hk
                      -- An output `true` entry is either a surviving (invalidated)
                      -- input entry — whose regime value the effect invalidation + policy
                      -- keep — or the freshly installed return guard, which the output
                      -- regime interprets by construction.
                      rcases applyFnTClosure_extern_tagEnv_get_cases ctx st1 st2 p p1 etyp2 p2 pred2
                          rCursor r fuel'' id x retSpec effects capturedEnv declaredArgQt happly_old
                          k ⟨true, deps⟩ hk with hold | ⟨_, _, hR⟩
                      · have hk_orig : rCursor.tagEnv'.get? k = some ⟨true, deps⟩ :=
                          invalidateTagDeps_get?_some_imp _ _ k _ hold
                        rcases hIH1_tagEnv k deps hk_orig with hm | ht
                        · exact Or.inl hm
                        · refine Or.inr (applyFnTClosure_extern_regime_preserve_some
                            ctx st1 st2 p p1 etyp2 p2 pred2 rCursor r fuel''
                            id x retSpec effects capturedEnv declaredArgQt happly_old k true ?_ ht)
                          rw [hold]; exact Option.some_ne_none _
                      · exact Or.inr hR
                have h_pfn_closure_reg :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
                      (results : List TypeResult),
                      applyClosuresThreaded
                        (fun tcl cursor bn =>
                          applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                        tcls (result1.nextTag', result1.nextLoc') result1.nextBind' = .ok results →
                      ∀ r, r ∈ results → regimeConsistentWithCtxMasked masked (ctxAfter ctx r) := by
                  intro st1 st2 p p1 tcls results hthread r hr
                  rcases applyClosuresThreaded_ok_mem_output_exists_input
                      (applyOne := fun tcl cursor bn =>
                        applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                      (hthread := hthread) (hmem := hr) with
                    ⟨tcl, _htcl_mem, cursor, bn, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyPFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyPFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                            cases hqt3 : result3.qualType with
                            | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    set bodyCtx := { ctx with
                                      pc := joinPoison p (joinPoison ctx.pc p1),
                                      memEnv := result1.memEnv',
                                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                      bindEnv := BindEnv.bindParam env x bn,
                                      tagEnv := result1.tagEnv', nextTag := cursor.1, nextBind := bn + 1,
                                      pureCtx := true,
                                      nextLoc := cursor.2, regime := result1.regime',
                                      externRefAllowed := false,
                                      declaredExternRefs := result1.declared' }
                                    have hreg_body : regimeConsistentWithCtxMasked masked bodyCtx := by
                                      exact hIH1_tagEnv
                                    have htcBody' : typecheck bodyCtx (PExpr.toExpr body) k = .ok result3 := by
                                      simpa using! htcBody
                                    have hIH_body := IH' k (by omega) masked bodyCtx (PExpr.toExpr body) result3 hreg_body htcBody'
                                    apply regimeConsistentWithCtxMasked_of_tagEnv_regime_nextTag masked (ctxAfter bodyCtx result3)
                                    · simp [ctxAfter]
                                    · simp [ctxAfter]
                                    · simp [ctxAfter]
                                    · exact hIH_body
                  | extern id x retSpec capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                      have happly_old :
                          applyPFnTClosure (.extern id x retSpec capturedEnv declaredArgQt captures) st1 st2 p p1
                            etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyPFnTClosure
                        unfold applyPFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      simp only [regimeConsistentWithCtxMasked, ctxAfter, tagEnvConsistentWithRegimeMasked]
                      intro k deps hk
                      -- Surviving input entries keep their regime value through
                      -- the insert-if-absent policy; the freshly installed return guard is
                      -- regime-interpreted by construction.
                      rcases applyPFnTClosure_extern_tagEnv_get_cases ctx st1 st2 p p1 etyp2 p2 pred2
                          rCursor r fuel'' id x retSpec capturedEnv declaredArgQt happly_old
                          k ⟨true, deps⟩ hk with hold | ⟨_, _, hR⟩
                      · rcases hIH1_tagEnv k deps hold with hm | ht
                        · exact Or.inl hm
                        · exact Or.inr (applyPFnTClosure_extern_regime_preserve_some
                            ctx st1 st2 p p1 etyp2 p2 pred2 rCursor r fuel''
                            id x retSpec capturedEnv declaredArgQt happly_old k true ht)
                      · exact Or.inr hR
                rcases hcases with
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1, _hpure, _hne, _hsub, hmap, hresults, h_join, rfl⟩ |
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1, _hne, _hsub, hmap, hresults, h_join, rfl⟩
                · subst hresults
                  have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtxMasked masked (ctxAfter ctx r) :=
                    h_fn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
                  exact joinTypeResults_regimeConsistentWithCtxMasked masked ctx first rest res h_join
                    (h_all_reg first (List.mem_cons_self ..))
                    (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))
                · subst hresults
                  have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtxMasked masked (ctxAfter ctx r) :=
                    h_pfn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
                  exact joinTypeResults_regimeConsistentWithCtxMasked masked ctx first rest res h_join
                    (h_all_reg first (List.mem_cons_self ..))
                    (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))

private lemma typecheckExpr_preserves_regimeConsistentWithCtx_main :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    regimeConsistentWithCtx ctx →
    typecheck ctx e fuel = .ok res →
    regimeConsistentWithCtx (ctxAfter ctx res) := by
  intro fuel ctx e res hreg htc
  have hmasked : regimeConsistentWithCtxMasked (fun _ => False) ctx := by
    exact tagEnvConsistentWithRegime_to_masked ctx.tagEnv ctx.regime (fun _ => False) hreg
  have hres :=
    typecheckExpr_preserves_regimeConsistentWithCtxMasked_main fuel (fun _ => False) ctx e res hmasked htc
  simpa [regimeConsistentWithCtxMasked, tagEnvConsistentWithRegimeMasked] using! hres

lemma typecheckExpr_preserves_regimeConsistentWithCtx
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hreg : regimeConsistentWithCtx ctx)
    (htc : typecheck ctx e fuel = .ok res) :
    regimeConsistentWithCtx (ctxAfter ctx res) :=
  typecheckExpr_preserves_regimeConsistentWithCtx_main fuel ctx e res hreg htc

lemma typecheckExpr_preserves_regimeConsistentWithCtxMasked
    (masked : Tag → Prop)
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hreg : regimeConsistentWithCtxMasked masked ctx)
    (htc : typecheck ctx e fuel = .ok res) :
    regimeConsistentWithCtxMasked masked (ctxAfter ctx res) :=
  typecheckExpr_preserves_regimeConsistentWithCtxMasked_main fuel masked ctx e res hreg htc

private lemma typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv_main :
    ∀ (fuel : Nat) (masked : Tag → Prop) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    MaskedTagsAbsentFromTrueTagEnv masked ctx →
    (∀ k, masked k → ctx.regime.lookup? k = none) →
    (∀ k, masked k → k < ctx.nextTag) →
    typecheck ctx e fuel = .ok res →
    MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx res) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro masked ctx e res habsent hmasked_none hmasked_bounded htc
    have IH' :
        ∀ m < fuel, ∀ (masked' : Tag → Prop) (ctx' : TypeContext) (e' : Expr)
          (res' : TypeResult),
          MaskedTagsAbsentFromTrueTagEnv masked' ctx' →
          (∀ k, masked' k → ctx'.regime.lookup? k = none) →
          (∀ k, masked' k → k < ctx'.nextTag) →
          typecheck ctx' e' m = .ok res' →
          MaskedTagsAbsentFromTrueTagEnv masked' (ctxAfter ctx' res') := by
      intro m hm masked' ctx' e' res' habsent' hmasked_none' hmasked_bounded' htc'
      exact IH m hm masked' ctx' e' res' habsent' hmasked_none' hmasked_bounded' htc'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc
        simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | bool _b =>
            unfold typecheckBool at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | unit =>
            unfold typecheckUnit at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | str _s =>
            unfold typecheckString at htc
            simp [pure, Except.pure] at htc
            cases htc
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | var x =>
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                cases pred with
                | noPred =>
                    simp [pure, Except.pure] at htc
                    cases htc
                    simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
                | guardOnly k =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
                | guardClosure k tcls ptcls body_t =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | fn _ _ _ _ =>
            have hfn := typecheckFn_ok_eq htc
            subst hfn
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ =>
                simp [h_topexpr, pure, Except.pure] at htc
                subst htc
                simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | externVal id typ poison pred =>
            have htc' : typecheckExternVal ctx id typ poison pred fuel' = .ok res := htc
            obtain ⟨_, tagMapping, _, _, _, halloc, _, _, rfl⟩ := typecheckExternVal_ok_shape htc'
            simp only [ctxAfter, MaskedTagsAbsentFromTrueTagEnv]
            intro k deps hm hk
            rcases installReturnGuard_get?_cases _ _ _ _ k _ hk with hold | ⟨hR, _⟩
            · exact habsent k deps hm hold
            · -- The installed tag is fresh, so it is not a masked tag.
              rcases applyExternRegimePolicy_lookup_spec ctx.regime id ctx.externRegime tagMapping k
                with heq | ⟨idx, hidx⟩
              · rw [heq, hmasked_none k hm] at hR; cases hR
              · exact absurd (collectAndAllocExternTags_mapping_values_ge _ _ _ _ halloc idx k hidx)
                  (Nat.not_le.mpr (hmasked_bounded k hm))
        | externRef _ _ _ _ _ =>
            simp only [typecheckExternRef] at htc
            simp [Bind.bind, Except.bind, pure, Except.pure] at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            cases htc
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | externFn id arg argTyp argPoison argPred retSpec effects cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternFn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec effects res htc
            rw [hres]
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | externPfn id arg argTyp argPoison argPred retSpec cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternPfn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec res htc
            rw [hres]
            simpa [ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using habsent
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, htag, _, _hnextTag, _hreg', _, _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
              (ctx₁ := ctxAfter ctx result1) (ctx₂ := ctxAfter ctx res)
            · simp [ctxAfter, htag]
            · exact hIH
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, _, htag, _, _hnextTag, _hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
              (ctx₁ := ctxAfter ctx result1) (ctx₂ := ctxAfter ctx res)
            · simp [ctxAfter, htag]
            · exact hIH
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, _, _, _, _, htag, _, _hnextTag, _hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
              (ctx₁ := ctxAfter ctx result1) (ctx₂ := ctxAfter ctx res)
            · simp [ctxAfter, htag]
            · exact hIH
        | op e1 op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
            rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, _, htag, _, _hnextTag, _hregime', _, _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            have hmasked_none_mid :
                ∀ k, masked k → (updateCtxFromResult ctx result1).regime.lookup? k = none := by
              intro k hk
              have hmono := regime_monotoneExt ctx e1 (fuel' - 1) result1 htc1'
              simpa [updateCtxFromResult] using!
                masked_lookup_none_of_monotoneStepExt hmasked_none
                  (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk
            have hmasked_bounded_mid :
                ∀ k, masked k → k < (updateCtxFromResult ctx result1).nextTag :=
              fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                (typecheck_nextTag_mono ctx e1 (fuel' - 1) result1 htc1')
            have habsent_mid :
                MaskedTagsAbsentFromTrueTagEnv masked (updateCtxFromResult ctx result1) := by
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            have hIH2 := IH' (fuel' - 1) (by omega) masked
              (updateCtxFromResult ctx result1) e2 result2
              habsent_mid hmasked_none_mid hmasked_bounded_mid htc2'
            apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
              (ctx₁ := ctxAfter (updateCtxFromResult ctx result1) result2)
              (ctx₂ := ctxAfter ctx res)
            · simp [ctxAfter, updateCtxFromResult, htag]
            · exact hIH2
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', res, htc1, hctx', htc2, rfl⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            have hmasked_none_mid : ∀ k, masked k → ctx'.regime.lookup? k = none := by
              intro k hk
              have hmono := regime_monotoneExt ctx e1 (fuel' - 1) result1 htc1'
              rw [hctx']
              simpa [updateCtxFromResult] using!
                masked_lookup_none_of_monotoneStepExt hmasked_none
                  (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk
            have hmasked_bounded_mid : ∀ k, masked k → k < ctx'.nextTag := by
              rw [hctx']
              exact fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                (typecheck_nextTag_mono ctx e1 (fuel' - 1) result1 htc1')
            have habsent_mid : MaskedTagsAbsentFromTrueTagEnv masked ctx' := by
              rw [hctx']
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok res := by simpa using! htc2
            exact IH' (fuel' - 1) (by omega) masked ctx' e2 res
              habsent_mid hmasked_none_mid hmasked_bounded_mid htc2'
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, htag, _, _hnextTag, _hregime', _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 result1
              habsent hmasked_none hmasked_bounded htc1'
            have hmasked_none_mid : ∀ k, masked k → ctx'.regime.lookup? k = none := by
              intro k hk
              have hmono := regime_monotoneExt ctx e1 (fuel' - 1) result1 htc1'
              rw [hctx']
              simpa [updateCtxFromResult] using!
                masked_lookup_none_of_monotoneStepExt hmasked_none
                  (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk
            have hmasked_bounded_mid : ∀ k, masked k → k < ctx'.nextTag := by
              rw [hctx']
              exact fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                (typecheck_nextTag_mono ctx e1 (fuel' - 1) result1 htc1')
            have habsent_mid : MaskedTagsAbsentFromTrueTagEnv masked ctx' := by
              rw [hctx']
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok result2 := by simpa using! htc2
            have hIH2 := IH' (fuel' - 1) (by omega) masked ctx' e2 result2
              habsent_mid hmasked_none_mid hmasked_bounded_mid htc2'
            apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
              (ctx₁ := ctxAfter ctx' result2) (ctx₂ := ctxAfter ctx res)
            · simp [ctxAfter, htag]
            · exact hIH2
        | assign e1 e2 =>
            unfold typecheckAssign at htc
            cases fuel' with
            | zero => simp at htc
            | succ fuel'' =>
                simp only [bind, Except.bind] at htc
                cases h_tc1 : typecheckExpr ctx e1 fuel'' with
                | error _ => simp [h_tc1] at htc
                | ok result1 =>
                    simp only [h_tc1] at htc
                    have htc1' : typecheck ctx e1 fuel'' = .ok result1 := by simpa using! h_tc1
                    have hIH1 := IH' fuel'' (by omega) masked ctx e1 result1
                      habsent hmasked_none hmasked_bounded htc1'
                    cases h_qt1 : result1.qualType with
                    | mk etyp1 p1 pred1 =>
                        rw [h_qt1] at htc
                        simp at htc
                        cases etyp1 <;> simp at htc
                        case ref ls =>
                            let memEnv2 := result1.memEnv'
                            let tagEnv2 := result1.tagEnv'
                            let nextLoc2 := result1.nextLoc'
                            let nextTag2 := result1.nextTag'
                            let regime2 := result1.regime'
                            let ctx2 : TypeContext :=
                              { pc := ctx.pc, regime := regime2, memEnv := memEnv2, varEnv := ctx.varEnv, bindEnv := ctx.bindEnv,
                                tagEnv := tagEnv2, nextLoc := nextLoc2, nextTag := nextTag2, nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                declaredExternRefs := result1.declared' }
                            have habsent2 : MaskedTagsAbsentFromTrueTagEnv masked ctx2 := by
                              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter, ctx2, tagEnv2] using hIH1
                            have hmasked_none2 : ∀ k, masked k → ctx2.regime.lookup? k = none := by
                              intro k hk
                              have hmono := regime_monotoneExt ctx e1 fuel'' result1 htc1'
                              simpa [ctx2, regime2] using!
                                masked_lookup_none_of_monotoneStepExt hmasked_none
                                  (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk
                            have hmasked_bounded2 : ∀ k, masked k → k < ctx2.nextTag :=
                              fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                                (typecheck_nextTag_mono ctx e1 fuel'' result1 htc1')
                            cases h_tc2 : typecheckExpr ctx2 e2 fuel'' with
                            | error err =>
                                have h_tc2_explicit :
                                    typecheckExpr
                                      { pc := ctx.pc, regime := result1.regime', memEnv := result1.memEnv',
                                        varEnv := ctx.varEnv, bindEnv := ctx.bindEnv, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                        nextTag := result1.nextTag', nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                        externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                        declaredExternRefs := result1.declared' }
                                      e2 fuel'' = .error err := by
                                  simpa [ctx2, memEnv2, tagEnv2, nextLoc2, nextTag2, regime2] using h_tc2
                                rw [h_tc2_explicit] at htc
                                simp at htc
                            | ok result2 =>
                                have htc2' : typecheck ctx2 e2 fuel'' = .ok result2 := by simpa using! h_tc2
                                have hIH2 := IH' fuel'' (by omega) masked ctx2 e2 result2
                                  habsent2 hmasked_none2 hmasked_bounded2 htc2'
                                have h_tc2_explicit :
                                    typecheckExpr
                                      { pc := ctx.pc, regime := result1.regime', memEnv := result1.memEnv',
                                        varEnv := ctx.varEnv, bindEnv := ctx.bindEnv, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                        nextTag := result1.nextTag', nextBind := result1.nextBind', pureCtx := ctx.pureCtx,
                                        externRegime := ctx.externRegime, externRefAllowed := ctx.externRefAllowed,
                                        declaredExternRefs := result1.declared' }
                                      e2 fuel'' = .ok result2 := by
                                  simpa [ctx2, memEnv2, tagEnv2, nextLoc2, nextTag2, regime2] using h_tc2
                                rw [h_tc2_explicit] at htc
                                simp at htc
                                cases h_qt2 : result2.qualType with
                                | mk etyp2 p2 pred2 =>
                                    rw [h_qt2] at htc
                                    simp at htc
                                    by_cases h_etyp2_int : etyp2 = ETyp.int
                                    · subst h_etyp2_int
                                      simp at htc
                                      cases htc
                                      exact
                                        MaskedTagsAbsentFromTrueTagEnv_invalidateTagDeps
                                          (masked := masked)
                                          (ctx := ctxAfter ctx2 result2) (ls := ls) hIH2
                                    · simp [h_etyp2_int] at htc
        | ite e1 e2 e3 =>
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            rcases hstruct with h1 | h2 | hstd
            · rcases h1 with ⟨k, deps, _, hRk, res1, htc1p, _, res2, _, htc2, _, _hmem, htag, _, _, _hregEq, _, _⟩
              have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
              have hnotMasked : masked k → False := by
                intro hk
                have hnone := hmasked_none k hk
                rw [hRk] at hnone
                contradiction
              have habsent_true :
                  MaskedTagsAbsentFromTrueTagEnv masked
                    { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } :=
                MaskedTagsAbsentFromTrueTagEnv_insert_true
                  (masked := masked) (ctx := ctx) habsent hnotMasked
              have hmasked_none_true :
                  ∀ t, masked t →
                    ({ ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } : TypeContext).regime.lookup? t = none := by
                simpa using hmasked_none
              have hmasked_bounded_true :
                  ∀ t, masked t →
                    t < ({ ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                    nextTag := res1.nextTag', nextBind := res1.nextBind' } : TypeContext).nextTag :=
                fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht) hb1
              have htc2' : typecheck { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                nextTag := res1.nextTag', nextBind := res1.nextBind',
                                                declaredExternRefs := res1.declared' } e2 (fuel' - 1) = .ok res2 := by
                simpa using! htc2
              have hIH2 := IH' (fuel' - 1) (by omega) masked
                { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                           nextTag := res1.nextTag', nextBind := res1.nextBind',
                           declaredExternRefs := res1.declared' } e2 res2
                habsent_true hmasked_none_true hmasked_bounded_true htc2'
              apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
                (ctx₁ := ctxAfter { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                             nextTag := res1.nextTag', nextBind := res1.nextBind',
                                             declaredExternRefs := res1.declared' } res2)
                (ctx₂ := ctxAfter ctx res)
              · simp [ctxAfter, htag]
              · exact hIH2
            · rcases h2 with ⟨k, deps, _, _, res1, htc1p, _, res2, res3, htc2f, htc3, _hmem, htag, _, _, _hregEq, _, _⟩
              have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
              have habsent_false :
                  MaskedTagsAbsentFromTrueTagEnv masked
                    { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } :=
                MaskedTagsAbsentFromTrueTagEnv_insert_false
                  (masked := masked) (ctx := ctx) habsent
              let ctxF := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                     nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind',
                                     declaredExternRefs := res2.declared' }
              have habsent_F : MaskedTagsAbsentFromTrueTagEnv masked ctxF := by
                simpa [ctxF, MaskedTagsAbsentFromTrueTagEnv] using habsent_false
              have hmasked_none_F : ∀ t, masked t → ctxF.regime.lookup? t = none := by
                simpa [ctxF] using hmasked_none
              have hbF : ctx.nextTag ≤ res2.nextTag' := by
                have := typecheck_nextTag_mono _ e2 (fuel' - 1) res2 (by simpa [typecheck] using htc2f)
                exact Nat.le_trans hb1 (by simpa using this)
              have hmasked_bounded_F : ∀ t, masked t → t < ctxF.nextTag := by
                intro t ht
                show t < res2.nextTag'
                exact Nat.lt_of_lt_of_le (hmasked_bounded t ht) hbF
              have htc3' : typecheck ctxF e3 (fuel' - 1) = .ok res3 := by simpa [ctxF] using! htc3
              have hIH3 := IH' (fuel' - 1) (by omega) masked ctxF e3 res3
                habsent_F hmasked_none_F hmasked_bounded_F htc3'
              apply MaskedTagsAbsentFromTrueTagEnv_of_tagEnv
                (ctx₁ := ctxAfter ctxF res3) (ctx₂ := ctxAfter ctx res)
              · simp [ctxAfter, ctxF, htag]
              · exact hIH3
            · obtain ⟨_hstdCase, res1, htc1, _, res2, htc2, res3, htc3,
                _hmem, htag, _, _hnextTag, _hregEq, _, _, _⟩ := hstd
              have htc1' : typecheck ctx e1 (fuel' - 1) = .ok res1 := by simpa using! htc1
              have hIH1 := IH' (fuel' - 1) (by omega) masked ctx e1 res1
                habsent hmasked_none hmasked_bounded htc1'
              set ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                     nextLoc := res1.nextLoc', nextTag := res1.nextTag', nextBind := res1.nextBind', regime := res1.regime',
                                     declaredExternRefs := res1.declared' }
              have habsent1 : MaskedTagsAbsentFromTrueTagEnv masked ctx' := by
                simpa [ctx', MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hIH1
              have hmasked_none1 : ∀ k, masked k → ctx'.regime.lookup? k = none := by
                intro k hk
                have hmono := regime_monotoneExt ctx e1 (fuel' - 1) res1 htc1'
                simpa [ctx'] using! masked_lookup_none_of_monotoneStepExt hmasked_none
                  (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk
              have hb1 : ctx.nextTag ≤ res1.nextTag' := typecheck_nextTag_mono ctx e1 (fuel' - 1) res1 htc1'
              have hmasked_bounded1 : ∀ k, masked k → k < ctx'.nextTag :=
                fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht) hb1
              set ctx'' := { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
              have habsent1' : MaskedTagsAbsentFromTrueTagEnv masked ctx'' := by
                simpa [ctx'', MaskedTagsAbsentFromTrueTagEnv] using habsent1
              have hmasked_none1' : ∀ k, masked k → ctx''.regime.lookup? k = none := by
                simpa [ctx''] using hmasked_none1
              have hmasked_bounded1' : ∀ k, masked k → k < ctx''.nextTag := by
                simpa [ctx''] using hmasked_bounded1
              have htc2' : typecheck ctx'' e2 (fuel' - 1) = .ok res2 := by simpa using! htc2
              have hIH2 := IH' (fuel' - 1) (by omega) masked ctx'' e2 res2
                habsent1' hmasked_none1' hmasked_bounded1' htc2'
              set ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind', declaredExternRefs := res2.declared' }
              have habsent3_in : MaskedTagsAbsentFromTrueTagEnv masked ctxForE3 := by
                simpa [ctxForE3, MaskedTagsAbsentFromTrueTagEnv] using habsent1'
              have hmasked_none3 : ∀ k, masked k → ctxForE3.regime.lookup? k = none := by
                simpa [ctxForE3] using hmasked_none1'
              have hb2 : res1.nextTag' ≤ res2.nextTag' := by
                simpa [ctx'', ctx'] using typecheck_nextTag_mono ctx'' e2 (fuel' - 1) res2 htc2'
              have hmasked_bounded3 : ∀ k, masked k → k < ctxForE3.nextTag := by
                intro t ht
                show t < res2.nextTag'
                exact Nat.lt_of_lt_of_le (hmasked_bounded1' t ht) hb2
              have htc3' : typecheck ctxForE3 e3 (fuel' - 1) = .ok res3 := by simpa using! htc3
              have hIH3 := IH' (fuel' - 1) (by omega) masked ctxForE3 e3 res3
                habsent3_in hmasked_none3 hmasked_bounded3 htc3'
              have hIH2_tag :
                  ∀ k deps, masked k → res2.tagEnv'.get? k = some ⟨true, deps⟩ → False := by
                simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hIH2
              have hIH3_tag :
                  ∀ k deps, masked k → res3.tagEnv'.get? k = some ⟨true, deps⟩ → False := by
                simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hIH3
              have hjoin_abs :=
                MaskedTagsAbsentFromTrueTagEnvs_join hIH2_tag hIH3_tag
              simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter, htag] using hjoin_abs
        | app e1 e2 =>
            simp at htc
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
                rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
                  ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩
                have hIH2 := IH' fuel'' (by omega) masked ctx e2 result2
                  habsent hmasked_none hmasked_bounded htc2
                have hmasked_none2 :
                    ∀ k, masked k → (ctxAfter ctx result2).regime.lookup? k = none := by
                  intro k hk
                  exact masked_lookup_none_of_monotoneStepExt hmasked_none
                    (fun t ht => Nat.not_le.2 (hmasked_bounded t ht))
                    (regime_monotoneExt ctx e2 fuel'' result2 htc2) k hk
                have hbfun : ctx.nextTag ≤ result2.nextTag' :=
                  typecheck_nextTag_mono ctx e2 fuel'' result2 htc2
                have hmasked_bounded_fun :
                    ∀ k, masked k →
                      k < (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, ctx.bindEnv, result2.tagEnv',
                        result2.nextLoc', result2.nextTag', result2.nextBind', ctx.pureCtx, ctx.externRegime,
                        ctx.externRefAllowed, result2.declared'⟩ : TypeContext).nextTag :=
                  fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht) hbfun
                have habsent_fun :
                    MaskedTagsAbsentFromTrueTagEnv masked
                      (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, ctx.bindEnv, result2.tagEnv',
                        result2.nextLoc', result2.nextTag', result2.nextBind', ctx.pureCtx, ctx.externRegime,
                        ctx.externRefAllowed, result2.declared'⟩ : TypeContext) := by
                  simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hIH2
                have hmasked_none_fun :
                    ∀ k, masked k →
                      (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, ctx.bindEnv, result2.tagEnv',
                        result2.nextLoc', result2.nextTag', result2.nextBind', ctx.pureCtx, ctx.externRegime,
                        ctx.externRefAllowed, result2.declared'⟩ : TypeContext).regime.lookup? k = none := by
                  intro k hk
                  simpa using! hmasked_none2 k hk
                have hIH1 := IH' fuel'' (by omega) masked _ e1 result1
                  habsent_fun hmasked_none_fun hmasked_bounded_fun htc1
                have hIH1_tag :
                    ∀ k deps, masked k → result1.tagEnv'.get? k = some ⟨true, deps⟩ → False := by
                  simpa [MaskedTagsAbsentFromTrueTagEnv, ctxAfter] using hIH1
                have hmasked_none1 :
                    ∀ k, masked k → result1.regime'.lookup? k = none := by
                  intro k hk
                  exact masked_lookup_none_of_monotoneStepExt hmasked_none_fun
                    (fun t ht => Nat.not_le.2 (hmasked_bounded_fun t ht))
                    (regime_monotoneExt
                      (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, ctx.bindEnv, result2.tagEnv',
                        result2.nextLoc', result2.nextTag', result2.nextBind', ctx.pureCtx, ctx.externRegime,
                        ctx.externRefAllowed, result2.declared'⟩ : TypeContext)
                      e1 fuel'' result1 htc1) k hk
                have h_fn_closure_absent :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
                      (results : List TypeResult),
                      applyClosuresThreaded
                        (fun tcl cursor bn =>
                          applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                        tcls (result1.nextTag', result1.nextLoc') result1.nextBind' = .ok results →
                      ∀ r, r ∈ results → MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r) := by
                  intro st1 st2 p p1 tcls results hthread r hr
                  have hb_r1 : ctx.nextTag ≤ result1.nextTag' :=
                    Nat.le_trans hbfun (by simpa using typecheck_nextTag_mono _ e1 fuel'' result1 htc1)
                  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
                      (applyOne := fun tcl cursor bn =>
                        applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                      (base := result1.nextTag')
                      (hmono := fun tcl cursor bn result hb happly =>
                        Nat.le_trans hb (applyFnTClosureAtCursor_nextTag_advance tcl ctx st1 st2 p p1
                          etyp2 p2 pred2 result1 result cursor bn fuel'' happly))
                      (hbase := Nat.le_refl _) (hthread := hthread) (hmem := hr) with
                    ⟨tcl, _htcl_mem, cursor, bn, hcursorTag, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                              cases hqt3 : result3.qualType with
                              | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    let bodyCtx : TypeContext := { ctx with
                                      pc := joinPoison p (joinPoison p1 ctx.pc),
                                      memEnv := result1.memEnv',
                                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                      bindEnv := BindEnv.bindParam env x bn,
                                      tagEnv := result1.tagEnv', nextTag := cursor.1, nextBind := bn + 1,
                                      nextLoc := cursor.2, regime := result1.regime',
                                      externRefAllowed := false,
                                      declaredExternRefs := result1.declared' }
                                    have habsent_body :
                                        MaskedTagsAbsentFromTrueTagEnv masked bodyCtx := by
                                      simpa [bodyCtx, MaskedTagsAbsentFromTrueTagEnv] using hIH1_tag
                                    have hmasked_none_body :
                                        ∀ k, masked k → bodyCtx.regime.lookup? k = none := by
                                      intro k hk
                                      simpa [bodyCtx] using hmasked_none1 k hk
                                    have hmasked_bounded_body :
                                        ∀ k, masked k → k < bodyCtx.nextTag :=
                                      fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                                        (Nat.le_trans hb_r1 hcursorTag)
                                    have htcBody' : typecheck bodyCtx body k = .ok result3 := by
                                      simpa [bodyCtx] using! htcBody
                                    have hIH_body := IH' k (by omega) masked bodyCtx body result3
                                      habsent_body hmasked_none_body hmasked_bounded_body htcBody'
                                    simpa [bodyCtx, ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using hIH_body
                  | extern id x retSpec effects capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                      have happly_old :
                          applyFnTClosure (.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
                            etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyFnTClosure
                        unfold applyFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      -- An output `true` entry is either a surviving (invalidated)
                      -- input entry — absent for masked tags by the IH — or the freshly
                      -- installed return guard, whose tag is ≥ the cursor base and hence
                      -- never masked (masked tags are bounded by the incoming nextTag).
                      intro k deps hmasked hget
                      rcases applyFnTClosure_extern_tagEnv_get_cases ctx st1 st2 p p1 etyp2 p2 pred2
                          rCursor r fuel'' id x retSpec effects capturedEnv declaredArgQt happly_old
                          k ⟨true, deps⟩ (by simpa [ctxAfter] using hget) with hold | ⟨hge, _, _⟩
                      · have habsent : MaskedTagsAbsentFromTrueTagEnv masked
                            { ctx with tagEnv := rCursor.tagEnv' } := by
                          simpa [rCursor, MaskedTagsAbsentFromTrueTagEnv] using hIH1_tag
                        exact habsent k deps hmasked (invalidateTagDeps_get?_some_imp _ _ k _ hold)
                      · exact absurd hge (Nat.not_le.2
                          (Nat.lt_of_lt_of_le (hmasked_bounded k hmasked) (Nat.le_trans hb_r1 hcursorTag)))
                have h_pfn_closure_absent :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
                      (results : List TypeResult),
                      applyClosuresThreaded
                        (fun tcl cursor bn =>
                          applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                        tcls (result1.nextTag', result1.nextLoc') result1.nextBind' = .ok results →
                      ∀ r, r ∈ results → MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r) := by
                  intro st1 st2 p p1 tcls results hthread r hr
                  have hb_r1 : ctx.nextTag ≤ result1.nextTag' :=
                    Nat.le_trans hbfun (by simpa using typecheck_nextTag_mono _ e1 fuel'' result1 htc1)
                  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
                      (applyOne := fun tcl cursor bn =>
                        applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor bn fuel'')
                      (base := result1.nextTag')
                      (hmono := fun tcl cursor bn result hb happly =>
                        Nat.le_trans hb (applyPFnTClosureAtCursor_nextTag_advance tcl ctx st1 st2 p p1
                          etyp2 p2 pred2 result1 result cursor bn fuel'' happly))
                      (hbase := Nat.le_refl _) (hthread := hthread) (hmem := hr) with
                    ⟨tcl, _htcl_mem, cursor, bn, hcursorTag, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyPFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyPFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                            cases hqt3 : result3.qualType with
                            | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    let bodyCtx := { ctx with
                                      pc := joinPoison p (joinPoison ctx.pc p1),
                                      memEnv := result1.memEnv',
                                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                      bindEnv := BindEnv.bindParam env x bn,
                                      tagEnv := result1.tagEnv', nextTag := cursor.1, nextBind := bn + 1,
                                      pureCtx := true,
                                      nextLoc := cursor.2, regime := result1.regime',
                                      externRefAllowed := false,
                                      declaredExternRefs := result1.declared' }
                                    have habsent_body :
                                        MaskedTagsAbsentFromTrueTagEnv masked bodyCtx := by
                                      simpa [bodyCtx, MaskedTagsAbsentFromTrueTagEnv] using hIH1_tag
                                    have hmasked_none_body :
                                        ∀ k, masked k → bodyCtx.regime.lookup? k = none := by
                                      intro k hk
                                      simpa [bodyCtx] using hmasked_none1 k hk
                                    have hmasked_bounded_body :
                                        ∀ k, masked k → k < bodyCtx.nextTag :=
                                      fun t ht => Nat.lt_of_lt_of_le (hmasked_bounded t ht)
                                        (Nat.le_trans hb_r1 hcursorTag)
                                    have htcBody' : typecheck bodyCtx (PExpr.toExpr body) k = .ok result3 := by
                                      simpa [bodyCtx] using! htcBody
                                    have hIH_body := IH' k (by omega) masked bodyCtx
                                      (PExpr.toExpr body) result3
                                      habsent_body hmasked_none_body hmasked_bounded_body htcBody'
                                    simpa [bodyCtx, ctxAfter, MaskedTagsAbsentFromTrueTagEnv] using hIH_body
                  | extern id x retSpec capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                      have happly_old :
                          applyPFnTClosure (.extern id x retSpec capturedEnv declaredArgQt captures) st1 st2 p p1
                            etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyPFnTClosure
                        unfold applyPFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      -- Surviving input entries are absent for masked tags by
                      -- the IH; the freshly installed return guard's tag is ≥ the cursor
                      -- base and hence never masked (masked tags are bounded).
                      intro k deps hmasked hget
                      rcases applyPFnTClosure_extern_tagEnv_get_cases ctx st1 st2 p p1 etyp2 p2 pred2
                          rCursor r fuel'' id x retSpec capturedEnv declaredArgQt happly_old
                          k ⟨true, deps⟩ (by simpa [ctxAfter] using hget) with hold | ⟨hge, _, _⟩
                      · have habsent : MaskedTagsAbsentFromTrueTagEnv masked
                            { ctx with tagEnv := rCursor.tagEnv' } := by
                          simpa [rCursor, MaskedTagsAbsentFromTrueTagEnv] using hIH1_tag
                        exact habsent k deps hmasked hold
                      · exact absurd hge (Nat.not_le.2
                          (Nat.lt_of_lt_of_le (hmasked_bounded k hmasked) (Nat.le_trans hb_r1 hcursorTag)))
                rcases hcases with
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1, _hpure, _hne, _hsub, hmap, hresults, h_join, rfl⟩ |
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1, _hne, _hsub, hmap, hresults, h_join, rfl⟩
                · subst hresults
                  have h_all :
                      ∀ r, r ∈ (first :: rest) →
                        MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r) :=
                    h_fn_closure_absent st1 st2 p p1 tcls (first :: rest) hmap
                  exact joinTypeResults_MaskedTagsAbsentFromTrueTagEnv' masked ctx first rest res
                    h_join (h_all first (List.mem_cons_self ..))
                    (fun r hr => h_all r (List.mem_cons_of_mem _ hr))
                · subst hresults
                  have h_all :
                      ∀ r, r ∈ (first :: rest) →
                        MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx r) :=
                    h_pfn_closure_absent st1 st2 p p1 tcls (first :: rest) hmap
                  exact joinTypeResults_MaskedTagsAbsentFromTrueTagEnv' masked ctx first rest res
                    h_join (h_all first (List.mem_cons_self ..))
                    (fun r hr => h_all r (List.mem_cons_of_mem _ hr))

lemma typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
    (masked : Tag → Prop)
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (habsent : MaskedTagsAbsentFromTrueTagEnv masked ctx)
    (hmasked_none : ∀ k, masked k → ctx.regime.lookup? k = none)
    (hmasked_bounded : ∀ k, masked k → k < ctx.nextTag)
    (htc : typecheck ctx e fuel = .ok res) :
    MaskedTagsAbsentFromTrueTagEnv masked (ctxAfter ctx res) :=
  typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv_main
    fuel masked ctx e res habsent hmasked_none hmasked_bounded htc

/-- Mix lemma: combine inVar evidence from one (σ, Γ₁) pair with inMem evidence from
    another (σ₂, Γ) pair. Works because `QTypInEnvs.inVar` only uses σ and
    `QTypInEnvs.inMem` only uses Γ. -/
private lemma EnvRespectsTagMeaning_mix
    (tm : TagMeaning) (σ₁ : VarTypeEnv) (Γ₁ : MemoryTypeEnv) (σ₂ : VarTypeEnv) (Γ₂ : MemoryTypeEnv)
    (h1 : EnvRespectsTagMeaning tm σ₁ Γ₁)
    (h2 : EnvRespectsTagMeaning tm σ₂ Γ₂) :
    EnvRespectsTagMeaning tm σ₁ Γ₂ := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinenvs, hguard⟩
  cases hinenvs with
  | inVar _ _ x _ qtRoot hlookup hinq =>
    -- Same σ₁ lookup, swap Γ₂ for Γ₁
    exact h1.1 (GuardDescInEnvsDeep.intro qt k d
      (QTypInEnvs.inVar σ₁ Γ₁ x qt qtRoot hlookup hinq) hguard)
  | inMem _ _ l _ qtRoot hlookup hinq =>
    -- Same Γ₂ lookup, swap σ₁ for σ₂
    exact h2.1 (GuardDescInEnvsDeep.intro qt k d
      (QTypInEnvs.inMem σ₂ Γ₂ l qt qtRoot hlookup hinq) hguard)

/-- typecheckIf always produces a result with pred = noPred. -/

lemma typecheckIf_pred_noPred
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckIf ctx e1 e2 e3 fuel = .ok res) :
    res.qualType.pred = Predicate.noPred := by
  cases fuel with
  | zero => simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind] at htc
    cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv fuel' with
    | ok kd =>
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      cases hregime : ctx.regime.lookup? k with
      | some b =>
        cases b with
        | true =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                    pure, Except.pure] at htc
                cases htc2 : typecheckExpr _ e2 fuel' with
                | error e => rw [htc2] at htc; simp at htc
                | ok result2 =>
                  rw [htc2] at htc; simp at htc
                  match hq2 : result2.qualType with
                  | ⟨_, _, _⟩ =>
                    simp only [hq2] at htc
                    cases htc3 : typecheckExpr _ e3 fuel' with
                    | error e => rw [htc3] at htc; simp at htc
                    | ok result3 =>
                      rw [htc3] at htc; simp at htc
                      match hq3 : result3.qualType with
                      | ⟨_, _, _⟩ =>
                        simp only [hq3] at htc
                        split at htc
                        all_goals cases htc
                        all_goals rfl
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
        | false =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                    pure, Except.pure] at htc
                cases htc2 : typecheckExpr _ e2 fuel' with
                | error e => rw [htc2] at htc; simp at htc
                | ok result2 =>
                  rw [htc2] at htc; simp at htc
                  match hq2 : result2.qualType with
                  | ⟨etyp2, _, _⟩ =>
                    simp only [hq2] at htc
                    cases htc3 : typecheckExpr _ e3 fuel' with
                    | error e => rw [htc3] at htc; simp at htc
                    | ok result3 =>
                      rw [htc3] at htc; simp at htc
                      match hq3 : result3.qualType with
                      | ⟨_, _, _⟩ =>
                        simp only [hq3] at htc
                        split at htc
                        all_goals cases htc
                        all_goals rfl
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
      | none =>
        simp only [hregime] at htc
        cases htc1pure : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
        | error e => simp only [htc1pure] at htc; cases htc
        | ok guardResult =>
          simp only [htc1pure] at htc
          match hqGuard : guardResult.qualType with
          | ⟨guardEtyp, _, _⟩ =>
            simp only [hqGuard] at htc
            by_cases hguardBool : guardEtyp = ETyp.bool
            · simp only [hguardBool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
              cases htc1 : typecheckExpr ctx e1 fuel' with
              | error e => simp only [htc1] at htc; cases htc
              | ok result1 =>
                simp only [htc1] at htc
                match hq1 : result1.qualType with
                | ⟨etyp1, p1, _⟩ =>
                  simp only [hq1] at htc
                  by_cases hbool : etyp1 = ETyp.bool
                  · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
                    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                           nextLoc := result1.nextLoc', nextTag := result1.nextTag', nextBind := result1.nextBind', regime := result1.regime',
                                           declaredExternRefs := result1.declared' }
                    let pc' := joinPoison ctx.pc p1
                    let ctx'' := { ctx' with pc := pc' }
                    cases htc2 : typecheckExpr ctx'' e2 fuel' with
                    | error e => rw [htc2] at htc; cases htc
                    | ok result2 =>
                      rw [htc2] at htc
                      match hq2 : result2.qualType with
                      | ⟨etyp2, _, _⟩ =>
                        simp only [hq2] at htc
                        let ctxForE3 :=
                          { ctx'' with
                            nextLoc := result2.nextLoc'
                            nextTag := result2.nextTag', nextBind := result2.nextBind'
                            declaredExternRefs := result2.declared' }
                        cases htc3 : typecheckExpr ctxForE3 e3 fuel' with
                        | error e => rw [htc3] at htc; cases htc
                        | ok result3 =>
                          rw [htc3] at htc
                          match hq3 : result3.qualType with
                          | ⟨etyp3, _, _⟩ =>
                            simp only [hq3] at htc
                            by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                            · simp only [hcompat] at htc; cases htc
                            · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                                cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                              simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htc
                              cases htc; rfl
                  · simp only [hbool, bne_iff_ne, ne_eq] at htc
                    cases htc
            · simp only [hguardBool, bne_iff_ne, ne_eq] at htc
              cases htc
    | error err =>
      simp only [hmatch] at htc
      cases htc1 : typecheckExpr ctx e1 fuel' with
      | error e => simp only [htc1] at htc; cases htc
      | ok result1 =>
        simp only [htc1] at htc
        match hq1 : result1.qualType with
        | ⟨etyp1, _, _⟩ =>
          simp only [hq1] at htc
          by_cases hbool : etyp1 = ETyp.bool
          · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
            cases htc2 : typecheckExpr _ e2 fuel' with
            | error e => rw [htc2] at htc; cases htc
            | ok result2 =>
              rw [htc2] at htc
              match hq2 : result2.qualType with
              | ⟨etyp2, _, _⟩ =>
                simp only [hq2] at htc
                cases htc3 : typecheckExpr _ e3 fuel' with
                | error e => rw [htc3] at htc; cases htc
                | ok result3 =>
                  rw [htc3] at htc
                  match hq3 : result3.qualType with
                  | ⟨etyp3, _, _⟩ =>
                    simp only [hq3] at htc
                    by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                    · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc; cases htc
                    · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                        cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                      simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htc
                      cases htc; rfl
          · simp only [hbool, bne_iff_ne, ne_eq] at htc
            cases htc

/-- Transport QTypRespectsTagMeaning across same etyp when pred becomes noPred.
    The self-descriptor vanishes (noPred → none), and nested descriptors through etyp
    are unchanged. -/
private lemma QTypRespectsTagMeaning_of_etyp_noPred
    (tm : TagMeaning) (qt qt' : QTyp)
    (h : QTypRespectsTagMeaning tm qt)
    (hetyp : qt'.etyp = qt.etyp)
    (hpred : qt'.pred = Predicate.noPred) :
    QTypRespectsTagMeaning tm qt' := by
  intro q k d hinq hqd
  have htr := QTypInQTyp_transport_etyp hinq hetyp
  cases htr with
  | inl hEq =>
    subst hEq
    simp [qtypGuardDesc?, hpred] at hqd
  | inr hinq' =>
    exact h hinq' hqd

private lemma EnvRespectsTagMeaning_joinMemEnvsStrong'
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ1 Γ2 : MemoryTypeEnv)
    (h1 : EnvRespectsTagMeaning tm σ Γ1) :
    EnvRespectsTagMeaning tm σ (joinMemEnvsStrong Γ1 Γ2) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hgd
  rcases hgd with ⟨qt, k, d, hinq, hdesc⟩
  cases hinq with
  | inVar _ _ x _ qtRoot hlookup hsub =>
      exact h1.1 (GuardDescInEnvsDeep.intro qt k d (QTypInEnvs.inVar σ Γ1 x qt qtRoot hlookup hsub) hdesc)
  | inMem _ _ l qt0 qtRoot hlookup hsub =>
      have hcontains : (joinMemEnvsStrong Γ1 Γ2).contains l := by
        have hlookup_eq : (joinMemEnvsStrong Γ1 Γ2).lookup l = some qtRoot := by
          rw [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?]
          exact hlookup
        exact memEnv_contains_of_lookup_some (joinMemEnvsStrong Γ1 Γ2) l qtRoot hlookup_eq
      have hor := joinMemEnvsStrong_contains_implies_or Γ1 Γ2 l hcontains
      cases hor with
      | inl hleft =>
          by_cases h2none : Γ2.lookup l = none
          · have h2none_get : Γ2[l]? = none := by
              simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h2none
            have hleft_eq :=
              joinMemEnvsStrong_lookup_eq_left_of_right_none Γ1 Γ2 l hleft h2none_get
            cases h1lookup : Γ1.lookup l with
            | none =>
                rw [h1lookup, hlookup] at hleft_eq
                simp at hleft_eq
            | some qt1 =>
                rw [h1lookup] at hleft_eq
                rw [hlookup] at hleft_eq
                have hroot_eq : qtRoot = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
                  simpa using hleft_eq
                have htm_qt1 : QTypRespectsTagMeaning tm qt1 :=
                  EnvRespectsTagMeaning_mem_lookup_qtyp tm σ Γ1 l qt1 h1 h1lookup
                have htm_root : QTypRespectsTagMeaning tm qtRoot := by
                  apply QTypRespectsTagMeaning_transport_etyp_noGuard tm qt1 qtRoot htm_qt1
                  · simpa using congrArg QTyp.etyp hroot_eq
                  · simp [hroot_eq, qtypGuardDesc?]
                exact htm_root hsub hdesc
          · have h2some : Γ2[l]? ≠ none := by
              intro hnone
              exact h2none (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hnone)
            have h1some : Γ1[l]? ≠ none := by
              intro hnone
              have hnot_some : ¬Option.isSome (Γ1[l]?) := by simp [hnone]
              have hmem : l ∈ Γ1 := (Std.ExtTreeMap.contains_iff_mem).mp hleft
              exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
            rcases Option.ne_none_iff_exists'.1 h1some with ⟨e1, h1some'⟩
            rcases Option.ne_none_iff_exists'.1 h2some with ⟨e2, h2some'⟩
            let qt1 : QTyp := ⟨ETyp.int, e1.poison, e1.pred⟩
            let qt2 : QTyp := ⟨ETyp.int, e2.poison, e2.pred⟩
            have h1lookup' : Γ1.lookup l = some qt1 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h1some', qt1, Option.map]
            have h2lookup' : Γ2.lookup l = some qt2 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h2some', qt2, Option.map]
            have hlookupW : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot := by
              rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup Γ1 Γ2 l qt1 qt2 h1lookup' h2lookup']
              exact hlookup
            exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 hlookupW h1some h2some) hsub hdesc
      | inr hright =>
          by_cases h1none : Γ1.lookup l = none
          · have h1none_get : Γ1[l]? = none := by
              simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h1none
            have hright_eq :=
              joinMemEnvsStrong_lookup_eq_right_of_left_none Γ1 Γ2 l h1none_get hright
            cases h2lookup : Γ2.lookup l with
            | none =>
                rw [h2lookup, hlookup] at hright_eq
                simp at hright_eq
            | some qt2 =>
                rw [h2lookup] at hright_eq
                rw [hlookup] at hright_eq
                have hroot_eq : qtRoot = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
                  simpa using hright_eq
                have hqt2_int : qt2.etyp = ETyp.int :=
                  memEnv_lookup_etyp_int Γ2 l qt2 h2lookup
                have hnotfun : qtRoot.etyp.isFunctionType = false := by
                  simp [hroot_eq, hqt2_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hself : qt = qtRoot := QTypInQTyp_eq_of_nonFunctionTarget hsub hnotfun
                subst hself
                simp [hroot_eq, qtypGuardDesc?] at hdesc
          · have h1some : Γ1[l]? ≠ none := by
              intro hnone
              exact h1none (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hnone)
            have h2some : Γ2[l]? ≠ none := by
              intro hnone
              have hnot_some : ¬Option.isSome (Γ2[l]?) := by simp [hnone]
              have hmem : l ∈ Γ2 := (Std.ExtTreeMap.contains_iff_mem).mp hright
              exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
            rcases Option.ne_none_iff_exists'.1 h1some with ⟨e1, h1some'⟩
            rcases Option.ne_none_iff_exists'.1 h2some with ⟨e2, h2some'⟩
            let qt1 : QTyp := ⟨ETyp.int, e1.poison, e1.pred⟩
            let qt2 : QTyp := ⟨ETyp.int, e2.poison, e2.pred⟩
            have h1lookup' : Γ1.lookup l = some qt1 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h1some', qt1, Option.map]
            have h2lookup' : Γ2.lookup l = some qt2 := by
              simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h2some', qt2, Option.map]
            have hlookupW : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot := by
              rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup Γ1 Γ2 l qt1 qt2 h1lookup' h2lookup']
              exact hlookup
            exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 hlookupW h1some h2some) hsub hdesc

-- A single join-step for QTypRespectsTagMeaning: joining two tag-meaning-respecting
-- qualified types produces another tag-meaning-respecting qualified type.
private lemma QTypRespectsTagMeaning_joinStep
    (tm : TagMeaning) (e1 e2 : ETyp) (p1 p2 : Poison) (pred1 pred2 : Predicate)
    (h1 : QTypRespectsTagMeaning tm ⟨e1, p1, pred1⟩)
    (h2 : QTypRespectsTagMeaning tm ⟨e2, p2, pred2⟩) :
    QTypRespectsTagMeaning tm ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
  intro qt' k d hinq hqd
  have hdecomp :
      QTypInQTyp qt' ⟨e1, p1, pred1⟩ ∨
      QTypInQTyp qt' ⟨e2, p2, pred2⟩ ∨
      qt' = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ :=
    (QTypInQTyp.recOn
        (motive := fun qt' qt₂ _ =>
          qt₂ = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ →
          QTypInQTyp qt' ⟨e1, p1, pred1⟩ ∨ QTypInQTyp qt' ⟨e2, p2, pred2⟩ ∨
          qt' = ⟨joinETyps e1 e2 p1 p2, joinPoison p1 p2, joinPredicates pred1 pred2⟩)
        hinq
        (fun _ hn => Or.inr (Or.inr hn))
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x _n hetyp htcl hcap hjoined => by
          subst hjoined
          cases e1 with
          | arrow st1a st2a pa1 tcls1 =>
              cases e2 with
              | arrow st1b st2b pb1 tcls2 =>
                  simp only [joinETyps] at hetyp
                  by_cases hshape : st1a == st1b && st2a == st2b
                  · simp only [hshape, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                    cases mem_mergeFnTClosures_inv tcls1 tcls2 tcl htcl with
                    | inl h =>
                        exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                          st1a st2a pa1 tcls1 tcl x rfl h hcap)
                    | inr h =>
                        exact Or.inr (Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1b st2b pb1 tcls2, p2, pred2⟩
                          st1b st2b pb1 tcls2 tcl x rfl h hcap))
                  · simp only [hshape, Bool.false_eq_true, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                    exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                      st1a st2a pa1 tcls1 tcl x rfl htcl hcap)
              | _ =>
                  simp only [joinETyps] at hetyp
                  obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.arrow.inj hetyp
                  exact Or.inl (QTypInQTyp.in_arrow qtInner ⟨ETyp.arrow st1a st2a pa1 tcls1, p1, pred1⟩
                    st1a st2a pa1 tcls1 tcl x rfl htcl hcap)
          | int | bool | unit | string => simp [joinETyps] at hetyp
          | ref ls =>
              cases e2 with
              | ref ls2 =>
                  simp [joinETyps] at hetyp
              | _ => simp [joinETyps] at hetyp
          | parrow st1a st2a pa1 ptcls1 =>
              cases e2 with
              | parrow st1b st2b pb1 ptcls2 =>
                  simp only [joinETyps] at hetyp
                  split_ifs at hetyp
              | _ => simp [joinETyps] at hetyp)
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x _n hetyp htcl hcap hjoined => by
          subst hjoined
          cases e1 with
          | parrow st1a st2a pa1 ptcls1 =>
              cases e2 with
              | parrow st1b st2b pb1 ptcls2 =>
                  simp only [joinETyps] at hetyp
                  by_cases hshape : st1a == st1b && st2a == st2b
                  · simp only [hshape, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                    cases mem_mergePFnTClosures_inv ptcls1 ptcls2 tcl htcl with
                    | inl h =>
                        exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                          st1a st2a pa1 ptcls1 tcl x rfl h hcap)
                    | inr h =>
                        exact Or.inr (Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1b st2b pb1 ptcls2, p2, pred2⟩
                          st1b st2b pb1 ptcls2 tcl x rfl h hcap))
                  · simp only [hshape, Bool.false_eq_true, ↓reduceIte] at hetyp
                    obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                    exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                      st1a st2a pa1 ptcls1 tcl x rfl htcl hcap)
              | _ =>
                  simp only [joinETyps] at hetyp
                  obtain ⟨rfl, rfl, _, rfl⟩ := ETyp.parrow.inj hetyp
                  exact Or.inl (QTypInQTyp.in_parrow qtInner ⟨ETyp.parrow st1a st2a pa1 ptcls1, p1, pred1⟩
                    st1a st2a pa1 ptcls1 tcl x rfl htcl hcap)
          | int | bool | unit | string => simp [joinETyps] at hetyp
          | ref ls =>
              cases e2 with
              | ref ls2 =>
                  simp [joinETyps] at hetyp
              | _ => simp [joinETyps] at hetyp
          | arrow st1a st2a pa1 tcls1 =>
              cases e2 with
              | arrow st1b st2b pb1 tcls2 =>
                  simp only [joinETyps] at hetyp
                  split_ifs at hetyp
              | _ => simp [joinETyps] at hetyp)
        (fun a b _c h₁₂ _h₂₃ ih₁₂ ih₂₃ hjoined =>
          (ih₂₃ hjoined).elim
            (fun h_e1 => Or.inl (QTypInQTyp.trans a b _ h₁₂ h_e1))
            (fun h => h.elim
              (fun h_e2 => Or.inr (Or.inl (QTypInQTyp.trans a b _ h₁₂ h_e2)))
              (fun heq => ih₁₂ heq)))) rfl
  rcases hdecomp with (h_e1 | h_e2 | h_self)
  · exact h1 h_e1 hqd
  · exact h2 h_e2 hqd
  · subst h_self
    have hpj := qtypGuardDesc?_eq_some_pred_guardClosure hqd
    have hp1 := (joinPredicates_eq_guardClosure hpj).1
    exact h1 (QTypInQTyp.self _) (by simp [qtypGuardDesc?, hp1])

private lemma applyFnTClosure_ok_tagMeaningSub_byIH
  (Q : TagMeaning)
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (IH :
    ∀ (m : Nat), m < fuel →
      ∀ (tm_i : TagMeaning) (ctx_i : TypeContext) (e_i : Expr) (res_i : TypeResult),
      typecheck ctx_i e_i m = .ok res_i →
      wfTagMeaningCtx tm_i ctx_i →
      TagMeaningBounded tm_i ctx_i.nextTag →
      tm_i ⊑ Q → LogIn res_i.tagLog' Q →
      ∃ tm', IsCanonicalExtension tm_i ctx_i e_i res_i tm' ∧ tm' ⊑ Q)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hbounded : TagMeaningBounded tm result1.nextTag')
  (h_laws : tm ⊑ Q) (hL : LogIn r.tagLog' Q)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  ∃ tm',
    tm ⊑ tm' ∧
    TagMeaningBounded tm' r.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx r) ∧
    QTypRespectsTagMeaning tm' r.qualType ∧
    tm' ⊑ Q := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next _hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              bindEnv := BindEnv.bindParam env x result1.nextBind',
              tagEnv := result1.tagEnv', nextTag := result1.nextTag', nextBind := result1.nextBind' + 1,
              nextLoc := result1.nextLoc', regime := result1.regime',
              externRefAllowed := false,
              declaredExternRefs := result1.declared' }
          have htcBody' : typecheck bodyCtx body fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using!
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          rcases IH fuel' (Nat.lt_succ_self _) tm bodyCtx body result3
              htcBody' hwf_body (by simpa [bodyCtx] using hbounded) h_laws hL with
            ⟨tmBody, hcanonBody, h_lawsBody⟩
          have hextBody : tm ⊑ tmBody := hcanonBody.1
          have hctxTm1Body : wfTagMeaningCtx tmBody (ctxAfter ctx result1) :=
            wfTagMeaningCtx_mono hextBody hctxTm1
          have hIH : wfTagMeaningCtx tmBody (ctxAfter bodyCtx result3) :=
            hcanonBody.2.2.1
          refine ⟨tmBody, hextBody, ?_, ?_, ?_, h_lawsBody⟩
          · exact hcanonBody.2.1
          · unfold wfTagMeaningCtx at hctxTm1Body hIH ⊢
            simp only [ctxAfter] at hctxTm1Body hIH ⊢
            exact EnvRespectsTagMeaning_mix tmBody ctx.varEnv result1.memEnv'
              bodyCtx.varEnv result3.memEnv' hctxTm1Body hIH
          · have hresTm3 : QTypRespectsTagMeaning tmBody ⟨etyp3, p3, pred3⟩ := by
              rw [← hqt3]
              exact hcanonBody.2.2.2
            simp only [normalizeAppResultByProvenance]
            split
            · intro q' k' d' hinq hgd
              exact QTypRespectsTagMeaning_of_etyp_noPred tmBody ⟨etyp3, p3, pred3⟩
                ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
            · intro q' k' d' hinq hgd
              exact QTypRespectsTagMeaning_transport_etyp_pred tmBody ⟨etyp3, p3, pred3⟩
                ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern id x retSpec effects capturedEnv argQt captures =>
    have hcapTm : ∀ (name : Name) (qt : QTyp) (n : Nat), (name, qt, n) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt := by
      intro name qt n hmem qtDeep k d hinqDeep hqd
      have hmemCap : (name, qt, n) ∈ fnCapturedEnv
          (FnTClosure.extern id x retSpec effects capturedEnv argQt captures) :=
        by simpa [fnCapturedEnv] using hmem
      have hroot : QTypInQTyp qt result1.qualType :=
        QTypInQTyp.in_arrow qt result1.qualType st1 st2 p tcls
          (FnTClosure.extern id x retSpec effects capturedEnv argQt captures) name hetyp1 hmem_tcl hmemCap
      exact hresTm1 (QTypInQTyp.trans qtDeep qt result1.qualType hinqDeep hroot) hqd
    have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
      QTypRespectsTagMeaning_transport_etyp_pred tm
        ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        hargTm rfl rfl
    rcases applyFnTClosure_extern_canonical_batch tm ctx st1 st2 p p1 argEtyp argPoison
        argPred result1 fuel id x retSpec effects capturedEnv r
        hctxTm1 hbounded hcapTm hargTm' argQt happly with
      ⟨tm', _tagMapping, _nextTag', hbatch, hwithin, hbounded', hwf, hqtm⟩
    exact ⟨tm', ExternBatchTagMeaningExtension.extends_tm hbatch, hbounded', hwf, hqtm,
      hwithin.submap h_laws hL⟩

private lemma applyPFnTClosure_ok_tagMeaningSub_byIH
  (Q : TagMeaning)
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (IH :
    ∀ (m : Nat), m < fuel →
      ∀ (tm_i : TagMeaning) (ctx_i : TypeContext) (e_i : Expr) (res_i : TypeResult),
      typecheck ctx_i e_i m = .ok res_i →
      wfTagMeaningCtx tm_i ctx_i →
      TagMeaningBounded tm_i ctx_i.nextTag →
      tm_i ⊑ Q → LogIn res_i.tagLog' Q →
      ∃ tm', IsCanonicalExtension tm_i ctx_i e_i res_i tm' ∧ tm' ⊑ Q)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hbounded : TagMeaningBounded tm result1.nextTag')
  (h_laws : tm ⊑ Q) (hL : LogIn r.tagLog' Q)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  ∃ tm',
    tm ⊑ tm' ∧
    TagMeaningBounded tm' r.nextTag' ∧
    wfTagMeaningCtx tm' (ctxAfter ctx r) ∧
    QTypRespectsTagMeaning tm' r.qualType ∧
    tm' ⊑ Q := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure, bind, Except.bind] at happly
      split at happly
      · exact absurd happly (Except.error_ne_ok _ _)
      · next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next _hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              bindEnv := BindEnv.bindParam env x result1.nextBind',
              tagEnv := result1.tagEnv', nextTag := result1.nextTag', nextBind := result1.nextBind' + 1,
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime',
              externRefAllowed := false,
              declaredExternRefs := result1.declared' }
          have htcBody' : typecheck bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by
            simpa [typecheck] using htcBody
          have hargTm' : QTypRespectsTagMeaning tm
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using!
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          rcases IH fuel' (Nat.lt_succ_self _) tm bodyCtx (PExpr.toExpr body) result3
              htcBody' hwf_body (by simpa [bodyCtx] using hbounded) h_laws hL with
            ⟨tmBody, hcanonBody, h_lawsBody⟩
          have hextBody : tm ⊑ tmBody := hcanonBody.1
          have hctxTm1Body : wfTagMeaningCtx tmBody (ctxAfter ctx result1) :=
            wfTagMeaningCtx_mono hextBody hctxTm1
          have hIH : wfTagMeaningCtx tmBody (ctxAfter bodyCtx result3) :=
            hcanonBody.2.2.1
          refine ⟨tmBody, hextBody, ?_, ?_, ?_, h_lawsBody⟩
          · exact hcanonBody.2.1
          · unfold wfTagMeaningCtx at hctxTm1Body hIH ⊢
            simp only [ctxAfter] at hctxTm1Body hIH ⊢
            exact EnvRespectsTagMeaning_mix tmBody ctx.varEnv result1.memEnv'
              bodyCtx.varEnv result3.memEnv' hctxTm1Body hIH
          · have hresTm3 : QTypRespectsTagMeaning tmBody ⟨etyp3, p3, pred3⟩ := by
              rw [← hqt3]
              exact hcanonBody.2.2.2
            simp only [normalizeAppResultByProvenance]
            split
            · intro q' k' d' hinq hgd
              exact QTypRespectsTagMeaning_of_etyp_noPred tmBody ⟨etyp3, p3, pred3⟩
                ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
            · intro q' k' d' hinq hgd
              exact QTypRespectsTagMeaning_transport_etyp_pred tmBody ⟨etyp3, p3, pred3⟩
                ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern id x retSpec capturedEnv declaredArgQt captures =>
    have hcapTm : ∀ (name : Name) (qt : QTyp) (n : Nat), (name, qt, n) ∈ capturedEnv →
        QTypRespectsTagMeaning tm qt := by
      intro name qt n hmem qt' k d hinq' hqd'
      exact hresTm1
        (QTypInQTyp.trans qt' qt result1.qualType hinq'
          (QTypInQTyp.in_parrow qt result1.qualType st1 st2 p tcls
            (PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures) name hetyp1 hmem_tcl hmem))
        hqd'
    have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
      QTypRespectsTagMeaning_transport_etyp_pred tm
        ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        hargTm rfl rfl
    cases retSpec with
    | simple typ poison spred =>
        rcases applyPFnTClosure_extern_simple_canonical_batch tm ctx st1 st2 p p1
            argEtyp argPoison argPred result1 fuel id x typ poison spred capturedEnv r
            hctxTm1 hbounded hcapTm hargTm' declaredArgQt happly with
          ⟨tm', _tagMapping, _nextTag', hbatch, hwithin, hbounded', hwf, hqtm⟩
        exact ⟨tm', ExternBatchTagMeaningExtension.extends_tm hbatch, hbounded', hwf, hqtm,
          hwithin.submap h_laws hL⟩
    | nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
        have hmem := applyPFnTClosure_extern_memEnv_eq ctx st1 st2 p p1
          argEtyp argPoison argPred result1 r fuel id x
          (ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures)
          capturedEnv declaredArgQt happly
        have hwf : wfTagMeaningCtx tm (ctxAfter ctx r) := by
          simp only [wfTagMeaningCtx, ctxAfter] at hctxTm1 ⊢
          rwa [hmem]
        have hqtm : QTypRespectsTagMeaning tm r.qualType :=
          applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_of_respects
            (tm := tm) (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
            (result2 := result1) (fuel := fuel) (id := id) (x := x)
            (retSpec := ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures)
            (capturedEnv := capturedEnv) (declaredArgQt := declaredArgQt) (r := r) hctxTm1 hcapTm hargTm'
            (fun {typ} {poison} {spred} hsimple _tagMapping _nextTag' _halloc => by
              cases hsimple)
            happly
        have htag_eq : r.nextTag' = result1.nextTag' := by
          cases fuel with
          | zero => simp [applyPFnTClosure] at happly
          | succ fuel' =>
              unfold applyPFnTClosure at happly
              simp only [bind, Except.bind] at happly
              split at happly
              · simp at happly
              simp only [pure, Except.pure] at happly
              split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                rw [← happly]
                simp only [resolveArgCondQTyp, bind, Except.bind] at hresolve
                split at hresolve
                · simp at hresolve
                · simp only [pure, Except.pure, Except.ok.injEq] at hresolve; rw [← hresolve]
        exact ⟨tm, ExtTreeMap.IsSubmap.refl tm, by rwa [htag_eq], hwf, hqtm, h_laws⟩
    | nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
        have hmem := applyPFnTClosure_extern_memEnv_eq ctx st1 st2 p p1
          argEtyp argPoison argPred result1 r fuel id x
          (ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures)
          capturedEnv declaredArgQt happly
        have hwf : wfTagMeaningCtx tm (ctxAfter ctx r) := by
          simp only [wfTagMeaningCtx, ctxAfter] at hctxTm1 ⊢
          rwa [hmem]
        have hqtm : QTypRespectsTagMeaning tm r.qualType :=
          applyPFnTClosure_extern_ok_QTypRespectsTagMeaning_of_respects
            (tm := tm) (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
            (result2 := result1) (fuel := fuel) (id := id) (x := x)
            (retSpec := ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures)
            (capturedEnv := capturedEnv) (declaredArgQt := declaredArgQt) (r := r) hctxTm1 hcapTm hargTm'
            (fun {typ} {poison} {spred} hsimple _tagMapping _nextTag' _halloc => by
              cases hsimple)
            happly
        have htag_eq : r.nextTag' = result1.nextTag' := by
          cases fuel with
          | zero => simp [applyPFnTClosure] at happly
          | succ fuel' =>
              unfold applyPFnTClosure at happly
              simp only [bind, Except.bind] at happly
              split at happly
              · simp at happly
              simp only [pure, Except.pure] at happly
              split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                rw [← happly]
                simp only [resolveArgCondQTyp, bind, Except.bind] at hresolve
                split at hresolve
                · simp at hresolve
                · simp only [pure, Except.pure, Except.ok.injEq] at hresolve; rw [← hresolve]
        exact ⟨tm, ExtTreeMap.IsSubmap.refl tm, by rwa [htag_eq], hwf, hqtm, h_laws⟩

private lemma applyFnClosuresThreaded_ok_tagMeaningSub_byIH
  (Q : TagMeaning)
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (allTcls todo : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (cursor : Tag × Loc) (bn : Nat) (fuel : Nat)
  (IH :
    ∀ (m : Nat), m < fuel →
      ∀ (tm_i : TagMeaning) (ctx_i : TypeContext) (e_i : Expr) (res_i : TypeResult),
      typecheck ctx_i e_i m = .ok res_i →
      wfTagMeaningCtx tm_i ctx_i →
      TagMeaningBounded tm_i ctx_i.nextTag →
      tm_i ⊑ Q → LogIn res_i.tagLog' Q →
      ∃ tm', IsCanonicalExtension tm_i ctx_i e_i res_i tm' ∧ tm' ⊑ Q)
  (first : TypeResult) (rest : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hbounded : TagMeaningBounded tm cursor.1)
  (h_laws : tm ⊑ Q) (hL : ∀ r ∈ first :: rest, LogIn r.tagLog' Q)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p allTcls)
  (hmem_todo : ∀ tcl, tcl ∈ todo → tcl ∈ allTcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hthread :
    applyClosuresThreaded
      (fun tcl cursor bn =>
        applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor bn fuel)
      todo cursor bn = .ok (first :: rest)) :
  ∃ (tm' : TagMeaning) (last : TypeResult),
    tm ⊑ tm' ∧
    last ∈ first :: rest ∧
    TagMeaningBounded tm' last.nextTag' ∧
    (∀ r, r ∈ first :: rest → wfTagMeaningCtx tm' (ctxAfter ctx r)) ∧
    (∀ r, r ∈ first :: rest → QTypRespectsTagMeaning tm' r.qualType) ∧
    tm' ⊑ Q := by
  induction todo generalizing tm cursor bn first rest with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
  | cons tcl todo ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hhead :
          applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor bn fuel with
      | error err =>
          simp [hhead] at hthread
      | ok head =>
          simp [hhead] at hthread
          cases htail :
              applyClosuresThreaded
                (fun tcl cursor bn =>
                  applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
                    ctx result1 cursor bn fuel)
                todo (head.nextTag', head.nextLoc') head.nextBind' with
          | error err =>
              simp [htail] at hthread
          | ok tailResults =>
              simp [htail, pure, Except.pure] at hthread
              have hhead_eq : head = first := hthread.1
              have htail_eq : tailResults = rest := hthread.2
              let cursorResult : TypeResult :=
                { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
              have hctxCursor : wfTagMeaningCtx tm (ctxAfter ctx cursorResult) := by
                simpa [ctxAfter, cursorResult] using! hctxTm1
              have hresCursor : QTypRespectsTagMeaning tm cursorResult.qualType := by
                intro qt' k d hinq hqd
                exact hresTm1 (by simpa [cursorResult] using hinq) hqd
              have hetypCursor :
                  cursorResult.qualType.etyp = ETyp.arrow st1 st2 p allTcls := by
                simpa [cursorResult] using hetyp1
              have happlyOld :
                  applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
                    ctx cursorResult fuel = .ok head := by
                unfold applyFnTClosure
                unfold applyFnTClosureAtCursor at hhead
                simpa [cursorResult] using hhead
              rcases applyFnTClosure_ok_tagMeaningSub_byIH
                  (Q := Q) (tm := tm)
                  (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                  (tcls := allTcls)
                  (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
                  (result1 := cursorResult) (fuel := fuel)
                  (IH := IH)
                  (tcl := tcl) (r := head)
                  hctxCursor hresCursor (by simpa [cursorResult] using hbounded) h_laws
                  (by rw [hhead_eq]; exact hL first (List.mem_cons_self ..))
                  hetypCursor (hmem_todo tcl (by simp)) hargTm happlyOld with
                ⟨tmHead, hextHead, hboundedHead, hwfHead, hqHead, h_lawsHead⟩
              cases tailResults with
              | nil =>
                  refine ⟨tmHead, head, hextHead, by simp [← hhead_eq, ← htail_eq],
                    hboundedHead, ?_, ?_, h_lawsHead⟩
                  · intro r hr
                    have hr' : r = head := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rw [hr']
                    exact hwfHead
                  · intro r hr
                    have hr' : r = head := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rw [hr']
                    intro qt' k d hinq hqd
                    exact hqHead hinq hqd
              | cons tailFirst tailRest =>
                  have hctxHeadBase : wfTagMeaningCtx tmHead (ctxAfter ctx result1) :=
                    wfTagMeaningCtx_mono hextHead hctxTm1
                  have hresHeadBase : QTypRespectsTagMeaning tmHead result1.qualType :=
                    QTypRespectsTagMeaning_mono hextHead hresTm1
                  have hargHead : QTypRespectsTagMeaning tmHead
                      ⟨argEtyp, argPoison, argPred⟩ :=
                    QTypRespectsTagMeaning_mono hextHead hargTm
                  rcases ih tmHead (head.nextTag', head.nextLoc') head.nextBind' tailFirst tailRest
                      hctxHeadBase hresHeadBase hboundedHead h_lawsHead
                      (fun r hr => hL r (by
                        rw [← htail_eq]; exact List.mem_cons_of_mem _ hr))
                      (fun tcl htcl => hmem_todo tcl (by simp [htcl]))
                      hargHead htail with
                    ⟨tmTail, last, hextTail, hlastTail, hboundedLast,
                      hwfTail, hqTail, h_lawsTail⟩
                  refine ⟨tmTail, last, ExtTreeMap.IsSubmap.trans hextHead hextTail,
                    ?_, hboundedLast, ?_, ?_, h_lawsTail⟩
                  · simp [← hhead_eq, ← htail_eq, hlastTail]
                  · intro r hr
                    have hr' : r = head ∨ r ∈ tailFirst :: tailRest := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rcases hr' with hr' | hr'
                    · rw [hr']
                      exact wfTagMeaningCtx_mono hextTail hwfHead
                    · exact hwfTail r hr'
                  · intro r hr
                    have hr' : r = head ∨ r ∈ tailFirst :: tailRest := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rcases hr' with hr' | hr'
                    · rw [hr']
                      intro qt' k d hinq hqd
                      exact (QTypRespectsTagMeaning_mono hextTail hqHead) hinq hqd
                    · intro qt' k d hinq hqd
                      exact hqTail r hr' hinq hqd

private lemma applyPFnClosuresThreaded_ok_tagMeaningSub_byIH
  (Q : TagMeaning)
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (allTcls todo : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (cursor : Tag × Loc) (bn : Nat) (fuel : Nat)
  (IH :
    ∀ (m : Nat), m < fuel →
      ∀ (tm_i : TagMeaning) (ctx_i : TypeContext) (e_i : Expr) (res_i : TypeResult),
      typecheck ctx_i e_i m = .ok res_i →
      wfTagMeaningCtx tm_i ctx_i →
      TagMeaningBounded tm_i ctx_i.nextTag →
      tm_i ⊑ Q → LogIn res_i.tagLog' Q →
      ∃ tm', IsCanonicalExtension tm_i ctx_i e_i res_i tm' ∧ tm' ⊑ Q)
  (first : TypeResult) (rest : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hbounded : TagMeaningBounded tm cursor.1)
  (h_laws : tm ⊑ Q) (hL : ∀ r ∈ first :: rest, LogIn r.tagLog' Q)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p allTcls)
  (hmem_todo : ∀ tcl, tcl ∈ todo → tcl ∈ allTcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hthread :
    applyClosuresThreaded
      (fun tcl cursor bn =>
        applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
          ctx result1 cursor bn fuel)
      todo cursor bn = .ok (first :: rest)) :
  ∃ (tm' : TagMeaning) (last : TypeResult),
    tm ⊑ tm' ∧
    last ∈ first :: rest ∧
    TagMeaningBounded tm' last.nextTag' ∧
    (∀ r, r ∈ first :: rest → wfTagMeaningCtx tm' (ctxAfter ctx r)) ∧
    (∀ r, r ∈ first :: rest → QTypRespectsTagMeaning tm' r.qualType) ∧
    tm' ⊑ Q := by
  induction todo generalizing tm cursor bn first rest with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
  | cons tcl todo ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hhead :
          applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
            ctx result1 cursor bn fuel with
      | error err =>
          simp [hhead] at hthread
      | ok head =>
          simp [hhead] at hthread
          cases htail :
              applyClosuresThreaded
                (fun tcl cursor bn =>
                  applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
                    ctx result1 cursor bn fuel)
                todo (head.nextTag', head.nextLoc') head.nextBind' with
          | error err =>
              simp [htail] at hthread
          | ok tailResults =>
              simp [htail, pure, Except.pure] at hthread
              have hhead_eq : head = first := hthread.1
              have htail_eq : tailResults = rest := hthread.2
              let cursorResult : TypeResult :=
                { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
              have hctxCursor : wfTagMeaningCtx tm (ctxAfter ctx cursorResult) := by
                simpa [ctxAfter, cursorResult] using! hctxTm1
              have hresCursor : QTypRespectsTagMeaning tm cursorResult.qualType := by
                intro qt' k d hinq hqd
                exact hresTm1 (by simpa [cursorResult] using hinq) hqd
              have hetypCursor :
                  cursorResult.qualType.etyp = ETyp.parrow st1 st2 p allTcls := by
                simpa [cursorResult] using hetyp1
              have happlyOld :
                  applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred
                    ctx cursorResult fuel = .ok head := by
                unfold applyPFnTClosure
                unfold applyPFnTClosureAtCursor at hhead
                simpa [cursorResult] using hhead
              rcases applyPFnTClosure_ok_tagMeaningSub_byIH
                  (Q := Q) (tm := tm)
                  (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                  (tcls := allTcls)
                  (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
                  (result1 := cursorResult) (fuel := fuel)
                  (IH := IH)
                  (tcl := tcl) (r := head)
                  hctxCursor hresCursor (by simpa [cursorResult] using hbounded) h_laws
                  (by rw [hhead_eq]; exact hL first (List.mem_cons_self ..))
                  hetypCursor (hmem_todo tcl (by simp)) hargTm happlyOld with
                ⟨tmHead, hextHead, hboundedHead, hwfHead, hqHead, h_lawsHead⟩
              cases tailResults with
              | nil =>
                  refine ⟨tmHead, head, hextHead, by simp [← hhead_eq, ← htail_eq],
                    hboundedHead, ?_, ?_, h_lawsHead⟩
                  · intro r hr
                    have hr' : r = head := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rw [hr']
                    exact hwfHead
                  · intro r hr
                    have hr' : r = head := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rw [hr']
                    intro qt' k d hinq hqd
                    exact hqHead hinq hqd
              | cons tailFirst tailRest =>
                  have hctxHeadBase : wfTagMeaningCtx tmHead (ctxAfter ctx result1) :=
                    wfTagMeaningCtx_mono hextHead hctxTm1
                  have hresHeadBase : QTypRespectsTagMeaning tmHead result1.qualType :=
                    QTypRespectsTagMeaning_mono hextHead hresTm1
                  have hargHead : QTypRespectsTagMeaning tmHead
                      ⟨argEtyp, argPoison, argPred⟩ :=
                    QTypRespectsTagMeaning_mono hextHead hargTm
                  rcases ih tmHead (head.nextTag', head.nextLoc') head.nextBind' tailFirst tailRest
                      hctxHeadBase hresHeadBase hboundedHead h_lawsHead
                      (fun r hr => hL r (by
                        rw [← htail_eq]; exact List.mem_cons_of_mem _ hr))
                      (fun tcl htcl => hmem_todo tcl (by simp [htcl]))
                      hargHead htail with
                    ⟨tmTail, last, hextTail, hlastTail, hboundedLast,
                      hwfTail, hqTail, h_lawsTail⟩
                  refine ⟨tmTail, last, ExtTreeMap.IsSubmap.trans hextHead hextTail,
                    ?_, hboundedLast, ?_, ?_, h_lawsTail⟩
                  · simp [← hhead_eq, ← htail_eq, hlastTail]
                  · intro r hr
                    have hr' : r = head ∨ r ∈ tailFirst :: tailRest := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rcases hr' with hr' | hr'
                    · rw [hr']
                      exact wfTagMeaningCtx_mono hextTail hwfHead
                    · exact hwfTail r hr'
                  · intro r hr
                    have hr' : r = head ∨ r ∈ tailFirst :: tailRest := by
                      simpa [← hhead_eq, ← htail_eq] using hr
                    rcases hr' with hr' | hr'
                    · rw [hr']
                      intro qt' k d hinq hqd
                      exact (QTypRespectsTagMeaning_mono hextTail hqHead) hinq hqd
                    · intro qt' k d hinq hqd
                      exact hqTail r hr' hinq hqd

private lemma join_transport_wfTagMeaningCtx_byFirst
  (tm : TagMeaning) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : wfTagMeaningCtx tm (ctxAfter ctx first)) :
  wfTagMeaningCtx tm (ctxAfter ctx res) := by
  unfold wfTagMeaningCtx
  rw [ctxAfter]
  have h_first_env : EnvRespectsTagMeaning tm ctx.varEnv first.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using h_first
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_tm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        EnvRespectsTagMeaning tm ctx.varEnv acc.2.1 →
        EnvRespectsTagMeaning tm ctx.varEnv acc'.2.1 := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hacc1 : EnvRespectsTagMeaning tm ctx.varEnv (joinMemEnvsStrong acc.2.1 x.memEnv') :=
              EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv acc.2.1 x.memEnv' hacc
            exact ih _ hfold hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              exact h_fold_tm rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag')
                a hfold h_first_env

private lemma joinTypeResults_QTypRespectsTagMeaning_byMembers
  (tm : TagMeaning)
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : QTypRespectsTagMeaning tm first.qualType)
  (h_rest : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType) :
  QTypRespectsTagMeaning tm res.qualType := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_qtm :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        QTypRespectsTagMeaning tm ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ →
        (∀ r ∈ rs', QTypRespectsTagMeaning tm r.qualType) →
        QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ := by
    intro rs' acc acc' hfold hacc hrs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold; exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hx : QTypRespectsTagMeaning tm x.qualType := hrs x (by simp)
            have hacc1 : QTypRespectsTagMeaning tm ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ :=
              QTypRespectsTagMeaning_joinStep tm acc.1 resEtyp acc.2.2.1 resPoison
                acc.2.2.2.1 resPred hacc (hqx ▸ hx)
            have hrs_tail : ∀ r ∈ xs, QTypRespectsTagMeaning tm r.qualType := by
              intro r hr; exact hrs r (by simp [hr])
            show QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error _ => erw [hcheck] at h_join; simp at h_join
      | ok _ =>
          erw [hcheck] at h_join; simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error _ => erw [hfold] at h_join; simp at h_join
          | ok a =>
              rcases a with
                ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred,
                  joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag⟩
              erw [hfold] at h_join
              simp at h_join
              subst res
              have h_first_qtm : QTypRespectsTagMeaning tm ⟨etyp, poison, pred⟩ :=
                hqt ▸ h_first
              have hacc_qtm :
                  QTypRespectsTagMeaning tm ⟨joinedEtyp, joinedPoison, joinedPred⟩ :=
                h_fold_qtm rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred,
                    joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag)
                  hfold h_first_qtm h_rest
              cases joinedEtyp with
              | arrow st1 st2 p tcls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_of_etyp_noPred tm
                      ⟨ETyp.arrow st1 st2 p tcls, joinedPoison, joinedPred⟩
                      ⟨ETyp.arrow st1 st2 p tcls, joinPoison ctx.pc joinedPoison, Predicate.noPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | parrow st1 st2 p tcls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_of_etyp_noPred tm
                      ⟨ETyp.parrow st1 st2 p tcls, joinedPoison, joinedPred⟩
                      ⟨ETyp.parrow st1 st2 p tcls, joinPoison ctx.pc joinedPoison, Predicate.noPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | int =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.int, joinedPoison, joinedPred⟩
                      ⟨ETyp.int, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | bool =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.bool, joinedPoison, joinedPred⟩
                      ⟨ETyp.bool, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | unit =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.unit, joinedPoison, joinedPred⟩
                      ⟨ETyp.unit, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | string =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.string, joinedPoison, joinedPred⟩
                      ⟨ETyp.string, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd
              | ref ls =>
                  intro qt' k d hinq hqd
                  exact
                    QTypRespectsTagMeaning_transport_etyp_pred tm
                      ⟨ETyp.ref ls, joinedPoison, joinedPred⟩
                      ⟨ETyp.ref ls, joinPoison ctx.pc joinedPoison, joinedPred⟩
                      hacc_qtm rfl rfl hinq hqd

private lemma typecheck_extends_tagMeaning_nonApp_byIH
    (Q : TagMeaning)
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (htc : typecheck ctx e fuel = .ok res)
    (hP : tm ⊑ Q) (hL : LogIn res.tagLog' Q)
    (hnotApp : ∀ e1 e2, e ≠ Expr.app e1 e2)
    (hnotExternVal : ∀ id typ poison pred, e ≠ Expr.externVal id typ poison pred)
    (IH : ∀ m, m < fuel →
      ∀ (tm_i : TagMeaning) (ctx_i : TypeContext) (e_i : Expr) (res_i : TypeResult),
        wfTagMeaningCtx tm_i ctx_i →
        TagMeaningBounded tm_i ctx_i.nextTag →
        tm_i ⊑ Q → LogIn res_i.tagLog' Q →
        typecheck ctx_i e_i m = .ok res_i →
        ∃ tm', IsCanonicalExtension tm_i ctx_i e_i res_i tm' ∧ tm' ⊑ Q) :
    ∃ tm', IsCanonicalExtension tm ctx e res tm' ∧ tm' ⊑ Q := by
  have htc_full := htc
  unfold typecheck at htc
  cases fuel with
  | zero =>
      unfold typecheckExpr at htc
      simp at htc
  | succ fuel' =>
      unfold typecheckExpr at htc
      cases e with
      | num n =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.num n) (Nat.succ fuel') res htc_full)
          unfold typecheckInt at htc
          simp [pure, Except.pure] at htc
          cases htc
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
      | bool b =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.bool b) (Nat.succ fuel') res htc_full)
          unfold typecheckBool at htc
          simp [pure, Except.pure] at htc
          cases htc
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
      | unit =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx Expr.unit (Nat.succ fuel') res htc_full)
          unfold typecheckUnit at htc
          simp [pure, Except.pure] at htc
          cases htc
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
      | str s =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.str s) (Nat.succ fuel') res htc_full)
          unfold typecheckString at htc
          simp [pure, Except.pure] at htc
          cases htc
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
      | var x =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.var x) (Nat.succ fuel') res htc_full)
          simp at htc
          unfold typecheckVar at htc
          simp only [bind, Except.bind] at htc
          cases hlookup : ctx.varEnv.lookup x with
          | none => simp [hlookup] at htc
          | some qt =>
            simp [hlookup] at htc
            cases qt with
            | mk etyp poison pred =>
              simp at htc
              cases pred with
              | noPred =>
                  simp [pure, Except.pure] at htc
                  cases htc
                  refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
                  · exact hb_res
                  · simpa [wfTagMeaningCtx, ctxAfter]
                  · exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                      ⟨etyp, poison, Predicate.noPred⟩ _
                      (wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ h_wf hlookup)
                      (by simp) (by simp [qtypGuardDesc?])
              | guardOnly k =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    revert htc
                    generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none =>
                        intro htc
                        simp at htc
                        cases htc
                        refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
                        · exact hb_res
                        · simpa [wfTagMeaningCtx, ctxAfter]
                        · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _
                            hfn (by simp [qtypGuardDesc?])
                    | some tv =>
                        cases tv with
                        | mk val deps =>
                          cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                            refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
                          · exact hb_res
                          · simpa [wfTagMeaningCtx, ctxAfter]
                          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _
                              hfn (by simp [qtypGuardDesc?])
                          · exact hb_res
                          · simpa [wfTagMeaningCtx, ctxAfter]
                          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _
                              hfn (by simp [qtypGuardDesc?])
                  | true => simp [hfn] at htc
              | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    have hqt_orig :
                        QTypRespectsTagMeaning tm
                          ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩ :=
                      wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ h_wf hlookup
                    revert htc
                    generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none =>
                        intro htc
                        simp at htc
                        cases htc
                        refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
                        · exact hb_res
                        · simpa [wfTagMeaningCtx, ctxAfter]
                        · exact QTypRespectsTagMeaning_transport_etyp_pred tm
                            ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩
                            ⟨etyp, joinPoison ctx.pc poison,
                              Predicate.guardClosure k tcls ptcls body_t⟩
                            hqt_orig rfl rfl
                    | some tv =>
                        cases tv with
                        | mk val deps =>
                          cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                            refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
                          · exact hb_res
                          · simpa [wfTagMeaningCtx, ctxAfter]
                          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _
                              hfn (by simp [qtypGuardDesc?])
                          · exact hb_res
                          · simpa [wfTagMeaningCtx, ctxAfter]
                          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _
                              hfn (by simp [qtypGuardDesc?])
                  | true => simp [hfn] at htc
      | fn x st1 body st2 =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.fn x st1 body st2) (Nat.succ fuel') res
                htc_full)
          have hfn := typecheckFn_ok_eq htc
          subst hfn
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_fn_regular tm ctx x st1 st2 ctx.pc body h_wf
      | pfn x st1 body st2 =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.pfn x st1 body st2) (Nat.succ fuel') res
                htc_full)
          unfold typecheckPfn at htc
          simp [bind, Except.bind] at htc
          cases h_topexpr : body.toPExpr with
          | error _ => simp [h_topexpr] at htc
          | ok pbody =>
              simp [h_topexpr, pure, Except.pure] at htc
              subst htc
              refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
              · exact hb_res
              · simpa [wfTagMeaningCtx, ctxAfter]
              · exact QTypRespectsTagMeaning_pfn_regular tm ctx x st1 st2 ctx.pc pbody h_wf
      | externVal id typ poison pred =>
          exact False.elim (hnotExternVal id typ poison pred rfl)
      | externRef id refPoison refPred cellPoison cellPred =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.externRef id refPoison refPred cellPoison cellPred)
                (Nat.succ fuel') res htc_full)
          simp only [typecheckExternRef] at htc
          simp [bind, Except.bind, pure, Except.pure] at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          cases htc
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simp only [wfTagMeaningCtx, ctxAfter]
            exact EnvRespectsTagMeaning_updateMemEnv tm ctx.varEnv ctx.memEnv ctx.nextLoc
              ⟨ETyp.int, true, Predicate.noPred⟩ rfl h_wf
              (QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl (by simp [qtypGuardDesc?]))
          · exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl (by simp [qtypGuardDesc?])
      | externFn id arg argTyp argPoison argPred retSpec effects cap =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.externFn id arg argTyp argPoison argPred retSpec effects cap)
                (Nat.succ fuel') res htc_full)
          obtain ⟨argQt, _, htc_res⟩ :=
            typecheckExternFn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec effects res htc
          subst htc_res
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_fn_extern tm ctx id _ _ _ ctx.pc _ _ h_wf
      | externPfn id arg argTyp argPoison argPred retSpec cap =>
          have hb_res : TagMeaningBounded tm res.nextTag' :=
            h_bounded.mono
              (typecheck_nextTag_mono ctx (Expr.externPfn id arg argTyp argPoison argPred retSpec cap)
                (Nat.succ fuel') res htc_full)
          obtain ⟨argQt, _, htc_res⟩ :=
            typecheckExternPfn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec res htc
          subst htc_res
          refine ⟨tm, IsCanonicalExtension.refl ?_ ?_ ?_, hP⟩
          · exact hb_res
          · simpa [wfTagMeaningCtx, ctxAfter]
          · exact QTypRespectsTagMeaning_pfn_extern tm ctx id _ _ _ ctx.pc _ h_wf
      | unaryop op e1 =>
          have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
          rcases hstruct with
            ⟨result1, result_etyp, htc1, hopEtyp, hmemEnv, _htagEnv, _hnextLoc,
              hnextTag, _hregime, hetyp, _hpoison, hpred⟩
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa using! htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              (hL.of_log_eq (typecheckUnaryOp_tagLog htc htc1)) htc1' with
            ⟨tm1, hcanon1, hP1⟩
          have hresTm : QTypRespectsTagMeaning tm1 res.qualType := by
            have hnf : result_etyp.isFunctionType = false := by
              have : result_etyp = .bool := by
                revert hopEtyp
                unfold opUnaryEType?
                split <;> simp [eq_comm]
              subst this
              decide
            apply QTypRespectsTagMeaning_of_nonFunction_noGuard
            · rw [hetyp]
              exact hnf
            · simp [qtypGuardDesc?, hpred]
          refine ⟨tm1, ?_, hP1⟩
          exact ⟨IsCanonicalExtension.extends_tm hcanon1,
            by simpa [hnextTag] using IsCanonicalExtension.bounded hcanon1,
            by simpa [wfTagMeaningCtx, ctxAfter, hmemEnv] using
              IsCanonicalExtension.wfCtx hcanon1,
            hresTm⟩
      | deref e1 =>
          cases fuel' with
          | zero =>
              simp [typecheckDeref] at htc
          | succ fuel'' =>
              have hstruct := typecheckDeref_structure ctx e1 (Nat.succ fuel'') res htc
              rcases hstruct with
                ⟨result1, htc1, hmem, _htag, _hloc, hnextTag, _hregime⟩
              have htc1' : typecheck ctx e1 fuel'' = .ok result1 := by
                simpa [typecheck] using htc1
              rcases IH fuel'' (by omega) tm ctx e1 result1 h_wf h_bounded hP
                  (hL.of_log_eq (typecheckDeref_tagLog htc htc1)) htc1' with
                ⟨tm1, hcanon1, hP1⟩
              have hresTm : QTypRespectsTagMeaning tm1 res.qualType :=
                typecheckDeref_qtypRespects tm1 ctx e1 fuel'' res result1
                  (by simpa [ctxAfter] using IsCanonicalExtension.wfCtx hcanon1)
                  (by simpa using htc1) htc
              refine ⟨tm1, ?_, hP1⟩
              exact ⟨IsCanonicalExtension.extends_tm hcanon1,
                by simpa [hnextTag] using IsCanonicalExtension.bounded hcanon1,
                by simpa [wfTagMeaningCtx, ctxAfter, hmem] using
                  IsCanonicalExtension.wfCtx hcanon1,
                hresTm⟩
      | newRef e1 =>
          have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
          rcases hstruct with
            ⟨result1, l, htc1, hl, hInt, hRef_res, _hpoison_res, hpred_res,
              hmem_res, _htag_res, _hnextLoc_res, hnextTag_res, _hregime_res⟩
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa using! htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              (hL.of_log_eq (typecheckNewRef_tagLog htc htc1)) htc1' with
            ⟨tm1, hcanon1, hP1⟩
          let storedQt : QTyp :=
            ⟨ETyp.int, joinPoison ctx.pc result1.qualType.poison,
              if ctx.pc then Predicate.noPred else result1.qualType.pred⟩
          have hstored_qtm : QTypRespectsTagMeaning tm1 storedQt := by
            by_cases hpc : ctx.pc = true
            · have hnotfun : storedQt.etyp.isFunctionType = false := by
                simp [storedQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hguard : qtypGuardDesc? storedQt = none := by
                simp [storedQt, hpc, qtypGuardDesc?]
              exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm1 storedQt hnotfun hguard
            · exact
                QTypRespectsTagMeaning_transport_etyp_pred tm1 result1.qualType storedQt
                  (IsCanonicalExtension.respectsResult hcanon1)
                  (by simpa [storedQt] using hInt.symm)
                  (by simp [storedQt, hpc])
          have hEnv_res : EnvRespectsTagMeaning tm1 ctx.varEnv res.memEnv' := by
            have hEnv1 : EnvRespectsTagMeaning tm1 ctx.varEnv result1.memEnv' := by
              simpa [wfTagMeaningCtx, ctxAfter] using IsCanonicalExtension.wfCtx hcanon1
            rw [hmem_res, hl]
            exact
              EnvRespectsTagMeaning_updateMemEnv
                tm1 ctx.varEnv result1.memEnv' result1.nextLoc' storedQt rfl hEnv1 hstored_qtm
          have hresTm : QTypRespectsTagMeaning tm1 res.qualType := by
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hRef_res, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hguard : qtypGuardDesc? res.qualType = none := by
              simp [qtypGuardDesc?, hpred_res]
            intro qt' k d hinq hqd
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm1 res.qualType
              hnotfun hguard hinq hqd
          refine ⟨tm1, ?_, hP1⟩
          exact ⟨IsCanonicalExtension.extends_tm hcanon1,
            by simpa [hnextTag_res] using IsCanonicalExtension.bounded hcanon1,
            wfTagMeaningCtx_ctxAfter tm1 ctx res hEnv_res,
            hresTm⟩
      | op e1 op e2 =>
          have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
          rcases hstruct with
            ⟨result1, result2, result_etyp, htc1, htc2, hopEtyp, hmemEnv, _htagEnv,
              _hnextLoc, hnextTag, _hregime, hetyp, _hpoison, hpred⟩
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa using! htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              (hL.of_log_eq (typecheckOp_tagLog htc htc1 htc2)).left htc1' with
            ⟨tm1, hcanon1, hP1⟩
          have hwf_mid : wfTagMeaningCtx tm1 (updateCtxFromResult ctx result1) := by
            simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
              IsCanonicalExtension.wfCtx hcanon1
          have hb_mid : TagMeaningBounded tm1 (updateCtxFromResult ctx result1).nextTag := by
            simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
          have htc2' :
              typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
            simpa using! htc2
          rcases IH (fuel' - 1) (by omega) tm1 (updateCtxFromResult ctx result1) e2
              result2 hwf_mid hb_mid hP1
              (hL.of_log_eq (typecheckOp_tagLog htc htc1 htc2)).right htc2' with
            ⟨tm2, hcanon2, hP2⟩
          have hcanon_trans := IsCanonicalExtension.trans hcanon1 hcanon2
          have hresTm : QTypRespectsTagMeaning tm2 res.qualType := by
            have hnf : result_etyp.isFunctionType = false := by
              have : result_etyp = .int ∨ result_etyp = .bool := by
                revert hopEtyp
                unfold opEType?
                split <;> simp [eq_comm] <;> tauto
              rcases this with rfl | rfl <;> decide
            apply QTypRespectsTagMeaning_of_nonFunction_noGuard
            · rw [hetyp]
              exact hnf
            · simp [qtypGuardDesc?, hpred]
          refine ⟨tm2, ?_, hP2⟩
          exact ⟨hcanon_trans.1,
            by simpa [hnextTag] using hcanon_trans.2.1,
            by simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hmemEnv] using
              hcanon_trans.2.2.1,
            hresTm⟩
      | seq e1 e2 =>
          have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
          rcases hstruct with ⟨result1, ctx', res, htc1, hctx', htc2, rfl⟩
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa using! htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              hL.left htc1' with
            ⟨tm1, hcanon1, hP1⟩
          have hwf_mid : wfTagMeaningCtx tm1 ctx' := by
            rw [hctx']
            simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
              IsCanonicalExtension.wfCtx hcanon1
          have hb_mid : TagMeaningBounded tm1 ctx'.nextTag := by
            rw [hctx']
            simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
          have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok res := by
            simpa using! htc2
          rcases IH (fuel' - 1) (by omega) tm1 ctx' e2 res hwf_mid hb_mid hP1 hL.right htc2' with
            ⟨tm2, hcanon2, hP2⟩
          have hcanon_trans := IsCanonicalExtension.trans hcanon1 hcanon2
          refine ⟨tm2, ?_, hP2⟩
          exact ⟨hcanon_trans.1, hcanon_trans.2.1,
            by simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hctx'] using
              hcanon_trans.2.2.1,
            hcanon_trans.2.2.2⟩
      | vlet x e1 e2 =>
          have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
          rcases hstruct with
            ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp_res, hmemEnv, _htagEnv,
              _hnextLoc, hnextTag, _hregime, _hpoison_res, hpred_res⟩
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa using! htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              (hL.of_log_eq (typecheckVlet_tagLog htc htc1 (hctx' ▸ htc2))).left htc1' with
            ⟨tm1, hcanon1, hP1⟩
          have hwf_mid : wfTagMeaningCtx tm1 ctx' := by
            rw [hctx']
            have hwf_after : wfTagMeaningCtx tm1 (ctxAfter ctx result1) :=
              IsCanonicalExtension.wfCtx hcanon1
            simp only [wfTagMeaningCtx, ctxAfter] at hwf_after
            let ctxBase : TypeContext :=
              ⟨ctx.pc, result1.regime', result1.memEnv', ctx.varEnv,
               ctx.bindEnv.insert x result1.nextBind', result1.tagEnv',
               result1.nextLoc', result1.nextTag', result1.nextBind' + 1, ctx.pureCtx, ctx.externRegime,
               ctx.externRefAllowed, result1.declared'⟩
            exact wfTagMeaningCtx_varEnv_ext tm1 ctxBase x result1.qualType
              (by simpa [wfTagMeaningCtx, ctxAfter, ctxBase] using hwf_after)
              (IsCanonicalExtension.respectsResult hcanon1)
          have hb_mid : TagMeaningBounded tm1 ctx'.nextTag := by
            rw [hctx']
            simpa using IsCanonicalExtension.bounded hcanon1
          have htc2' : typecheck ctx' e2 (fuel' - 1) = .ok result2 := by
            simpa using! htc2
          rcases IH (fuel' - 1) (by omega) tm1 ctx' e2 result2 hwf_mid hb_mid hP1
              (hL.of_log_eq (typecheckVlet_tagLog htc htc1 (hctx' ▸ htc2))).right htc2' with
            ⟨tm2, hcanon2, hP2⟩
          have hcanon_trans := IsCanonicalExtension.trans hcanon1 hcanon2
          have hresTm : QTypRespectsTagMeaning tm2 res.qualType :=
            QTypRespectsTagMeaning_transport_etyp_pred tm2 result2.qualType res.qualType
              (IsCanonicalExtension.respectsResult hcanon2)
              (by rw [hetyp_res]) (by rw [hpred_res])
          have hTm_final : wfTagMeaningCtx tm2 (ctxAfter ctx res) := by
            have hcanon2_wf := IsCanonicalExtension.wfCtx hcanon2
            unfold wfTagMeaningCtx at hcanon2_wf ⊢
            simp only [ctxAfter, hmemEnv]
            have hTm2' :
                EnvRespectsTagMeaning tm2 (ctx.varEnv.update x result1.qualType)
                  result2.memEnv' := by
              simpa [hctx'] using! hcanon2_wf
            refine EnvRespectsTagMeaning_of_update tm2 x ctx.varEnv result1.qualType
              result2.memEnv' hTm2' ?_
            intro qt hlookup
            exact QTypRespectsTagMeaning_mono hcanon_trans.1
              (wfTagMeaningCtx_var_lookup_qtyp tm ctx x qt h_wf hlookup)
          refine ⟨tm2, ?_, hP2⟩
          exact ⟨hcanon_trans.1, by simpa [hnextTag] using hcanon_trans.2.1,
            hTm_final, hresTm⟩
      | assign e1 e2 =>
          have hstruct := typecheckAssign_structure ctx e1 e2 fuel' res htc
          rcases hstruct with
            ⟨result1s, result2s, _ls, htc1s, _hRef, htc2s, _hInt, _hnextLoc,
              hnextTag, _hregime, hetyp_res, _hpoison_res, hpred_res⟩
          have hmem_formula := typecheckAssign_memEnv_formula ctx e1 e2 fuel' res htc
          rcases hmem_formula with
            ⟨result1, result2, ls, htc1, _hRef, htc2, _hInt, hmem_res, _hRegime⟩
          have hresult1_eq : result1 = result1s := by
            have h :
                (Except.ok result1 : TypecheckM TypeResult) = Except.ok result1s := by
              rw [← htc1, ← htc1s]
            exact Except.ok.inj h
          subst result1s
          have hresult2_eq : result2 = result2s := by
            have h :
                (Except.ok result2 : TypecheckM TypeResult) = Except.ok result2s := by
              rw [← htc2, ← htc2s]
            exact Except.ok.inj h
          subst result2s
          have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by
            simpa [typecheck] using htc1
          rcases IH (fuel' - 1) (by omega) tm ctx e1 result1 h_wf h_bounded hP
              (hL.of_log_eq (typecheckAssign_tagLog htc htc1 htc2)).left htc1' with
            ⟨tm1, hcanon1, hP1⟩
          have hwf_mid : wfTagMeaningCtx tm1 (updateCtxFromResult ctx result1) := by
            simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
              IsCanonicalExtension.wfCtx hcanon1
          have hb_mid : TagMeaningBounded tm1 (updateCtxFromResult ctx result1).nextTag := by
            simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
          have htc2' :
              typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
            simpa [typecheck] using htc2
          rcases IH (fuel' - 1) (by omega) tm1 (updateCtxFromResult ctx result1) e2
              result2 hwf_mid hb_mid hP1
              (hL.of_log_eq (typecheckAssign_tagLog htc htc1 htc2)).right htc2' with
            ⟨tm2, hcanon2, hP2⟩
          have hcanon_trans := IsCanonicalExtension.trans hcanon1 hcanon2
          let storedPred : Predicate :=
            if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred
            else result2.qualType.pred
          let storedQt : QTyp :=
            { etyp := ETyp.int
              poison := joinPoison ctx.pc
                (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := storedPred }
          have hstored_pred_respects : PredRespectsTagMeaning tm2 storedPred := by
            intro k arg_name pred_body var_env hpred
            by_cases hwrite : result1.qualType.poison = true ∨ ctx.pc = true
            · simp [storedPred, hwrite] at hpred
            · have hpred_res2 :
                  result2.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                simpa [storedPred, hwrite] using hpred
              have hqd2 :
                  qtypGuardDesc? result2.qualType =
                    some (k, { argName := arg_name, body := pred_body, capEnv := var_env }) := by
                simp [qtypGuardDesc?, hpred_res2]
              exact IsCanonicalExtension.respectsResult hcanon2
                (QTypInQTyp.self result2.qualType) hqd2
          have hstored_qtyp : QTypRespectsTagMeaning tm2 storedQt := by
            unfold storedQt
            exact
              QTypRespectsTagMeaning_int_of_predRespects tm2
                (joinPoison ctx.pc
                  (joinPoison result1.qualType.poison result2.qualType.poison))
                storedPred hstored_pred_respects
          have hEnvTm_res2 : EnvRespectsTagMeaning tm2 ctx.varEnv result2.memEnv' := by
            simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
              IsCanonicalExtension.wfCtx hcanon2
          have hEnvTm_res : EnvRespectsTagMeaning tm2 ctx.varEnv res.memEnv' := by
            rw [hmem_res]
            cases hls : Std.ExtTreeSet.toList ls with
            | nil =>
                simp
                exact
                  EnvRespectsTagMeaning_updateLocsetWeak
                    tm2 ctx.varEnv result2.memEnv' ls
                    (joinPoison ctx.pc
                      (joinPoison result1.qualType.poison result2.qualType.poison))
                    storedPred hEnvTm_res2 hstored_pred_respects
            | cons x xs =>
                cases xs with
                | nil =>
                    simp
                    exact
                      EnvRespectsTagMeaning_updateMemEnv
                        tm2 ctx.varEnv result2.memEnv' x storedQt (by simp [storedQt])
                        hEnvTm_res2 hstored_qtyp
                | cons y ys =>
                    simp
                    exact
                      EnvRespectsTagMeaning_updateLocsetWeak
                        tm2 ctx.varEnv result2.memEnv' ls
                        (joinPoison ctx.pc
                          (joinPoison result1.qualType.poison result2.qualType.poison))
                        storedPred hEnvTm_res2 hstored_pred_respects
          have hresTm : QTypRespectsTagMeaning tm2 res.qualType := by
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hetyp_res, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hguard : qtypGuardDesc? res.qualType = none := by
              simp [qtypGuardDesc?, hpred_res]
            intro qt' k d hinq hqd
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm2 res.qualType
              hnotfun hguard hinq hqd
          refine ⟨tm2, ?_, hP2⟩
          exact ⟨hcanon_trans.1, by simpa [hnextTag] using hcanon_trans.2.1,
            wfTagMeaningCtx_ctxAfter tm2 ctx res hEnvTm_res, hresTm⟩
      | ite e1 e2 e3 =>
          simp at htc
          have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
          cases hstruct with
          | inl h1 =>
              rcases h1 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  hmemEnv, _htagEnv, _hnextLoc, hnextTag, _hregime, _hdecl, _hpoison, hetyp_res⟩
              have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
              let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                      nextTag := res1.nextTag', nextBind := res1.nextBind',
                                                      declaredExternRefs := res1.declared' }
              have htc2' : typecheck ctxTrue e2 (fuel' - 1) = .ok res2 := by
                simpa [typecheck, ctxTrue] using htc2
              have hwf_true : wfTagMeaningCtx tm ctxTrue := by
                simpa [wfTagMeaningCtx, ctxTrue] using h_wf
              have hb_true : TagMeaningBounded tm ctxTrue.nextTag := h_bounded.mono hb1
              rcases IH (fuel' - 1) (by omega) tm ctxTrue e2 res2 hwf_true hb_true hP
                  (hL.of_log_eq
                    (typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3)).left.right
                  htc2' with
                ⟨tm2, hcanon2, hP2⟩
              have hresTm : QTypRespectsTagMeaning tm2 res.qualType :=
                QTypRespectsTagMeaning_of_etyp_noPred tm2 res2.qualType res.qualType
                  (IsCanonicalExtension.respectsResult hcanon2) hetyp_res
                  (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
              have hwfFinal : wfTagMeaningCtx tm2 (ctxAfter ctx res) := by
                simpa [wfTagMeaningCtx, ctxAfter, ctxTrue, hmemEnv] using
                  IsCanonicalExtension.wfCtx hcanon2
              refine ⟨tm2, ?_, hP2⟩
              exact ⟨IsCanonicalExtension.extends_tm hcanon2,
                (IsCanonicalExtension.bounded hcanon2).mono
                  (by rw [hnextTag]; exact Nat.le_max_left _ _),
                hwfFinal, hresTm⟩
          | inr h_rest =>
            cases h_rest with
            | inl h2 =>
                rcases h2 with
                  ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                    hmemEnv, _htagEnv, _hnextLoc, hnextTag, _hregime, _hdecl, _hpoison,
                    hetyp_res⟩
                have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                  typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
                let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ({ value := true, deps := deps } : TagVal),
                                                        nextTag := res1.nextTag', nextBind := res1.nextBind',
                                                        declaredExternRefs := res1.declared' }
                let ctxFalse : TypeContext :=
                  { ctx with tagEnv := ctx.tagEnv.insert k ({ value := false, deps := deps } : TagVal),
                             nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind',
                             declaredExternRefs := res2.declared' }
                have htc2' : typecheck ctxTrue e2 (fuel' - 1) = .ok res2 := by
                  simpa [typecheck, ctxTrue] using htc2
                have hnextTag2 : ctx.nextTag ≤ res2.nextTag' :=
                  Nat.le_trans hb1 (typecheck_nextTag_mono ctxTrue e2 (fuel' - 1) res2 htc2')
                have htc3' : typecheck ctxFalse e3 (fuel' - 1) = .ok res3 := by
                  simpa [typecheck, ctxFalse] using htc3
                have hwf_false : wfTagMeaningCtx tm ctxFalse := by
                  simpa [wfTagMeaningCtx, ctxFalse] using h_wf
                have hb_false : TagMeaningBounded tm ctxFalse.nextTag := by
                  simpa [ctxFalse] using h_bounded.mono hnextTag2
                rcases IH (fuel' - 1) (by omega) tm ctxFalse e3 res3 hwf_false hb_false hP
                    (hL.of_log_eq
                      (typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3)).right
                    htc3' with
                  ⟨tm3, hcanon3, hP3⟩
                have hresTm : QTypRespectsTagMeaning tm3 res.qualType :=
                  QTypRespectsTagMeaning_of_etyp_noPred tm3 res3.qualType res.qualType
                    (IsCanonicalExtension.respectsResult hcanon3) hetyp_res
                    (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
                have hwfFinal : wfTagMeaningCtx tm3 (ctxAfter ctx res) := by
                  simpa [wfTagMeaningCtx, ctxAfter, ctxFalse, hmemEnv] using
                    IsCanonicalExtension.wfCtx hcanon3
                refine ⟨tm3, ?_, hP3⟩
                exact ⟨IsCanonicalExtension.extends_tm hcanon3,
                  (IsCanonicalExtension.bounded hcanon3).mono
                    (by rw [hnextTag]; exact Nat.le_max_right _ _),
                  hwfFinal, hresTm⟩
            | inr hstd =>
                obtain
                  ⟨hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3_raw,
                    hmemEnv, _htagEnv, _hnextLoc, hnextTag, _hregime, _hdecl, _hpoison,
                    hetyp_res, hpred_res⟩ := hstd
                let ctx1 : TypeContext :=
                  { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                             nextLoc := res1.nextLoc', nextTag := res1.nextTag', nextBind := res1.nextBind', regime := res1.regime',
                             declaredExternRefs := res1.declared' }
                let pc' := joinPoison ctx.pc res1.qualType.poison
                let ctx'' := { ctx1 with pc := pc' }
                have htc1' : typecheck ctx e1 (fuel' - 1) = .ok res1 := by
                  simpa [typecheck] using htc1
                have hLstd := hL.of_log_eq
                  (typecheckIf_tagLog_std htc hstdCase htc1 htc2 htc3_raw)
                rcases IH (fuel' - 1) (by omega) tm ctx e1 res1 h_wf h_bounded hP
                    hLstd.left.left htc1' with
                  ⟨tm1, hcanon1, hP1⟩
                have hwf_mid : wfTagMeaningCtx tm1 ctx'' := by
                  simp only [wfTagMeaningCtx, ctx'', ctx1]
                  simpa [wfTagMeaningCtx, ctxAfter] using
                    IsCanonicalExtension.wfCtx hcanon1
                have hb_mid : TagMeaningBounded tm1 ctx''.nextTag := by
                  simpa [ctx'', ctx1] using IsCanonicalExtension.bounded hcanon1
                have htc2' : typecheck ctx'' e2 (fuel' - 1) = .ok res2 := by
                  simpa [typecheck, ctx'', ctx1, pc'] using htc2
                rcases IH (fuel' - 1) (by omega) tm1 ctx'' e2 res2 hwf_mid hb_mid
                    hP1 hLstd.left.right htc2' with
                  ⟨tm2, hcanon2, hP2⟩
                let ctxForE3 :=
                  { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind', declaredExternRefs := res2.declared' }
                have htc3' : typecheck ctxForE3 e3 (fuel' - 1) = .ok res3 := by
                  simpa [typecheck, ctxForE3, ctx'', ctx1, pc'] using htc3_raw
                have hwf_mid3 : wfTagMeaningCtx tm2 ctxForE3 := by
                  have hwf_ctx''_tm2 : wfTagMeaningCtx tm2 ctx'' :=
                    wfTagMeaningCtx_mono (IsCanonicalExtension.extends_tm hcanon2) hwf_mid
                  simpa [wfTagMeaningCtx, ctxForE3, ctx'', ctx1] using hwf_ctx''_tm2
                have hb_mid3 : TagMeaningBounded tm2 ctxForE3.nextTag := by
                  simpa [ctxForE3] using IsCanonicalExtension.bounded hcanon2
                rcases IH (fuel' - 1) (by omega) tm2 ctxForE3 e3 res3 hwf_mid3 hb_mid3
                    hP2 hLstd.right htc3' with
                  ⟨tm3, hcanon3, hP3⟩
                have hcanon12 := IsCanonicalExtension.trans hcanon1 hcanon2
                have hext_tm_tm3 : tm ⊑ tm3 :=
                  ExtTreeMap.IsSubmap.trans hcanon12.1
                    (IsCanonicalExtension.extends_tm hcanon3)
                have hEnv2_tm3 : EnvRespectsTagMeaning tm3 ctx.varEnv res2.memEnv' := by
                  have hEnv2_tm2 : EnvRespectsTagMeaning tm2 ctx.varEnv res2.memEnv' := by
                    simpa [wfTagMeaningCtx, ctxAfter, ctx'', ctx1] using
                      IsCanonicalExtension.wfCtx hcanon2
                  exact EnvRespectsTagMeaning_mono
                    (IsCanonicalExtension.extends_tm hcanon3) hEnv2_tm2
                have hTm_final : wfTagMeaningCtx tm3 (ctxAfter ctx res) := by
                  simp only [wfTagMeaningCtx, ctxAfter]
                  rw [hmemEnv]
                  exact EnvRespectsTagMeaning_joinMemEnvsStrong' tm3 ctx.varEnv
                    res2.memEnv' res3.memEnv' hEnv2_tm3
                have hresTm : QTypRespectsTagMeaning tm3 res.qualType := by
                  cases hq2 : res2.qualType with
                  | mk e2' p2 pred2 =>
                  cases hq3 : res3.qualType with
                  | mk e3' p3 pred3 =>
                    have hjoin_qt : QTypRespectsTagMeaning tm3
                        ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3,
                          joinPredicates pred2 pred3⟩ :=
                      QTypRespectsTagMeaning_joinStep tm3 e2' e3' p2 p3 pred2 pred3
                        (QTypRespectsTagMeaning_mono
                          (IsCanonicalExtension.extends_tm hcanon3)
                          (hq2 ▸ IsCanonicalExtension.respectsResult hcanon2))
                        (hq3 ▸ IsCanonicalExtension.respectsResult hcanon3)
                    simp only [hq2, hq3] at hetyp_res
                    intro q' k' d' hinq hgd
                    exact QTypRespectsTagMeaning_of_etyp_noPred tm3
                      ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3,
                        joinPredicates pred2 pred3⟩
                      res.qualType hjoin_qt hetyp_res hpred_res hinq hgd
                refine ⟨tm3, ?_, hP3⟩
                exact ⟨hext_tm_tm3,
                  (IsCanonicalExtension.bounded hcanon3).mono
                    (by rw [hnextTag]; exact Nat.le_max_right _ _),
                  hTm_final, hresTm⟩
      | app e1 e2 =>
          exact False.elim (hnotApp e1 e2 rfl)

/-- For any successful typecheck and any table `Q` that contains the input
    table and records every allocation of the run, there is a canonical
    extension `tm'` of the input table, and it is part of `Q`.

    Non-allocating leaves use `tm' = tm`.  Composite cases thread `tm'`
    through the sub-runs, each of whose allocations are allocations of the
    whole run.  At extern allocation steps the batch table adds only the
    allocations the batch logs, so it stays inside `Q`. -/
private theorem typecheck_canonical_sub
    (Q : TagMeaning)
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (h_laws : tm ⊑ Q) (hL : LogIn res.tagLog' Q)
    (htc : typecheck ctx e fuel = .ok res) :
    ∃ tm', IsCanonicalExtension tm ctx e res tm' ∧ tm' ⊑ Q := by
  revert tm ctx e res
  induction fuel using Nat.strong_induction_on with
  | h fuel IH =>
  intro tm ctx e res h_wf h_bounded h_laws hL htc
  have nonAppCase
      (hnotApp : ∀ e1 e2, e ≠ Expr.app e1 e2)
      (hnotExternVal : ∀ id typ poison pred, e ≠ Expr.externVal id typ poison pred) :
      ∃ tm', IsCanonicalExtension tm ctx e res tm' ∧ tm' ⊑ Q := by
    exact
      typecheck_extends_tagMeaning_nonApp_byIH
        (Q := Q)
        (tm := tm) (ctx := ctx) (e := e) (fuel := fuel) (res := res)
        h_wf h_bounded htc h_laws hL hnotApp hnotExternVal
        (fun m hm tm_i ctx_i e_i res_i hwf_i hb_i h_laws_i hL_i htc_i =>
          IH m hm tm_i ctx_i e_i res_i hwf_i hb_i h_laws_i hL_i htc_i)
  cases e with
  | num n =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | bool b =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | unit =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | str s =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | var x =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | op e1 op e2 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | newRef e1 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | assign e1 e2 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | deref e1 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | seq e1 e2 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | vlet x e1 e2 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | fn x paramType body returnType =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | pfn x paramType body returnType =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | app e1 e2 =>
      unfold typecheck typecheckExpr at htc
      cases fuel with
      | zero => simp at htc
      | succ fuel' =>
          cases fuel' with
          | zero =>
              simp [typecheckApp] at htc
          | succ fuel'' =>
              have htcApp : typecheckApp ctx e1 e2 (Nat.succ fuel'') = .ok res := htc
              obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1,
                h_arrow_or_parrow⟩ :=
                typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htcApp
              have htc2' : typecheck ctx e2 fuel'' = .ok result2 := by
                simpa [typecheck] using htc2
              have hLapp : ∃ joined : TypeResult,
                  res.tagLog' = result2.tagLog' ++ (result1.tagLog' ++ joined.tagLog') := by
                rcases h_arrow_or_parrow with
                  ⟨_, _, _, _, _, _, _, _, joined, _, _, _, _, _, _, _, _, hres⟩ |
                  ⟨_, _, _, _, _, _, _, _, joined, _, _, _, _, _, _, _, hres⟩
                · exact ⟨joined, by rw [hres]⟩
                · exact ⟨joined, by rw [hres]⟩
              obtain ⟨_joined, hLapp⟩ := hLapp
              have hL21 := hL.of_log_eq hLapp
              rcases IH fuel'' (by omega) tm ctx e2 result2
                  h_wf h_bounded h_laws hL21.left htc2' with
                ⟨tm2, hcanon2, h_laws2⟩
              have htc1' : typecheck (ctxAfter ctx result2) e1 fuel'' = .ok result1 := by
                simpa [typecheck, ctxAfter] using htc1
              rcases IH fuel'' (by omega) tm2 (ctxAfter ctx result2) e1 result1
                  hcanon2.2.2.1 hcanon2.2.1 h_laws2 hL21.right.left htc1' with
                ⟨tm1, hcanon1, h_laws1⟩
              have hext_tm_tm2 : tm ⊑ tm2 := hcanon2.1
              have hext_tm2_tm1 : tm2 ⊑ tm1 := hcanon1.1
              have hext_tm_tm1 : tm ⊑ tm1 :=
                ExtTreeMap.IsSubmap.trans hext_tm_tm2 hext_tm2_tm1
              have hctxTm1 : wfTagMeaningCtx tm1 (ctxAfter ctx result1) :=
                hcanon1.2.2.1
              have hresTm1 : QTypRespectsTagMeaning tm1 result1.qualType :=
                hcanon1.2.2.2
              have hargTm2 : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                rw [← hqt2]
                exact hcanon2.2.2.2
              have hargTm1 : QTypRespectsTagMeaning tm1 ⟨etyp2, p2, pred2⟩ :=
                QTypRespectsTagMeaning_mono hext_tm2_tm1 hargTm2
              cases h_arrow_or_parrow with
              | inl h_arrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, hetyp1, _hp1,
                    _hnpure, _hnempty, _hsub, hthread, heq_results, h_join, rfl⟩ := h_arrow
                  rcases applyFnClosuresThreaded_ok_tagMeaningSub_byIH
                      (Q := Q) (tm := tm1)
                      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (allTcls := tcls) (todo := tcls)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result1 := result1) (cursor := (result1.nextTag', result1.nextLoc'))
                      (bn := result1.nextBind') (fuel := fuel'')
                      (IH := fun m hm tm_i ctx_i e_i res_i htc_i hwf_i hb_i h_laws_i hL_i =>
                        IH m (by omega) tm_i ctx_i e_i res_i
                          hwf_i hb_i h_laws_i hL_i htc_i)
                      (first := first) (rest := rest)
                      hctxTm1 hresTm1 hcanon1.2.1 h_laws1 (hL.right.right.of_join h_join)
                      hetyp1 (fun tcl htcl => htcl) hargTm1
                      (by simpa [heq_results] using hthread) with
                    ⟨tmFinal, last, hextClosures, hlast_mem, hboundedLast,
                      hwfResults, hqResults, h_lawsFinal⟩
                  have hlast_le_res : last.nextTag' ≤ res.nextTag' := by
                    have hmax := joinTypeResults_nextTag_eq_max ctx first rest res h_join
                    have hlast_mem_tags :
                        last.nextTag' ∈ first.nextTag' :: rest.map TypeResult.nextTag' := by
                      cases hlast_mem with
                      | head =>
                          simp
                      | tail _ hlast =>
                          exact List.mem_cons_of_mem _
                            (List.mem_map.mpr ⟨last, hlast, rfl⟩)
                    rw [hmax]
                    exact List.le_max_of_mem hlast_mem_tags
                  have hboundedRes : TagMeaningBounded tmFinal res.nextTag' :=
                    hboundedLast.mono hlast_le_res
                  have hwfJoin : wfTagMeaningCtx tmFinal (ctxAfter ctx res) :=
                    join_transport_wfTagMeaningCtx_byFirst tmFinal ctx first rest res h_join
                      (hwfResults first (by simp))
                  have hqFirst : QTypRespectsTagMeaning tmFinal first.qualType :=
                    hqResults first (by simp)
                  have hqRest : ∀ r ∈ rest, QTypRespectsTagMeaning tmFinal r.qualType := by
                    intro r hr
                    exact hqResults r (by simp [hr])
                  exact ⟨tmFinal,
                    ⟨ExtTreeMap.IsSubmap.trans hext_tm_tm1 hextClosures,
                      hboundedRes, hwfJoin,
                      joinTypeResults_QTypRespectsTagMeaning_byMembers tmFinal ctx first rest
                        res h_join hqFirst hqRest⟩,
                    h_lawsFinal⟩
              | inr h_parrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, hetyp1, _hp1,
                    _hnempty, _hsub, hthread, heq_results, h_join, rfl⟩ := h_parrow
                  rcases applyPFnClosuresThreaded_ok_tagMeaningSub_byIH
                      (Q := Q) (tm := tm1)
                      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (allTcls := tcls) (todo := tcls)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result1 := result1) (cursor := (result1.nextTag', result1.nextLoc'))
                      (bn := result1.nextBind') (fuel := fuel'')
                      (IH := fun m hm tm_i ctx_i e_i res_i htc_i hwf_i hb_i h_laws_i hL_i =>
                        IH m (by omega) tm_i ctx_i e_i res_i
                          hwf_i hb_i h_laws_i hL_i htc_i)
                      (first := first) (rest := rest)
                      hctxTm1 hresTm1 hcanon1.2.1 h_laws1 (hL.right.right.of_join h_join)
                      hetyp1 (fun tcl htcl => htcl) hargTm1
                      (by simpa [heq_results] using hthread) with
                    ⟨tmFinal, last, hextClosures, hlast_mem, hboundedLast,
                      hwfResults, hqResults, h_lawsFinal⟩
                  have hlast_le_res : last.nextTag' ≤ res.nextTag' := by
                    have hmax := joinTypeResults_nextTag_eq_max ctx first rest res h_join
                    have hlast_mem_tags :
                        last.nextTag' ∈ first.nextTag' :: rest.map TypeResult.nextTag' := by
                      cases hlast_mem with
                      | head =>
                          simp
                      | tail _ hlast =>
                          exact List.mem_cons_of_mem _
                            (List.mem_map.mpr ⟨last, hlast, rfl⟩)
                    rw [hmax]
                    exact List.le_max_of_mem hlast_mem_tags
                  have hboundedRes : TagMeaningBounded tmFinal res.nextTag' :=
                    hboundedLast.mono hlast_le_res
                  have hwfJoin : wfTagMeaningCtx tmFinal (ctxAfter ctx res) :=
                    join_transport_wfTagMeaningCtx_byFirst tmFinal ctx first rest res h_join
                      (hwfResults first (by simp))
                  have hqFirst : QTypRespectsTagMeaning tmFinal first.qualType :=
                    hqResults first (by simp)
                  have hqRest : ∀ r ∈ rest, QTypRespectsTagMeaning tmFinal r.qualType := by
                    intro r hr
                    exact hqResults r (by simp [hr])
                  exact ⟨tmFinal,
                    ⟨ExtTreeMap.IsSubmap.trans hext_tm_tm1 hextClosures,
                      hboundedRes, hwfJoin,
                      joinTypeResults_QTypRespectsTagMeaning_byMembers tmFinal ctx first rest
                        res h_join hqFirst hqRest⟩,
                    h_lawsFinal⟩
  | ite e1 e2 e3 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | unaryop op e1 =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | externVal id typ poison pred =>
      unfold typecheck typecheckExpr at htc
      cases fuel with
      | zero => simp at htc
      | succ fuel' =>
          rcases typecheckExternVal_canonical_batch tm ctx id typ poison pred fuel' res
              h_wf h_bounded htc with
            ⟨tm', _tagMapping, _nextTag', _hbatch, hwithin, hcanon⟩
          exact ⟨tm', hcanon, hwithin.submap h_laws hL⟩
  | externRef _ _ _ _ _ =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | externFn id arg argTyp _ _ retSpec effects =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)
  | externPfn id arg argTyp _ _ retSpec =>
      exact nonAppCase (by intro e1 e2 h; cases h)
        (by intro id typ poison pred h; cases h)

/-- For any successful typecheck there is a canonical extension `tm'` of the
    input table that adds only allocations of the run; `tm'` does not depend on
    a relation, and every relation with a frame for the run (a lawful table,
    under that relation's view, containing the input table and every
    allocation of the run) satisfies the laws on `tm'` under the same view. -/
theorem typecheck_preserves_predSatLaws_uniform
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (htc : typecheck ctx e fuel = .ok res) :
    ∃ tm', IsCanonicalExtension tm ctx e res tm' ∧ WithinLog tm res.tagLog' tm' ∧
      ∀ (predSat : PredSat) (β : BindVals),
        TagFrame predSat β tm res.tagLog' → PredSatLaws predSat tm' β := by
  obtain ⟨hsub, hlog, hwithinQ⟩ := typecheck_programTable tm ctx e fuel res h_bounded htc
  obtain ⟨tm', hcanon, hsubQ⟩ :=
    typecheck_canonical_sub (programTable tm res.tagLog') tm ctx e fuel res
      h_wf h_bounded hsub hlog htc
  have hwithin : WithinLog tm res.tagLog' tm' := hwithinQ.of_submap hsubQ
  exact ⟨tm', hcanon, hwithin, fun _ _ hframe => hframe.laws_of_within hwithin⟩

/-- For any successful typecheck in a frame (a lawful table, under the view
    `β`, containing the input table and every allocation of the run), there is
    a canonical extension `tm'` of the input table; it adds only allocations
    of the run, and `PredSatLaws predSat tm' β` holds. -/
theorem typecheck_preserves_predSatLaws
    (predSat : PredSat) (β : BindVals)
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (h_wf : wfTagMeaningCtx tm ctx)
    (h_bounded : TagMeaningBounded tm ctx.nextTag)
    (hframe : TagFrame predSat β tm res.tagLog')
    (htc : typecheck ctx e fuel = .ok res) :
    ∃ tm', IsCanonicalExtension tm ctx e res tm' ∧ PredSatLaws predSat tm' β ∧
      WithinLog tm res.tagLog' tm' := by
  obtain ⟨tm', hcanon, hwithin, hlaws⟩ :=
    typecheck_preserves_predSatLaws_uniform tm ctx e fuel res h_wf h_bounded htc
  exact ⟨tm', hcanon, hlaws predSat β hframe, hwithin⟩

lemma applyPFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyPFnTClosure (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        bindEnv := BindEnv.bindParam tenv x result2.nextBind'
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextBind := result2.nextBind' + 1
        nextLoc := result2.nextLoc'
        regime := result2.regime'
        externRefAllowed := false
        declaredExternRefs := result2.declared' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isErasureOf st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
        declared' := result2.declared' } := by
  unfold applyPFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        bindEnv := BindEnv.bindParam tenv x result2.nextBind'
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextBind := result2.nextBind' + 1
        nextLoc := result2.nextLoc'
        regime := result2.regime'
        externRefAllowed := false
        declaredExternRefs := result2.declared' } (PExpr.toExpr pbody) fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isErasureOf st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isErasureOf st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isErasureOf st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
                        declared' := result2.declared' } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) }
                      declared' := result2.declared' } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

private lemma monotoneStep_lookup_back {R R' : Regime}
    (h_mono : Regime.monotoneStep R R') :
    ∀ k b, R'.lookup? k = some b → R.lookup? k = some b := by
  intro k b hkR'
  have hRdef : R.lookup? k ≠ none := by
    exact h_mono.2 k (by simp [hkR'])
  cases hkR : R.lookup? k with
  | none =>
      exact False.elim (hRdef hkR)
  | some b0 =>
      have hkeep := h_mono.1 k b0 hkR
      cases hkeep with
      | inl hkR'' =>
          have : b0 = b := by
            exact Option.some.inj (hkR''.symm.trans hkR')
          subst this
          rfl
      | inr hkR'' =>
          simp [hkR''] at hkR'

private lemma joinTypeResults_lookup_head_guardTag_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp) (k : Tag)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first)
  (htag_res : qtypGuardTag qt = some k) :
  qtypGuardTag qt_first = some k := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_guardTag :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_acc : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.1.lookup l = some qt_acc →
        acc'.2.1.lookup l = some qt →
        qtypGuardTag qt = some k →
        qtypGuardTag qt_acc = some k := by
    intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out htag_out
    induction rs' generalizing acc qt_acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        have hqeq : qt_acc = qt := by
          have hqeq_opt : some qt_acc = some qt := by
            calc
              some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
              _ = some qt := hlookup_out
          exact Option.some.inj hqeq_opt
        subst hqeq
        exact htag_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            obtain ⟨qt_mid, hlookup_mid⟩ :=
              joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
            have htag_mid : qtypGuardTag qt_mid = some k :=
              ih (acc := acc1) (qt_acc := qt_mid) hfold_tail hlookup_mid
            exact
              joinMemEnvsStrong_lookup_guardTag_left
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid) (qt1 := qt_acc) (k := k)
                hlookup_mid hlookup_acc htag_mid
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_first' : first.memEnv'.lookup l = some qt_first := by
                simpa [ctxAfter] using hlookup_first
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              exact
                h_fold_guardTag
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a qt_first
                  hfold hlookup_first' hlookup_res' htag_res

private lemma joinTypeResults_lookup_head_regime_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (k : Tag) (b : Bool)
  (hlookup_res : (ctxAfter ctx res).regime.lookup? k = some b) :
  (ctxAfter ctx first).regime.lookup? k = some b := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_regime :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.2.2.2.1.lookup? k = some b →
        acc.2.2.2.2.2.1.lookup? k = some b := by
    intro rs' acc acc' hfold hlookup_out
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hlookup_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hlookup_mid : acc1.2.2.2.2.2.1.lookup? k = some b :=
              ih (acc := acc1) hfold_tail
            exact
              joinRegimes_lookup_some_left
                (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_mid
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              exact
                h_fold_regime
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a
                  hfold (by simpa [ctxAfter] using hlookup_res)

private lemma joinTypeResults_lookup_head_poison_imp
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first) :
  qt.poison = false → qt_first.poison = false := by
  intro hpoison_res
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_poison :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_acc : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.1.lookup l = some qt_acc →
        acc'.2.1.lookup l = some qt →
        qt.poison = false →
        qt_acc.poison = false := by
    intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out hclean_out
    induction rs' generalizing acc qt_acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        have hqeq : qt_acc = qt := by
          have hqeq_opt : some qt_acc = some qt := by
            calc
              some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
              _ = some qt := hlookup_out
          exact Option.some.inj hqeq_opt
        subst hqeq
        exact hclean_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            obtain ⟨qt_mid, hlookup_mid⟩ :=
              joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
            have hclean_mid : qt_mid.poison = false :=
              ih (acc := acc1) (qt_acc := qt_mid) hfold_tail hlookup_mid
            have hacc_not_none : acc.2.1.lookup l ≠ none := by
              intro hnone
              rw [hlookup_acc] at hnone
              cases hnone
            have hleft_clean :=
              joinMemEnvsStrong_lookup_clean_left
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid)
                hlookup_mid hclean_mid hacc_not_none
            rcases hleft_clean with ⟨qt_acc', hlookup_acc', _hetyp, hpoison_acc'⟩
            have hqeq : qt_acc' = qt_acc := by
              have hqeq_opt : some qt_acc' = some qt_acc := by
                calc
                  some qt_acc' = acc.2.1.lookup l := hlookup_acc'.symm
                  _ = some qt_acc := hlookup_acc
              exact Option.some.inj hqeq_opt
            subst hqeq
            exact hpoison_acc'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_first' : first.memEnv'.lookup l = some qt_first := by
                simpa [ctxAfter] using hlookup_first
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              exact
                h_fold_poison
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a qt_first
                  hfold hlookup_first' hlookup_res' hpoison_res

lemma joinTypeResults_lookup_member_regime_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (k : Tag) (b : Bool)
  (hlookup_res : (ctxAfter ctx res).regime.lookup? k = some b) :
  (ctxAfter ctx src).regime.lookup? k = some b := by
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    simpa using
      (joinTypeResults_lookup_head_regime_compat
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join k b hlookup_res)
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_regime_members :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc'.2.2.2.2.2.1.lookup? k = some b →
          (acc.2.2.2.2.2.1.lookup? k = some b) ∧
            (∀ r ∈ rs', r.regime'.lookup? k = some b) := by
      intro rs' acc acc' hfold hlookup_out
      induction rs' generalizing acc acc' with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          exact ⟨hlookup_out, by intro r hr; cases hr⟩
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              have htail_pack :=
                ih (acc := acc1) (acc' := acc') hfold_tail hlookup_out
              have hlookup_acc1 : acc1.2.2.2.2.2.1.lookup? k = some b := htail_pack.1
              have hlookup_acc : acc.2.2.2.2.2.1.lookup? k = some b :=
                joinRegimes_lookup_some_left
                  (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_acc1
              have hlookup_x : x.regime'.lookup? k = some b :=
                joinRegimes_lookup_some_right
                  (R1 := acc.2.2.2.2.2.1) (R2 := x.regime') (k := k) (b := b) hlookup_acc1
              refine ⟨hlookup_acc, ?_⟩
              intro r hr
              rcases (List.mem_cons.mp hr) with hrx | hrxs
              · subst r
                exact hlookup_x
              · exact htail_pack.2 r hrxs
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.2.2.2.2.1.lookup? k = some b := by
                  simpa [ctxAfter] using hlookup_res
                have hpack :=
                  h_fold_regime_members
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    a
                    hfold hlookup_res'
                have hsrc_lookup : src.regime'.lookup? k = some b := hpack.2 src hsrc_rest
                simpa [ctxAfter] using hsrc_lookup

lemma joinTypeResults_lookup_member_guardTag_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp) (k : Tag)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src)
  (htag_res : qtypGuardTag qt = some k) :
  qtypGuardTag qt_src = some k := by
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    simpa using
      (joinTypeResults_lookup_head_guardTag_compat
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join l qt qt_src k hlookup_res hlookup_src htag_res)
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_guardTag :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (qt_acc : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc.2.1.lookup l = some qt_acc →
          acc'.2.1.lookup l = some qt →
          qtypGuardTag qt = some k →
          qtypGuardTag qt_acc = some k := by
      intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out htag_out
      induction rs' generalizing acc acc' qt_acc with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          have hqeq : qt_acc = qt := by
            have hqeq_opt : some qt_acc = some qt := by
              calc
                some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
                _ = some qt := hlookup_out
            exact Option.some.inj hqeq_opt
          subst hqeq
          exact htag_out
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              obtain ⟨qt_mid, hlookup_mid⟩ :=
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
              have htag_mid : qtypGuardTag qt_mid = some k :=
                ih (acc := acc1) (acc' := acc') (qt_acc := qt_mid) hfold_tail hlookup_mid hlookup_out
              exact
                joinMemEnvsStrong_lookup_guardTag_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid) (qt1 := qt_acc) (k := k)
                  hlookup_mid hlookup_acc htag_mid
    have h_fold_member_guardTag :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (src' : TypeResult) (qt_src' : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          src' ∈ rs' →
          acc'.2.1.lookup l = some qt →
          qtypGuardTag qt = some k →
          src'.memEnv'.lookup l = some qt_src' →
          qtypGuardTag qt_src' = some k := by
      intro rs' acc acc' src' qt_src' hfold hmem_src' hlookup_out htag_out hlookup_src'
      induction rs' generalizing acc acc' src' qt_src' with
      | nil =>
          cases hmem_src'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
              · subst src'
                have hlookup_acc1_exists :
                    ∃ qt_acc1, acc1.2.1.lookup l = some qt_acc1 := by
                  exact
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_src')
                      hlookup_src'
                rcases hlookup_acc1_exists with ⟨qt_acc1, hlookup_acc1⟩
                have htag_acc1 : qtypGuardTag qt_acc1 = some k :=
                  h_fold_guardTag
                    xs acc1 acc' qt_acc1
                    hfold_tail hlookup_acc1 hlookup_out htag_out
                exact
                  joinMemEnvsStrong_lookup_guardTag_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l)
                    (qt := qt_acc1) (qt2 := qt_src') (k := k)
                    hlookup_acc1 hlookup_src' htag_acc1
              · exact
                  ih (acc := acc1) (acc' := acc') (src' := src') (qt_src' := qt_src')
                    hfold_tail hsrc_tail hlookup_out hlookup_src'
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.1.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup_res
                have hlookup_src' : src.memEnv'.lookup l = some qt_src := by
                  simpa [ctxAfter] using hlookup_src
                exact
                  h_fold_member_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' htag_res hlookup_src'

lemma joinTypeResults_lookup_member_etyp_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qt.etyp = qt_src.etyp := by
  have hres_int : qt.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx res).memEnv) l qt hlookup_res
  have hsrc_int : qt_src.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx src).memEnv) l qt_src hlookup_src
  calc
    qt.etyp = ETyp.int := hres_int
    _ = qt_src.etyp := hsrc_int.symm

lemma joinTypeResults_lookup_member_poison_imp
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qt.poison = false → qt_src.poison = false := by
  intro hclean_out
  rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
  · subst src
    exact
      joinTypeResults_lookup_head_poison_imp
        (ctx := ctx) (first := first) (rest := rest) (res := res)
        _h_join l qt qt_src hlookup_res hlookup_src hclean_out
  · let joinStep :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
      fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
        match result.qualType with
        | ⟨resEtyp, resPoison, resPred⟩ =>
            Except.ok
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 result.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 result.regime',
                max acc.2.2.2.2.2.2.1 result.nextLoc',
                max acc.2.2.2.2.2.2.2 result.nextTag')
    have h_fold_poison :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (qt_acc : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          acc.2.1.lookup l = some qt_acc →
          acc'.2.1.lookup l = some qt →
          qt.poison = false →
          qt_acc.poison = false := by
      intro rs' acc acc' qt_acc hfold hlookup_acc hlookup_out hclean_out'
      induction rs' generalizing acc acc' qt_acc with
      | nil =>
          simp [List.foldlM_nil, pure, Except.pure] at hfold
          subst acc'
          have hqeq : qt_acc = qt := by
            have hqeq_opt : some qt_acc = some qt := by
              calc
                some qt_acc = acc.2.1.lookup l := hlookup_acc.symm
                _ = some qt := hlookup_out
            exact Option.some.inj hqeq_opt
          subst hqeq
          exact hclean_out'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              obtain ⟨qt_mid, hlookup_mid⟩ :=
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc
              have hclean_mid : qt_mid.poison = false :=
                ih (acc := acc1) (acc' := acc') (qt_acc := qt_mid) hfold_tail hlookup_mid hlookup_out
              have hacc_not_none : acc.2.1.lookup l ≠ none := by
                intro hnone
                rw [hlookup_acc] at hnone
                cases hnone
              have hleft_clean :=
                joinMemEnvsStrong_lookup_clean_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_mid)
                  hlookup_mid hclean_mid hacc_not_none
              rcases hleft_clean with ⟨qt_acc', hlookup_acc', _hetyp, hpoison_acc'⟩
              have hqeq : qt_acc' = qt_acc := by
                have hqeq_opt : some qt_acc' = some qt_acc := by
                  calc
                    some qt_acc' = acc.2.1.lookup l := hlookup_acc'.symm
                    _ = some qt_acc := hlookup_acc
                exact Option.some.inj hqeq_opt
              subst hqeq
              exact hpoison_acc'
    have h_fold_member_poison :
        ∀ (rs' : List TypeResult)
          (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
          (src' : TypeResult) (qt_src' : QTyp),
          List.foldlM joinStep acc rs' = .ok acc' →
          src' ∈ rs' →
          acc'.2.1.lookup l = some qt →
          qt.poison = false →
          src'.memEnv'.lookup l = some qt_src' →
          qt_src'.poison = false := by
      intro rs' acc acc' src' qt_src' hfold hmem_src' hlookup_out hclean_out' hlookup_src'
      induction rs' generalizing acc acc' src' qt_src' with
      | nil =>
          cases hmem_src'
      | cons x xs ih =>
          cases hqx : x.qualType with
          | mk resEtyp resPoison resPred =>
              simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
              let acc1 :
                  ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
                (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                  joinMemEnvsStrong acc.2.1 x.memEnv',
                  joinPoison acc.2.2.1 resPoison,
                  joinPredicates acc.2.2.2.1 resPred,
                  joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                  joinRegimes acc.2.2.2.2.2.1 x.regime',
                  max acc.2.2.2.2.2.2.1 x.nextLoc',
                  max acc.2.2.2.2.2.2.2 x.nextTag')
              have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
                simpa [acc1] using hfold
              rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
              · subst src'
                have hlookup_acc1_exists :
                    ∃ qt_acc1, acc1.2.1.lookup l = some qt_acc1 := by
                  exact
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_src')
                      hlookup_src'
                rcases hlookup_acc1_exists with ⟨qt_acc1, hlookup_acc1⟩
                have hclean_acc1 : qt_acc1.poison = false :=
                  h_fold_poison
                    xs acc1 acc' qt_acc1
                    hfold_tail hlookup_acc1 hlookup_out hclean_out'
                have hx_not_none : x.memEnv'.lookup l ≠ none := by
                  intro hnone
                  rw [hlookup_src'] at hnone
                  cases hnone
                have hright_clean :=
                  joinMemEnvsStrong_lookup_clean_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                    hlookup_acc1 hclean_acc1 hx_not_none
                rcases hright_clean with ⟨qt_x, hlookup_x, _hetyp_x, hclean_x⟩
                have hqeq : qt_x = qt_src' := by
                  have hqeq_opt : some qt_x = some qt_src' := by
                    calc
                      some qt_x = x.memEnv'.lookup l := hlookup_x.symm
                      _ = some qt_src' := hlookup_src'
                  exact Option.some.inj hqeq_opt
                subst hqeq
                exact hclean_x
              · exact
                  ih (acc := acc1) (acc' := acc') (src' := src') (qt_src' := qt_src')
                    hfold_tail hsrc_tail hlookup_out hlookup_src'
    cases hqt : first.qualType with
    | mk etyp poison pred =>
        simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, TypecheckM] at _h_join
        cases hcheck :
            (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                  if beqETypSignature etyp resEtyp = false then
                    Except.error
                      (toString "Closure alternatives produced incompatible result types: " ++
                        toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                  else Except.ok ())
              () rest : Except String Unit) with
        | error err =>
            erw [hcheck] at _h_join
            simp at _h_join
        | ok _ =>
            erw [hcheck] at _h_join
            simp at _h_join
            cases hfold :
                List.foldlM joinStep
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag') rest with
            | error err =>
                erw [hfold] at _h_join
                simp at _h_join
            | ok a =>
                erw [hfold] at _h_join
                simp at _h_join
                subst res
                have hlookup_res' : a.2.1.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup_res
                have hlookup_src' : src.memEnv'.lookup l = some qt_src := by
                  simpa [ctxAfter] using hlookup_src
                exact
                  h_fold_member_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' hclean_out hlookup_src'

lemma applyPFnTClosure_mem_subset
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  ∀ l, r.memEnv'.contains l → result2.memEnv'.contains l := by
  intro l hcontains
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          rcases applyPFnTClosure_regular_inv
              ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuelBody x body env r happly with
            ⟨result3, htcBody, _hsub, hr⟩
          subst hr
          let bodyCtx : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1)
              memEnv := result2.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              bindEnv := BindEnv.bindParam env x result2.nextBind'
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextBind := result2.nextBind' + 1
              nextLoc := result2.nextLoc'
              regime := result2.regime'
              pureCtx := true
              externRefAllowed := false
              declaredExternRefs := result2.declared' }
          have hsub_body :
              ∀ l, result3.memEnv'.contains l → bodyCtx.memEnv.contains l :=
            typecheckExpr_pure_mem_subset_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hsub_body l hcontains
      | extern id x retSpec capturedEnv declaredArgQt captures =>
          have hmem_eq := applyPFnTClosure_extern_memEnv_eq
            ctx st1 st2 p p1 argEtyp argPoison argPred result2 r (fuelBody + 1)
            id x retSpec capturedEnv declaredArgQt happly
          rw [← hmem_eq]; exact hcontains

lemma applyPFnTClosure_preserves_memEnv_lookup
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  ∀ l qt, result2.memEnv'.lookup l = some qt → r.memEnv'.lookup l = some qt := by
  intro l qt hlookup
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          rcases applyPFnTClosure_regular_inv
              ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuelBody x body env r happly with
            ⟨result3, htcBody, _hsub, hr⟩
          subst hr
          let bodyCtx : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1)
              memEnv := result2.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              bindEnv := BindEnv.bindParam env x result2.nextBind'
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextBind := result2.nextBind' + 1
              nextLoc := result2.nextLoc'
              regime := result2.regime'
              pureCtx := true
              externRefAllowed := false
              declaredExternRefs := result2.declared' }
          have hpres_body :
              ∀ l qt, bodyCtx.memEnv.lookup l = some qt → result3.memEnv'.lookup l = some qt :=
            typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hpres_body l qt hlookup
      | extern id x retSpec capturedEnv declaredArgQt captures =>
          have hmem_eq := applyPFnTClosure_extern_memEnv_eq
            ctx st1 st2 p p1 argEtyp argPoison argPred result2 r (fuelBody + 1)
            id x retSpec capturedEnv declaredArgQt happly
          rw [hmem_eq]; exact hlookup

private lemma typecheckExpr_lookup_origin_of_pc_true_split
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr ctx e fuel = .ok res)
  (hwf : wfTypeContext ctx)
  (hbnd : TagBoundedCtx ctx)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp),
    res.memEnv'.lookup l = some qt_out →
    ctx.memEnv.contains l →
    (qt_out.poison = false → ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false) ∧
    (∀ k, qtypGuardTag qt_out = some k → res.regime'.lookup? k = some true →
      qt_out.etyp.isFunctionType = false →
      ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
        qtypGuardTag qt_in = some k ∧
        ctx.regime.lookup? k = some true ∧
        qt_in.etyp.isFunctionType = false) := by
  classical
  revert ctx e res htc hwf hbnd hpc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e res htc hwf hbnd hpc l qt_out hlookup_out hpre
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e with
      | num n =>
          simp [typecheckExpr] at htc
          cases htc
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | bool b =>
          simp [typecheckExpr] at htc
          cases htc
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | unit =>
          simp [typecheckExpr] at htc
          cases htc
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | str s =>
          simp [typecheckExpr] at htc
          cases htc
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | var x =>
          have htcVar : typecheckVar ctx x = .ok res := by
            simpa [typecheckExpr] using htc
          have hmem : res.memEnv' = ctx.memEnv :=
            typecheckVar_preserves_memEnv ctx x res htcVar
          have hreg : res.regime' = ctx.regime :=
            typecheckVar_preserves_regime ctx x res htcVar
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, by simpa [hmem] using hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, by simpa [hmem] using hlookup_out, htag, by simpa [hreg] using hk, hnotfun⟩
      | fn x st1 body st2 =>
          simp only [typecheckExpr] at htc
          have hfn := typecheckFn_ok_eq htc
          subst hfn
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact ⟨qt_out, hlookup_out, hpoison⟩
          · intro k htag hk hnotfun
            exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | pfn x st1 body st2 =>
          unfold typecheckExpr at htc
          unfold typecheckPfn at htc
          simp [bind, Except.bind] at htc
          cases h_topexpr : body.toPExpr with
          | error _ =>
              simp [h_topexpr] at htc
          | ok _ =>
              simp [h_topexpr, pure, Except.pure] at htc
              cases htc
              refine ⟨?_, ?_⟩
              · intro hpoison
                exact ⟨qt_out, hlookup_out, hpoison⟩
              · intro k htag hk hnotfun
                exact ⟨qt_out, hlookup_out, htag, hk, hnotfun⟩
      | op e1 bop e2 =>
          have htcOp : typecheckOp ctx e1 e2 fuel' bop = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckOp_structure ctx e1 e2 bop fuel' res htcOp with
            ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
              h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
            simpa [updateCtxFromResult] using hpc
          have hpre_r1 : result1.memEnv'.contains l :=
            typecheckExpr_mem_contains_preserved ctx e1 (fuel' - 1) result1 (by simpa using htc1) l hpre
          have hwf_ucr : wfTypeContext (updateCtxFromResult ctx result1) :=
            wfTypeContext_of_wfTypeResult ctx result1
              (typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) result1 hwf (by simpa using! htc1))
              hwf (typecheck_nextLoc_mono ctx e1 (fuel' - 1) result1 (by simpa using! htc1))
          have hbnd_ucr : TagBoundedCtx (updateCtxFromResult ctx result1) := by
            simpa [updateCtxFromResult, ctxAfter] using
              typecheckExpr_preserves_TagBoundedCtx ctx e1 (fuel' - 1) result1 (by simpa using htc1) hbnd
          rcases ih (fuel' - 1) hltSub
              (updateCtxFromResult ctx result1) e2 result2
              (by simpa [updateCtxFromResult] using htc2)
              hwf_ucr hbnd_ucr hpc2 l qt_out hlookup2 (by simpa [updateCtxFromResult] using hpre_r1) with
            ⟨hpoison2, hguard2⟩
          refine ⟨?_, ?_⟩
          · intro hpoison
            rcases hpoison2 hpoison with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [updateCtxFromResult] using hlookup_mid) hpre with
              ⟨hpoison1, _hguard1⟩
            exact hpoison1 hpoison_mid
          · intro k htag hk hnotfun
            rcases hguard2 k htag (by simpa [h_regime] using hk) hnotfun with
              ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [updateCtxFromResult] using hlookup_mid) hpre with
              ⟨_hpoison1, hguard1⟩
            exact hguard1 k htag_mid (by simpa [updateCtxFromResult] using hk_mid) hnotfun_mid
      | unaryop uop e1 =>
          have htcUnary : typecheckUnaryOp ctx uop e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckUnaryOp_structure ctx uop e1 fuel' res htcUnary with
            ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, h_regime,
              _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hwf hbnd hpc l qt_out hlookup1 hpre with
            ⟨hpoison1, hguard1⟩
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact hpoison1 hpoison
          · intro k htag hk hnotfun
            exact hguard1 k htag (by simpa [h_regime] using hk) hnotfun
      | deref e1 =>
          have htcDeref : typecheckDeref ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckDeref_structure ctx e1 fuel' res htcDeref with
            ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, h_regime⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hwf hbnd hpc l qt_out hlookup1 hpre with
            ⟨hpoison1, hguard1⟩
          refine ⟨?_, ?_⟩
          · intro hpoison
            exact hpoison1 hpoison
          · intro k htag hk hnotfun
            exact hguard1 k htag (by simpa [h_regime] using hk) hnotfun
      | seq e1 e2 =>
          have htcSeq : typecheckSeq ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
            ⟨result1, ctx', res, htc1, hctx', htc2, rfl⟩
          have hpc2 : ctx'.pc = true := by
            simpa [hctx', updateCtxFromResult] using hpc
          have hpre' : ctx'.memEnv.contains l := by
            simpa [hctx', updateCtxFromResult] using
              typecheckExpr_mem_contains_preserved ctx e1 (fuel' - 1) result1 (by simpa using htc1) l hpre
          have hwf_ctx' : wfTypeContext ctx' := by
            rw [hctx']
            exact wfTypeContext_of_wfTypeResult ctx result1
              (typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) result1 hwf (by simpa using! htc1))
              hwf (typecheck_nextLoc_mono ctx e1 (fuel' - 1) result1 (by simpa using! htc1))
          have hbnd_ctx' : TagBoundedCtx ctx' := by
            rw [hctx']
            simpa [updateCtxFromResult, ctxAfter] using
              typecheckExpr_preserves_TagBoundedCtx ctx e1 (fuel' - 1) result1 (by simpa using htc1) hbnd
          rcases ih (fuel' - 1) hltSub ctx' e2 res
              (by simpa [hctx'] using htc2) hwf_ctx' hbnd_ctx' hpc2 l qt_out hlookup_out hpre' with
            ⟨hpoison2, hguard2⟩
          refine ⟨?_, ?_⟩
          · intro hpoison
            rcases hpoison2 hpoison with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [hctx', updateCtxFromResult] using hlookup_mid) hpre with
              ⟨hpoison1, _hguard1⟩
            exact hpoison1 hpoison_mid
          · intro k htag hk hnotfun
            rcases hguard2 k htag hk hnotfun with
              ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [hctx', updateCtxFromResult] using hlookup_mid) hpre with
              ⟨_hpoison1, hguard1⟩
            exact hguard1 k htag_mid (by simpa [hctx', updateCtxFromResult] using hk_mid) hnotfun_mid
      | vlet x e1 e2 =>
          have htcVlet : typecheckVlet ctx x e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
            ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc,
              _h_ntag, h_regime, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hpc2 : ctx'.pc = true := by
            simpa [hctx'] using hpc
          have hpre_vlet : ctx'.memEnv.contains l := by
            simpa [hctx'] using
              typecheckExpr_mem_contains_preserved ctx e1 (fuel' - 1) result1 (by simpa using htc1) l hpre
          have hwf_ctx' : wfTypeContext ctx' := by
            rw [hctx']
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hwfRes1 := typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) result1 hwf htc1'
            have hmono1 := typecheck_nextLoc_mono ctx e1 (fuel' - 1) result1 htc1'
            refine ⟨hwfRes1, ?_, ?_⟩
            · exact varEnvRefLocsBounded_update
                (varEnvRefLocsBounded_mono hwf.2.1 hmono1)
                (typecheckExpr_preserves_etypRefLocsBounded ctx e1 (fuel' - 1) result1 hwf htc1')
            · exact varEnvClosuresCapturedRefLocsBounded_update
                (varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono1)
                (typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctx e1 (fuel' - 1) result1 hwf htc1')
          have hbnd_ctx' : TagBoundedCtx ctx' := by
            rw [hctx']
            simpa [updateCtxFromResult, ctxAfter] using
              typecheckExpr_TagBoundedCtx_varEnv_update ctx e1 (fuel' - 1) result1
                (by simpa using htc1) hbnd x
          rcases ih (fuel' - 1) hltSub ctx' e2 result2
              (by simpa [hctx'] using htc2) hwf_ctx' hbnd_ctx' hpc2 l qt_out hlookup2 hpre_vlet with
            ⟨hpoison2, hguard2⟩
          refine ⟨?_, ?_⟩
          · intro hpoison
            rcases hpoison2 hpoison with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [hctx'] using hlookup_mid) hpre with
              ⟨hpoison1, _hguard1⟩
            exact hpoison1 hpoison_mid
          · intro k htag hk hnotfun
            rcases hguard2 k htag (by simpa [h_regime] using hk) hnotfun with
              ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_mid
                (by simpa [hctx'] using hlookup_mid) hpre with
              ⟨_hpoison1, hguard1⟩
            exact hguard1 k htag_mid (by simpa [hctx'] using hk_mid) hnotfun_mid
      | newRef e1 =>
          have htcNew : typecheckNewRef ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckNewRef_structure ctx e1 fuel' res htcNew with
            ⟨result1, lfresh, htc1, _hlfresh, _hInt, _hRetEtyp, _hRetPoison, _hRetPred, h_mem,
              _h_tag, _h_nextLoc, _h_nextTag, h_regime⟩
          by_cases hEq : l = lfresh
          · subst l
            have hlookup_stored :
                res.memEnv'.lookup lfresh =
                  some { etyp := ETyp.int
                         poison := true
                         pred := Predicate.noPred } := by
              rw [h_mem]
              simp [hpc, joinPoison, updateMemEnv, MemoryTypeEnv.lookup]
            have hqt : qt_out = { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
              have hsomes : some qt_out = some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
                calc
                  some qt_out = res.memEnv'.lookup lfresh := by symm; exact hlookup_out
                  _ = some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := hlookup_stored
              exact Option.some.inj hsomes
            subst hqt
            refine ⟨?_, ?_⟩
            · intro hpoison
              simp at hpoison
            · intro k htag hk hnotfun
              simp [qtypGuardTag] at htag
          · have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
              rw [h_mem] at hlookup_out
              rw [MemoryTypeEnv_lookup_updateMemEnv_ne (l := lfresh) (l' := l)
                    (qt := { etyp := ETyp.int
                             poison := joinPoison ctx.pc result1.qualType.poison
                             pred := if ctx.pc then Predicate.noPred else result1.qualType.pred }) hEq] at hlookup_out
              exact hlookup_out
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hwf hbnd hpc l qt_out hlookup1 hpre with
              ⟨hpoison1, hguard1⟩
            refine ⟨?_, ?_⟩
            · intro hpoison
              exact hpoison1 hpoison
            · intro k htag hk hnotfun
              exact hguard1 k htag (by simpa [h_regime] using hk) hnotfun
      | assign e1 e2 =>
          have htcAssign : typecheckAssign ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckAssign_memEnv_formula ctx e1 e2 fuel' res htcAssign with
            ⟨result1, result2, ls, htc1, _hRef, htc2, _hInt, h_mem, h_regime⟩
          by_cases hIn : l ∈ ls
          · have hlookup_formula :
                (match Std.ExtTreeSet.toList ls with
                  | [l0] =>
                      updateMemEnv result2.memEnv' l0
                        { etyp := ETyp.int
                          poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                          pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
                  | _ =>
                      updateLocsetWeak result2.memEnv' ls
                        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                        (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l = some qt_out := by
              simpa [h_mem] using! hlookup_out
            cases hls : Std.ExtTreeSet.toList ls with
            | nil =>
                have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                simp [hls] at hInList
            | cons x xs =>
                cases xs with
                | nil =>
                    have hlEq : l = x := by
                      have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                      simpa [hls] using hInList
                    subst l
                    have hlookup_single :
                        (updateMemEnv result2.memEnv' x
                          { etyp := ETyp.int
                            poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                            pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x = some qt_out := by
                      simpa [hls] using hlookup_formula
                    have hqt :
                        qt_out =
                          { etyp := ETyp.int
                            poison := true
                            pred := Predicate.noPred } := by
                      have hsomes :
                          some qt_out =
                            some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
                        calc
                          some qt_out =
                              (updateMemEnv result2.memEnv' x
                                { etyp := ETyp.int
                                  poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                                  pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x := by
                                    symm
                                    exact hlookup_single
                          _ = some { etyp := ETyp.int, poison := true, pred := Predicate.noPred } := by
                                simp [hpc, joinPoison, updateMemEnv, MemoryTypeEnv.lookup]
                      exact Option.some.inj hsomes
                    subst hqt
                    refine ⟨?_, ?_⟩
                    · intro hpoison
                      simp at hpoison
                    · intro k htag hk hnotfun
                      simp [qtypGuardTag] at htag
                | cons y ys =>
                    have hlookup_weak :
                        (updateLocsetWeak result2.memEnv' ls
                          (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                          (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l = some qt_out := by
                      simpa [hls] using hlookup_formula
                    unfold updateLocsetWeak at hlookup_weak
                    set joined :=
                      LocSet.fold ls
                        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison),
                          if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
                        (fun (accP, accPred) l0 =>
                          match result2.memEnv'.get? l0 with
                          | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                          | none => (accP, Predicate.noPred)) with hjoined
                    set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
                    dsimp at hlookup_weak
                    unfold LocSet.fold at hlookup_weak
                    rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
                    have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
                    have hlookup_final :
                        (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l = some finalQt :=
                      list_fold_updateMemEnv_lookup_eq_of_mem ls.toList result2.memEnv' l finalQt hInList rfl
                    have hqt : qt_out = finalQt := by
                      have hsomes : some qt_out = some finalQt := by
                        calc
                          some qt_out =
                              (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l := by
                                symm
                                exact hlookup_weak
                          _ = some finalQt := hlookup_final
                      exact Option.some.inj hsomes
                    subst hqt
                    have hpoison : finalQt.poison = true := by
                      simp [finalQt, joined, hpc]
                      unfold LocSet.fold
                      rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                      simpa using!
                        list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
                    have hpred : finalQt.pred = Predicate.noPred := by
                      simp [finalQt, joined, hpc]
                      unfold LocSet.fold
                      rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                      simpa using! list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
                    refine ⟨?_, ?_⟩
                    · intro hpoison'
                      rw [hpoison] at hpoison'
                      simp at hpoison'
                    · intro k htag hk hnotfun
                      have hfalse : False := by
                        simp [qtypGuardTag, hpred] at htag
                      exact False.elim hfalse
          · have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
              have hlookup_eq :
                  (match Std.ExtTreeSet.toList ls with
                    | [l0] =>
                        updateMemEnv result2.memEnv' l0
                          { etyp := ETyp.int
                            poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                            pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
                    | _ =>
                        updateLocsetWeak result2.memEnv' ls
                          (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                          (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l =
                    result2.memEnv'.lookup l :=
                assign_memEnv_formula_lookup_eq_of_not_mem
                  result2.memEnv' ls
                  (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                  (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
                  l hIn
              have hlookup_formula :
                  (match Std.ExtTreeSet.toList ls with
                    | [l0] =>
                        updateMemEnv result2.memEnv' l0
                          { etyp := ETyp.int
                            poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                            pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
                    | _ =>
                        updateLocsetWeak result2.memEnv' ls
                          (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                          (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l =
                  some qt_out := by
                simpa [h_mem] using! hlookup_out
              calc
                result2.memEnv'.lookup l =
                    (match Std.ExtTreeSet.toList ls with
                      | [l0] =>
                          updateMemEnv result2.memEnv' l0
                            { etyp := ETyp.int
                              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
                      | _ =>
                          updateLocsetWeak result2.memEnv' ls
                            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l := by
                      symm
                      exact hlookup_eq
                _ = some qt_out := hlookup_formula
            have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
              simpa [updateCtxFromResult] using hpc
            have hpre_asgn : result1.memEnv'.contains l :=
              typecheckExpr_mem_contains_preserved ctx e1 (fuel' - 1) result1 (by simpa using htc1) l hpre
            have hwf_ucr : wfTypeContext (updateCtxFromResult ctx result1) :=
              wfTypeContext_of_wfTypeResult ctx result1
                (typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) result1 hwf (by simpa using! htc1))
                hwf (typecheck_nextLoc_mono ctx e1 (fuel' - 1) result1 (by simpa using! htc1))
            have hbnd_ucr : TagBoundedCtx (updateCtxFromResult ctx result1) := by
              simpa [updateCtxFromResult, ctxAfter] using
                typecheckExpr_preserves_TagBoundedCtx ctx e1 (fuel' - 1) result1 (by simpa using htc1) hbnd
            rcases ih (fuel' - 1) hltSub
                (updateCtxFromResult ctx result1) e2 result2
                (by simpa [updateCtxFromResult] using htc2)
                hwf_ucr hbnd_ucr hpc2 l qt_out hlookup2 (by simpa [updateCtxFromResult] using hpre_asgn) with
              ⟨hpoison2, hguard2⟩
            refine ⟨?_, ?_⟩
            · intro hpoison
              rcases hpoison2 hpoison with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 result1
                  (by simpa using htc1) hwf hbnd hpc l qt_mid
                  (by simpa [updateCtxFromResult] using hlookup_mid) hpre with
                ⟨hpoison1, _hguard1⟩
              exact hpoison1 hpoison_mid
            · intro k htag hk hnotfun
              have hk2 : result2.regime'.lookup? k = some true := by
                exact
                  monotoneStep_lookup_back
                    (invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls)
                    k true (by simpa [h_regime] using hk)
              rcases hguard2 k htag hk2 hnotfun with
                ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 result1
                  (by simpa using htc1) hwf hbnd hpc l qt_mid
                  (by simpa [updateCtxFromResult] using hlookup_mid) hpre with
                ⟨_hpoison1, hguard1⟩
              exact hguard1 k htag_mid (by simpa [updateCtxFromResult] using hk_mid) hnotfun_mid
      | ite e1 e2 e3 =>
          have htcIf : typecheckIf ctx e1 e2 e3 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htcIf with h1 | h2 | hstd
          · rcases h1 with ⟨k, deps, hmg, _hk, _res1, htc1p, _hBool, res2, _, htc2, _, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            have hb1 : ctx.nextTag ≤ _res1.nextTag' :=
              typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) _res1 htc1p
            let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                    nextTag := _res1.nextTag', nextBind := _res1.nextBind',
                                                    declaredExternRefs := _res1.declared' }
            have hpcTrue : ctxTrue.pc = true := by
              simpa [ctxTrue] using hpc
            have hwf_ctxTrue : wfTypeContext ctxTrue := by
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            have hk_lt : k < ctx.nextTag :=
              matchGuard_tag_bounded e1 ctx.memEnv ctx.varEnv ctx.bindEnv (fuel' - 1) k deps ctx.nextTag
                hmg hbnd.2.1.1 hbnd.2.1.2
            have hbnd_ctxTrue : TagBoundedCtx ctxTrue :=
              ⟨tagEnvBounded_mono _ _ _
                 (tagEnvBounded_insert_of_lt ctx.tagEnv ctx.nextTag k ⟨true, deps⟩ hbnd.1 hk_lt) hb1,
               ⟨predTagsBoundedInVarEnv_mono hbnd.2.1.1 hb1, predTagsBoundedInMemEnv_mono hbnd.2.1.2 hb1⟩,
               varEnvClosuresCapturedBounded_mono hbnd.2.2 hb1⟩
            rcases ih (fuel' - 1) hltSub ctxTrue e2 res2
                (by simpa [ctxTrue] using htc2) hwf_ctxTrue hbnd_ctxTrue hpcTrue l qt_out
                (by simpa [h_mem] using hlookup_out) (by simpa [ctxTrue] using hpre) with
              ⟨hpoison2, hguard2⟩
            refine ⟨?_, ?_⟩
            · intro hpoison
              rcases hpoison2 hpoison with ⟨qt_in, hlookup_in, hpoison_in⟩
              exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, hpoison_in⟩
            · intro k' htag hk hnotfun
              rcases hguard2 k' htag (by simpa [h_regime] using hk) hnotfun with
                ⟨qt_in, hlookup_in, htag_in, hk_in, hnotfun_in⟩
              exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, htag_in,
                by simpa [ctxTrue] using hk_in, hnotfun_in⟩
          · rcases h2 with ⟨k, deps, hmg, _hk, _res1, htc1p, _hBool, res2, res3, htc2_true, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            have hb1 : ctx.nextTag ≤ _res1.nextTag' :=
              typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) _res1 htc1p
            let ctxFalse : TypeContext :=
              { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                         nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind',
                         declaredExternRefs := res2.declared' }
            have hpcFalse : ctxFalse.pc = true := by
              simpa [ctxFalse] using hpc
            have hmonoT : ctx.nextTag ≤ res2.nextTag' :=
              Nat.le_trans hb1 (typecheck_nextTag_mono
                { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                           nextTag := _res1.nextTag', nextBind := _res1.nextBind',
                           declaredExternRefs := _res1.declared' }
                e2 (fuel' - 1) res2 htc2_true)
            have hwf_ctxFalse : wfTypeContext ctxFalse := by
              have hmono : ctx.nextLoc ≤ res2.nextLoc' :=
                typecheck_nextLoc_mono { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                  nextTag := _res1.nextTag', nextBind := _res1.nextBind',
                                                  declaredExternRefs := _res1.declared' }
                  e2 (fuel' - 1) res2 (by simpa using! htc2_true)
              exact ⟨fun l hl => Nat.lt_of_lt_of_le (hwf.1 l hl) hmono,
                     varEnvRefLocsBounded_mono hwf.2.1 hmono,
                     varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hmono⟩
            have hk_lt : k < ctx.nextTag :=
              matchGuard_tag_bounded e1 ctx.memEnv ctx.varEnv ctx.bindEnv (fuel' - 1) k deps ctx.nextTag
                hmg hbnd.2.1.1 hbnd.2.1.2
            have hbnd_ctxFalse : TagBoundedCtx ctxFalse :=
              ⟨tagEnvBounded_insert_of_lt ctx.tagEnv res2.nextTag' k ⟨false, deps⟩
                 (tagEnvBounded_mono ctx.tagEnv ctx.nextTag res2.nextTag' hbnd.1 hmonoT)
                 (Nat.lt_of_lt_of_le hk_lt hmonoT),
               ⟨predTagsBoundedInVarEnv_mono hbnd.2.1.1 hmonoT,
                predTagsBoundedInMemEnv_mono hbnd.2.1.2 hmonoT⟩,
               varEnvClosuresCapturedBounded_mono hbnd.2.2 hmonoT⟩
            rcases ih (fuel' - 1) hltSub ctxFalse e3 res3
                (by simpa [ctxFalse] using htc3) hwf_ctxFalse hbnd_ctxFalse hpcFalse l qt_out
                (by simpa [h_mem] using hlookup_out) (by simpa [ctxFalse] using hpre) with
              ⟨hpoison3, hguard3⟩
            refine ⟨?_, ?_⟩
            · intro hpoison
              rcases hpoison3 hpoison with ⟨qt_in, hlookup_in, hpoison_in⟩
              exact ⟨qt_in, by simpa [ctxFalse] using hlookup_in, hpoison_in⟩
            · intro k' htag hk hnotfun
              rcases hguard3 k' htag (by simpa [h_regime] using hk) hnotfun with
                ⟨qt_in, hlookup_in, htag_in, hk_in, hnotfun_in⟩
              exact ⟨qt_in, by simpa [ctxFalse] using hlookup_in, htag_in,
                by simpa [ctxFalse] using hk_in, hnotfun_in⟩
          · obtain ⟨_hstdCase, res1, htc1, _hBool, res2, htc2, res3, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp, _h_pred⟩ := hstd
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [h_mem] using hlookup_out
            let ctx' : TypeContext := ctxAfter ctx res1
            let pc' := joinPoison ctx.pc res1.qualType.poison
            let ctx'' : TypeContext := { ctx' with pc := pc' }
            let ctxForE3 : TypeContext :=
              { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag', nextBind := res2.nextBind', declaredExternRefs := res2.declared' }
            have hpc'' : ctx''.pc = true := by
              simp [ctx'', pc', hpc, joinPoison]
            have hpre_r1 : res1.memEnv'.contains l :=
              typecheckExpr_mem_contains_preserved ctx e1 (fuel' - 1) res1 (by simpa using htc1) l hpre
            have hwf_ctx'' : wfTypeContext ctx'' :=
              wfTypeContext_of_wfTypeResult ctx res1
                (typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) res1 hwf (by simpa using! htc1))
                hwf (typecheck_nextLoc_mono ctx e1 (fuel' - 1) res1 (by simpa using! htc1))
            have hwf_ctxE3 : wfTypeContext ctxForE3 := by
              have hmono2 : ctx''.nextLoc ≤ res2.nextLoc' :=
                typecheck_nextLoc_mono ctx'' e2 (fuel' - 1) res2
                  (by simpa [ctx'', ctx', pc', ctxAfter] using! htc2)
              exact ⟨fun l hl => Nat.lt_of_lt_of_le (hwf_ctx''.1 l hl) hmono2,
                     varEnvRefLocsBounded_mono hwf_ctx''.2.1 hmono2,
                     varEnvClosuresCapturedRefLocsBounded_mono hwf_ctx''.2.2 hmono2⟩
            have hbnd_ctx'' : TagBoundedCtx ctx'' := by
              simpa [ctx'', ctx', pc'] using!
                typecheckExpr_preserves_TagBoundedCtx ctx e1 (fuel' - 1) res1 (by simpa using htc1) hbnd
            have hbnd_ctxE3 : TagBoundedCtx ctxForE3 := by
              have hmono2T : ctx''.nextTag ≤ res2.nextTag' :=
                typecheck_nextTag_mono ctx'' e2 (fuel' - 1) res2
                  (by simpa [ctx'', ctx', pc', ctxAfter] using! htc2)
              obtain ⟨ht, hp, hc⟩ := hbnd_ctx''
              exact ⟨tagEnvBounded_mono ctx''.tagEnv ctx''.nextTag res2.nextTag' ht hmono2T,
                     ⟨predTagsBoundedInVarEnv_mono hp.1 hmono2T, predTagsBoundedInMemEnv_mono hp.2 hmono2T⟩,
                     varEnvClosuresCapturedBounded_mono hc hmono2T⟩
            refine ⟨?_, ?_⟩
            · intro hpoison
              have hcontains_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                memEnv_contains_of_lookup_some (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
              rcases joinMemEnvsStrong_contains_implies_or res2.memEnv' res3.memEnv' l hcontains_join with
                hcontains2 | hcontains3
              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
                have henv2 : res2.memEnv'.lookup l ≠ none := by
                  intro hnone
                  rw [hlookup2] at hnone
                  contradiction
                rcases joinMemEnvsStrong_lookup_clean_left
                    res2.memEnv' res3.memEnv' l qt_out hlookup_join hpoison henv2 with
                  ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                rcases ih (fuel' - 1) hltSub ctx'' e2 res2
                    (by simpa [ctx'', ctx', pc', ctxAfter] using htc2) hwf_ctx'' hbnd_ctx'' hpc'' l qt2' hlookup2'
                    (by simpa [ctx'', ctx', ctxAfter] using hpre_r1) with
                  ⟨hpoison2', _hguard2⟩
                rcases hpoison2' hpoison2 with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
                rcases ih (fuel' - 1) hltSub ctx e1 res1
                    (by simpa using htc1) hwf hbnd hpc l qt_mid
                    (by simpa [ctx'', ctx', ctxAfter] using hlookup_mid) hpre with
                  ⟨hpoison1, _hguard1⟩
                exact hpoison1 hpoison_mid
              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
                have henv3 : res3.memEnv'.lookup l ≠ none := by
                  intro hnone
                  rw [hlookup3] at hnone
                  contradiction
                rcases joinMemEnvsStrong_lookup_clean_right
                    res2.memEnv' res3.memEnv' l qt_out hlookup_join hpoison henv3 with
                  ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                rcases ih (fuel' - 1) hltSub ctxForE3 e3 res3
                    (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using htc3)
                    hwf_ctxE3 hbnd_ctxE3 (by simp [ctxForE3, ctx'', pc', hpc, joinPoison]) l qt3' hlookup3'
                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hpre_r1) with
                  ⟨hpoison3', _hguard3⟩
                rcases hpoison3' hpoison3 with ⟨qt_mid, hlookup_mid, hpoison_mid⟩
                rcases ih (fuel' - 1) hltSub ctx e1 res1
                    (by simpa using htc1) hwf hbnd hpc l qt_mid
                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hlookup_mid) hpre with
                  ⟨hpoison1, _hguard1⟩
                exact hpoison1 hpoison_mid
            · intro k htag hk hnotfun
              have hk_join : (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                simpa [h_regime] using hk
              have hcontains_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                memEnv_contains_of_lookup_some (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
              rcases joinMemEnvsStrong_contains_implies_or res2.memEnv' res3.memEnv' l hcontains_join with
                hcontains2 | hcontains3
              · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
                have htag2 : qtypGuardTag qt2 = some k :=
                  joinMemEnvsStrong_lookup_guardTag_left
                    res2.memEnv' res3.memEnv' l qt_out qt2 k hlookup_join hlookup2 htag
                have hk2 : res2.regime'.lookup? k = some true :=
                  joinRegimes_lookup_some_left res2.regime' res3.regime' k true hk_join
                have hnotfun2 : qt2.etyp.isFunctionType = false := by
                  rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                  decide
                rcases ih (fuel' - 1) hltSub ctx'' e2 res2
                    (by simpa [ctx'', ctx', pc', ctxAfter] using htc2) hwf_ctx'' hbnd_ctx'' hpc'' l qt2 hlookup2
                    (by simpa [ctx'', ctx', ctxAfter] using hpre_r1) with
                  ⟨_hpoison2, hguard2⟩
                rcases hguard2 k htag2 hk2 hnotfun2 with
                  ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
                rcases ih (fuel' - 1) hltSub ctx e1 res1
                    (by simpa using htc1) hwf hbnd hpc l qt_mid
                    (by simpa [ctx'', ctx', ctxAfter] using hlookup_mid) hpre with
                  ⟨_hpoison1, hguard1⟩
                exact hguard1 k htag_mid (by simpa [ctx'', ctx', ctxAfter] using hk_mid) hnotfun_mid
              · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
                have htag3 : qtypGuardTag qt3 = some k :=
                  joinMemEnvsStrong_lookup_guardTag_right
                    res2.memEnv' res3.memEnv' l qt_out qt3 k hlookup_join hlookup3 htag
                have hk3 : res3.regime'.lookup? k = some true :=
                  joinRegimes_lookup_some_right res2.regime' res3.regime' k true hk_join
                have hnotfun3 : qt3.etyp.isFunctionType = false := by
                  rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                  decide
                rcases ih (fuel' - 1) hltSub ctxForE3 e3 res3
                    (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using htc3)
                    hwf_ctxE3 hbnd_ctxE3 (by simp [ctxForE3, ctx'', pc', hpc, joinPoison]) l qt3 hlookup3
                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hpre_r1) with
                  ⟨_hpoison3, hguard3⟩
                rcases hguard3 k htag3 hk3 hnotfun3 with
                  ⟨qt_mid, hlookup_mid, htag_mid, hk_mid, hnotfun_mid⟩
                rcases ih (fuel' - 1) hltSub ctx e1 res1
                    (by simpa using htc1) hwf hbnd hpc l qt_mid
                    (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hlookup_mid) hpre with
                  ⟨_hpoison1, hguard1⟩
                exact hguard1 k htag_mid (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hk_mid) hnotfun_mid
      | app e1 e2 =>
          have htcApp : typecheckApp ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          cases fuel' with
          | zero =>
              simp [typecheckApp] at htcApp
          | succ fuelApp =>
              obtain ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩ :=
                typecheckApp_arrow_structure_full ctx e1 e2 fuelApp res htcApp
              let ctxFun : TypeContext :=
                { ctx with
                  memEnv := result2.memEnv'
                  tagEnv := result2.tagEnv'
                  nextLoc := result2.nextLoc'
                  nextTag := result2.nextTag', nextBind := result2.nextBind'
                  regime := result2.regime'
                  declaredExternRefs := result2.declared' }
              have hpcFun : ctxFun.pc = true := by
                simpa [ctxFun] using hpc
              have hwf_ctxFun : wfTypeContext ctxFun :=
                wfTypeContext_of_wfTypeResult ctx result2
                  (typecheckExpr_preserves_wfTypeResult ctx e2 fuelApp result2 hwf (by simpa using! htc2))
                  hwf (typecheck_nextLoc_mono ctx e2 fuelApp result2 (by simpa using! htc2))
              have hbnd_ctxFun : TagBoundedCtx ctxFun := by
                simpa [ctxFun, ctxAfter] using
                  typecheckExpr_preserves_TagBoundedCtx ctx e2 fuelApp result2 (by simpa using htc2) hbnd
              have hpre_r2 : result2.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved ctx e2 fuelApp result2 (by simpa using htc2) l hpre
              have hpre_r1 : result1.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved ctxFun e1 fuelApp result1
                  (by simpa [ctxFun] using htc1) l (by simpa [ctxFun] using hpre_r2)
              have hbackToCtx_poison :
                  ∀ qt_mid,
                    result1.memEnv'.lookup l = some qt_mid →
                    qt_mid.poison = false →
                    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
                intro qt_mid hlookup_mid hpoison_mid
                rcases ih fuelApp (by omega) ctxFun e1 result1
                    (by simpa [ctxFun] using htc1) hwf_ctxFun hbnd_ctxFun hpcFun l qt_mid hlookup_mid
                    (by simpa [ctxFun] using hpre_r2) with
                  ⟨hpoison1, _hguard1⟩
                rcases hpoison1 hpoison_mid with ⟨qt_arg, hlookup_arg, hpoison_arg⟩
                rcases ih fuelApp (by omega) ctx e2 result2
                    (by simpa using htc2) hwf hbnd hpc l qt_arg
                    (by simpa [ctxFun] using hlookup_arg) hpre with
                  ⟨hpoison2, _hguard2⟩
                exact hpoison2 hpoison_arg
              have hbackToCtx_guard :
                  ∀ qt_mid k,
                    result1.memEnv'.lookup l = some qt_mid →
                    qtypGuardTag qt_mid = some k →
                    result1.regime'.lookup? k = some true →
                    qt_mid.etyp.isFunctionType = false →
                    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
                      qtypGuardTag qt_in = some k ∧
                      ctx.regime.lookup? k = some true ∧
                      qt_in.etyp.isFunctionType = false := by
                intro qt_mid k hlookup_mid htag_mid hk_mid hnotfun_mid
                rcases ih fuelApp (by omega) ctxFun e1 result1
                    (by simpa [ctxFun] using htc1) hwf_ctxFun hbnd_ctxFun hpcFun l qt_mid hlookup_mid
                    (by simpa [ctxFun] using hpre_r2) with
                  ⟨_hpoison1, hguard1⟩
                rcases hguard1 k htag_mid hk_mid hnotfun_mid with
                  ⟨qt_arg, hlookup_arg, htag_arg, hk_arg, hnotfun_arg⟩
                rcases ih fuelApp (by omega) ctx e2 result2
                    (by simpa using htc2) hwf hbnd hpc l qt_arg
                    (by simpa [ctxFun] using hlookup_arg) hpre with
                  ⟨_hpoison2, hguard2⟩
                exact hguard2 k htag_arg (by simpa [ctxFun] using hk_arg) hnotfun_arg
              have hcontains_res : res.memEnv'.contains l := by
                exact memEnv_contains_of_lookup_some res.memEnv' l qt_out hlookup_out
              have hlookup_res_ctx :
                  (ctxAfter ctx res).memEnv.lookup l = some qt_out := by
                simpa [ctxAfter] using hlookup_out
              refine ⟨?_, ?_⟩
              · intro hpoison_out
                cases hcases with
                | inl harrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1,
                        _hnpure, _hnempty, _hsub, hmap, heq_results, h_join, rfl⟩ := harrow
                    have hmember_origin :
                        ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                          ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
                      intro srcRes hsrc_mem hsrc_contains
                      have hsrc_results : srcRes ∈ results := by
                        simpa [heq_results] using hsrc_mem
                      rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bounds
                          (applyOne := fun tcl cursor bn =>
                            applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                              ctx result1 cursor bn fuelApp)
                          (baseTag := result1.nextTag') (baseLoc := result1.nextLoc')
                          (hmono := by
                            intro tcl cursor bn result hct hcl happly
                            refine ⟨?_, ?_⟩
                            · exact Nat.le_trans hct (applyFnTClosureAtCursor_nextTag_advance tcl ctx
                                st1 st2 p p1 etyp2 p2 pred2 result1 result cursor bn fuelApp happly)
                            · exact applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
                                etyp2 p2 pred2 result1 result cursor bn fuelApp hcl
                                (fun m hm e c r htc => typecheck_nextLoc_mono c e m r htc)
                                happly)
                          (hbaseTag := Nat.le_refl _) (hbaseLoc := Nat.le_refl _) hmap hsrc_results with
                        ⟨tcl, _htcl_mem, cursor, bn, hcursorTag, hcursorLoc, happly_src⟩
                      rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have hpoison_src : qt_src.poison = false :=
                        joinTypeResults_lookup_member_poison_imp
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hlookup_src_ctx hpoison_out
                      cases tcl with
                      | regular x body tenv =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyFnTClosure (.regular x body tenv) st1 st2 p p1 etyp2 p2 pred2
                                ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyFnTClosure
                            unfold applyFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          rcases applyFnTClosure_regular_structure
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor fuelApp x body tenv
                              srcRes happly_old with
                            ⟨fuelBody, hfuelBody⟩
                          have happly_succ :
                              applyFnTClosure (FnTClosure.regular x body tenv)
                                st1 st2 p p1 etyp2 p2 pred2 ctx rCursor (Nat.succ fuelBody) = .ok srcRes := by
                            simpa [hfuelBody] using happly_old
                          rcases applyFnTClosure_regular_inv
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor fuelBody x body tenv srcRes
                              happly_succ with
                            ⟨result3, htcBody, _hsubBody, hr⟩
                          let bodyCtx : TypeContext :=
                            { ctx with
                              pc := joinPoison p (joinPoison p1 ctx.pc)
                              memEnv := result1.memEnv'
                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                                ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                              bindEnv := BindEnv.bindParam tenv x bn
                              tagEnv := result1.tagEnv'
                              nextTag := cursor.1
                              nextBind := bn + 1
                              nextLoc := cursor.2
                              regime := result1.regime'
                              externRefAllowed := false
                              declaredExternRefs := result1.declared' }
                          have hlookup_result3 : result3.memEnv'.lookup l = some qt_src := by
                            simpa [hr] using hlookup_src
                          have htc1' : typecheck ctxFun e1 fuelApp = .ok result1 := by
                            simpa [typecheck] using htc1
                          have hwf_bodyCtx : wfTypeContext bodyCtx := by
                            simp only [bodyCtx, wfTypeContext]
                            have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                              ctxFun e1 fuelApp result1 hwf_ctxFun htc1'
                            have hmono_e1 := typecheck_nextLoc_mono ctxFun e1 fuelApp result1 htc1'
                            have htc2' : typecheck ctx e2 fuelApp = .ok result2 := by
                              simpa [typecheck] using htc2
                            exact ⟨(fun l hl =>
                              Nat.lt_of_lt_of_le
                                (typecheckExpr_preserves_wfTypeResult
                                  ctxFun e1 fuelApp result1 hwf_ctxFun htc1' l hl)
                                hcursorLoc),
                              varEnvRefLocsBounded_update
                                (varEnvRefLocsBounded_ofCaptured
                                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                                    (CapturedEnvRefLocsFullBounded_mono
                                      (by rw [_hetyp1] at hClosRL; exact hClosRL _ _htcl_mem)
                                      hcursorLoc)))
                                (by
                                  have h := typecheckExpr_preserves_etypRefLocsBounded
                                    ctx e2 fuelApp result2 hwf htc2'
                                  rw [_hqt2] at h
                                  exact etypRefLocsBounded_mono h
                                    (Nat.le_trans hmono_e1 hcursorLoc)),
                              varEnvClosuresCapturedRefLocsBounded_update
                                (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                                  (CapturedEnvRefLocsFullBounded_mono
                                    (by rw [_hetyp1] at hClosRL; exact hClosRL _ _htcl_mem)
                                    hcursorLoc))
                                (by
                                  have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                                    ctx e2 fuelApp result2 hwf htc2'
                                  rw [_hqt2] at h
                                  exact etypClosuresCapturedRefLocsBounded_mono h
                                    (Nat.le_trans hmono_e1 hcursorLoc))⟩
                          have hbnd_bodyCtx : TagBoundedCtx bodyCtx := by
                            have hClosTag := typecheckExpr_preserves_qualType_closures_bounded
                              ctxFun e1 fuelApp result1 htc1' hbnd_ctxFun.2.1 hbnd_ctxFun.2.2
                            obtain ⟨htagE1, hpredE1, _hclosE1⟩ :=
                              typecheckExpr_preserves_TagBoundedCtx ctxFun e1 fuelApp result1 htc1' hbnd_ctxFun
                            have htc2'' : typecheck ctx e2 fuelApp = .ok result2 := by simpa [typecheck] using htc2
                            have hr2le : result2.nextTag' ≤ cursor.1 :=
                              Nat.le_trans
                                (by simpa [ctxFun] using typecheck_nextTag_mono ctxFun e1 fuelApp result1 htc1')
                                hcursorTag
                            have hQt2Pred :=
                              (typecheckExpr_preserves_predTagsBounded ctx e2 fuelApp result2 htc2'' hbnd.2.1 hbnd.2.2).2
                            have hQt2Clos := typecheckExpr_preserves_qualType_closures_bounded
                              ctx e2 fuelApp result2 htc2'' hbnd.2.1 hbnd.2.2
                            have htenv : CapturedEnvFullBounded tenv result1.nextTag' := by
                              rw [_hetyp1] at hClosTag; exact hClosTag _ _htcl_mem
                            refine ⟨tagEnvBounded_mono result1.tagEnv' result1.nextTag' cursor.1 htagE1 hcursorTag,
                              ⟨predTagsBoundedInVarEnv_update
                                (predTagsBoundedInVarEnv_ofCaptured
                                  (capturedPredTagsBounded_of_fullBounded
                                    (CapturedEnvFullBounded_mono htenv hcursorTag))) ?_,
                               predTagsBoundedInMemEnv_mono hpredE1.2 hcursorTag⟩,
                              varEnvClosuresCapturedBounded_update
                                (varEnvClosuresCapturedBounded_ofCaptured
                                  (CapturedEnvFullBounded_mono htenv hcursorTag)) ?_⟩
                            · have h := hQt2Pred; rw [_hqt2] at h; exact qtypPredTagBounded_mono h hr2le
                            · have h := hQt2Clos; rw [_hqt2] at h; exact etypClosuresFullBounded_mono h hr2le
                          rcases ih fuelBody (by omega) bodyCtx body result3
                              (by simpa [bodyCtx] using htcBody)
                              hwf_bodyCtx hbnd_bodyCtx
                              (by simp [bodyCtx, hpc, joinPoison]) l qt_src hlookup_result3
                              (by simpa [bodyCtx] using hpre_r1) with
                            ⟨hpoison3, _hguard3⟩
                          rcases hpoison3 hpoison_src with ⟨qt_mid, hlookup_mid_body, hpoison_mid⟩
                          exact
                            hbackToCtx_poison qt_mid
                              (by simpa [bodyCtx] using hlookup_mid_body)
                              hpoison_mid
                      | extern id x retSpec effects capturedEnv declaredArgQt captures =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyFnTClosure (.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyFnTClosure
                            unfold applyFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          rcases applyFnTClosure_extern_ok_memEnv_poison_origin ctx st1 st2 p p1
                              etyp2 p2 pred2 rCursor fuelApp id x retSpec effects capturedEnv srcRes
                              happly_old hpc l qt_src hlookup_src hpoison_src with
                            ⟨qt_mid, hlookup_mid, hpoison_mid⟩
                          exact hbackToCtx_poison qt_mid (by simpa [rCursor] using hlookup_mid) hpoison_mid
                    rcases joinTypeResults_mem_contains_head_or_rest
                        ctx first rest res h_join l hcontains_res with
                      hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                    · exact hmember_origin first (by simp) hhead
                    · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
                | inr hparrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1,
                        _hnempty, _hsub, hmap, heq_results, h_join, rfl⟩ := hparrow
                    have hmember_origin :
                        ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                          ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
                      intro srcRes hsrc_mem hsrc_contains
                      have hsrc_results : srcRes ∈ results := by
                        simpa [heq_results] using hsrc_mem
                      rcases applyClosuresThreaded_ok_mem_output_exists_input
                          (applyOne := fun tcl cursor bn =>
                            applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                              ctx result1 cursor bn fuelApp)
                          hmap hsrc_results with
                        ⟨tcl, _htcl_mem, cursor, bn, happly_src⟩
                      rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have hpoison_src : qt_src.poison = false :=
                        joinTypeResults_lookup_member_poison_imp
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hlookup_src_ctx hpoison_out
                      cases tcl with
                      | regular x pbody tenv =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyPFnTClosure (.regular x pbody tenv) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyPFnTClosure
                            unfold applyPFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          have hcontains_result1 : result1.memEnv'.contains l := by
                            have hcontains_cursor : rCursor.memEnv'.contains l :=
                              applyPFnTClosure_mem_subset
                                (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                                (result2 := rCursor) (fuel := fuelApp)
                                (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                                happly_old l hsrc_contains
                            simpa [rCursor] using hcontains_cursor
                          rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_result1 with
                            ⟨qt_mid, hlookup_mid⟩
                          have hlookup_preserved :
                              srcRes.memEnv'.lookup l = some qt_mid := by
                            exact
                              applyPFnTClosure_preserves_memEnv_lookup
                                (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                                (result2 := rCursor) (fuel := fuelApp)
                                (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                                happly_old l qt_mid (by simpa [rCursor] using hlookup_mid)
                          have hqt_mid : qt_src = qt_mid := by
                            rw [hlookup_src] at hlookup_preserved
                            exact Option.some.inj hlookup_preserved
                          exact hbackToCtx_poison qt_mid hlookup_mid (by simpa [hqt_mid] using hpoison_src)
                      | extern id x retSpec capturedEnv declaredArgQt captures =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyPFnTClosure (.extern id x retSpec capturedEnv declaredArgQt captures) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyPFnTClosure
                            unfold applyPFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          have hmem_eq := applyPFnTClosure_extern_memEnv_eq
                            ctx st1 st2 p p1 etyp2 p2 pred2 rCursor srcRes fuelApp
                            id x retSpec capturedEnv declaredArgQt happly_old
                          have hlookup_mid : result1.memEnv'.lookup l = some qt_src := by
                            have hlookup_cursor : rCursor.memEnv'.lookup l = some qt_src := by
                              rw [← hmem_eq]; exact hlookup_src
                            simpa [rCursor] using hlookup_cursor
                          exact hbackToCtx_poison qt_src hlookup_mid hpoison_src
                    rcases joinTypeResults_mem_contains_head_or_rest
                        ctx first rest res h_join l hcontains_res with
                      hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                    · exact hmember_origin first (by simp) hhead
                    · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
              · intro k htag hk hnotfun
                cases hcases with
                | inl harrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1,
                        _hnpure, _hnempty, _hsub, hmap, heq_results, h_join, rfl⟩ := harrow
                    have hmember_origin :
                        ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                          ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
                            qtypGuardTag qt_in = some k ∧
                            ctx.regime.lookup? k = some true ∧
                            qt_in.etyp.isFunctionType = false := by
                      intro srcRes hsrc_mem hsrc_contains
                      have hsrc_results : srcRes ∈ results := by
                        simpa [heq_results] using hsrc_mem
                      rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bounds
                          (applyOne := fun tcl cursor bn =>
                            applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                              ctx result1 cursor bn fuelApp)
                          (baseTag := result1.nextTag') (baseLoc := result1.nextLoc')
                          (hmono := by
                            intro tcl cursor bn result hct hcl happly
                            refine ⟨?_, ?_⟩
                            · exact Nat.le_trans hct (applyFnTClosureAtCursor_nextTag_advance tcl ctx
                                st1 st2 p p1 etyp2 p2 pred2 result1 result cursor bn fuelApp happly)
                            · exact applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1
                                etyp2 p2 pred2 result1 result cursor bn fuelApp hcl
                                (fun m hm e c r htc => typecheck_nextLoc_mono c e m r htc)
                                happly)
                          (hbaseTag := Nat.le_refl _) (hbaseLoc := Nat.le_refl _) hmap hsrc_results with
                        ⟨tcl, _htcl_mem, cursor, bn, hcursorTag, hcursorLoc, happly_src⟩
                      rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have htag_src : qtypGuardTag qt_src = some k :=
                        joinTypeResults_lookup_member_guardTag_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src k hlookup_res_ctx hlookup_src_ctx htag
                      have hreg_src : (ctxAfter ctx srcRes).regime.lookup? k = some true :=
                        joinTypeResults_lookup_member_regime_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem k true hk
                      have hetyp_eq : qt_out.etyp = qt_src.etyp :=
                        joinTypeResults_lookup_member_etyp_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hlookup_src_ctx
                      have hnotfun_src : qt_src.etyp.isFunctionType = false := by
                        simpa [hetyp_eq.symm] using hnotfun
                      cases tcl with
                      | regular x body tenv =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyFnTClosure (.regular x body tenv) st1 st2 p p1 etyp2 p2 pred2
                                ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyFnTClosure
                            unfold applyFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          rcases applyFnTClosure_regular_structure
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor fuelApp x body tenv
                              srcRes happly_old with
                            ⟨fuelBody, hfuelBody⟩
                          have happly_succ :
                              applyFnTClosure (FnTClosure.regular x body tenv)
                                st1 st2 p p1 etyp2 p2 pred2 ctx rCursor (Nat.succ fuelBody) =
                                  .ok srcRes := by
                            simpa [hfuelBody] using happly_old
                          rcases applyFnTClosure_regular_inv
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor fuelBody x body tenv srcRes
                              happly_succ with
                            ⟨result3, htcBody, _hsubBody, hr⟩
                          let bodyCtx : TypeContext :=
                            { ctx with
                              pc := joinPoison p (joinPoison p1 ctx.pc)
                              memEnv := result1.memEnv'
                              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                                ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                              bindEnv := BindEnv.bindParam tenv x bn
                              tagEnv := result1.tagEnv'
                              nextTag := cursor.1
                              nextBind := bn + 1
                              nextLoc := cursor.2
                              regime := result1.regime'
                              externRefAllowed := false
                              declaredExternRefs := result1.declared' }
                          have hlookup_result3 : result3.memEnv'.lookup l = some qt_src := by
                            simpa [hr] using hlookup_src
                          have hreg_result3 : result3.regime'.lookup? k = some true := by
                            simpa [ctxAfter, hr] using hreg_src
                          have htc1' : typecheck ctxFun e1 fuelApp = .ok result1 := by
                            simpa [typecheck] using htc1
                          have hwf_bodyCtx : wfTypeContext bodyCtx := by
                            simp only [bodyCtx, wfTypeContext]
                            have hClosRL := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                              ctxFun e1 fuelApp result1 hwf_ctxFun htc1'
                            have hmono_e1 := typecheck_nextLoc_mono ctxFun e1 fuelApp result1 htc1'
                            have htc2' : typecheck ctx e2 fuelApp = .ok result2 := by
                              simpa [typecheck] using htc2
                            exact ⟨(fun l hl =>
                              Nat.lt_of_lt_of_le
                                (typecheckExpr_preserves_wfTypeResult
                                  ctxFun e1 fuelApp result1 hwf_ctxFun htc1' l hl)
                                hcursorLoc),
                              varEnvRefLocsBounded_update
                                (varEnvRefLocsBounded_ofCaptured
                                  (capturedEnvRefLocsBounded_of_fullBounded_refLocs
                                    (CapturedEnvRefLocsFullBounded_mono
                                      (by rw [_hetyp1] at hClosRL; exact hClosRL _ _htcl_mem)
                                      hcursorLoc)))
                                (by
                                  have h := typecheckExpr_preserves_etypRefLocsBounded
                                    ctx e2 fuelApp result2 hwf htc2'
                                  rw [_hqt2] at h
                                  exact etypRefLocsBounded_mono h
                                    (Nat.le_trans hmono_e1 hcursorLoc)),
                              varEnvClosuresCapturedRefLocsBounded_update
                                (varEnvClosuresCapturedRefLocsBounded_ofCaptured
                                  (CapturedEnvRefLocsFullBounded_mono
                                    (by rw [_hetyp1] at hClosRL; exact hClosRL _ _htcl_mem)
                                    hcursorLoc))
                                (by
                                  have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                                    ctx e2 fuelApp result2 hwf htc2'
                                  rw [_hqt2] at h
                                  exact etypClosuresCapturedRefLocsBounded_mono h
                                    (Nat.le_trans hmono_e1 hcursorLoc))⟩
                          have hbnd_bodyCtx : TagBoundedCtx bodyCtx := by
                            have hClosTag := typecheckExpr_preserves_qualType_closures_bounded
                              ctxFun e1 fuelApp result1 htc1' hbnd_ctxFun.2.1 hbnd_ctxFun.2.2
                            obtain ⟨htagE1, hpredE1, _hclosE1⟩ :=
                              typecheckExpr_preserves_TagBoundedCtx ctxFun e1 fuelApp result1 htc1' hbnd_ctxFun
                            have htc2'' : typecheck ctx e2 fuelApp = .ok result2 := by simpa [typecheck] using htc2
                            have hr2le : result2.nextTag' ≤ cursor.1 :=
                              Nat.le_trans
                                (by simpa [ctxFun] using typecheck_nextTag_mono ctxFun e1 fuelApp result1 htc1')
                                hcursorTag
                            have hQt2Pred :=
                              (typecheckExpr_preserves_predTagsBounded ctx e2 fuelApp result2 htc2'' hbnd.2.1 hbnd.2.2).2
                            have hQt2Clos := typecheckExpr_preserves_qualType_closures_bounded
                              ctx e2 fuelApp result2 htc2'' hbnd.2.1 hbnd.2.2
                            have htenv : CapturedEnvFullBounded tenv result1.nextTag' := by
                              rw [_hetyp1] at hClosTag; exact hClosTag _ _htcl_mem
                            refine ⟨tagEnvBounded_mono result1.tagEnv' result1.nextTag' cursor.1 htagE1 hcursorTag,
                              ⟨predTagsBoundedInVarEnv_update
                                (predTagsBoundedInVarEnv_ofCaptured
                                  (capturedPredTagsBounded_of_fullBounded
                                    (CapturedEnvFullBounded_mono htenv hcursorTag))) ?_,
                               predTagsBoundedInMemEnv_mono hpredE1.2 hcursorTag⟩,
                              varEnvClosuresCapturedBounded_update
                                (varEnvClosuresCapturedBounded_ofCaptured
                                  (CapturedEnvFullBounded_mono htenv hcursorTag)) ?_⟩
                            · have h := hQt2Pred; rw [_hqt2] at h; exact qtypPredTagBounded_mono h hr2le
                            · have h := hQt2Clos; rw [_hqt2] at h; exact etypClosuresFullBounded_mono h hr2le
                          rcases ih fuelBody (by omega) bodyCtx body result3
                              (by simpa [bodyCtx] using htcBody)
                              hwf_bodyCtx hbnd_bodyCtx
                              (by simp [bodyCtx, hpc, joinPoison]) l qt_src hlookup_result3
                              (by simpa [bodyCtx] using hpre_r1) with
                            ⟨_hpoison3, hguard3⟩
                          rcases hguard3 k htag_src hreg_result3 hnotfun_src with
                            ⟨qt_mid, hlookup_mid_body, htag_mid, hk_mid, hnotfun_mid⟩
                          exact
                            hbackToCtx_guard qt_mid k
                              (by simpa [bodyCtx] using hlookup_mid_body)
                              htag_mid
                              (by simpa [bodyCtx] using hk_mid)
                              hnotfun_mid
                      | extern id x retSpec effects capturedEnv declaredArgQt captures =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyFnTClosure (.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyFnTClosure
                            unfold applyFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          -- Structural backward trace: under `pc = true`,
                          -- `applyFnTClosure` (extern) cannot install a guard
                          -- tag (predicate erasure in `applyExternEffect`),
                          -- so the guard-tagged post-cell traces back to the
                          -- same `qt_src` in the pre-extern memEnv (rCursor's
                          -- memEnv = result1's memEnv).
                          have hlookup_rCursor : rCursor.memEnv'.lookup l = some qt_src :=
                            applyFnTClosure_extern_ok_memEnv_guard_origin
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor fuelApp id x retSpec effects
                              capturedEnv srcRes happly_old hpc l qt_src k hlookup_src htag_src
                          have hlookup_result1 : result1.memEnv'.lookup l = some qt_src := by
                            simpa [rCursor] using hlookup_rCursor
                          have hreg_result1 : result1.regime'.lookup? k = some true := by
                            have hreg_src' : srcRes.regime'.lookup? k = some true := by
                              simpa [ctxAfter] using hreg_src
                            have hmemBound :=
                              (typecheckExpr_preserves_predTagsBounded ctxFun e1 fuelApp result1
                                (by simpa [typecheck] using htc1) hbnd_ctxFun.2.1 hbnd_ctxFun.2.2).1
                            have hk_lt : k < cursor.1 :=
                              Nat.lt_of_lt_of_le
                                (qtypGuardTag_lt_of_predTagBounded (hmemBound l qt_src hlookup_result1) htag_src)
                                hcursorTag
                            have hback := applyFnTClosure_extern_regime_preserve_some_back
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor srcRes fuelApp id x retSpec effects
                              capturedEnv declaredArgQt happly_old k true hk_lt hreg_src'
                            simpa [rCursor] using hback
                          exact
                            hbackToCtx_guard qt_src k hlookup_result1 htag_src
                              hreg_result1 hnotfun_src
                    rcases joinTypeResults_mem_contains_head_or_rest
                        ctx first rest res h_join l hcontains_res with
                      hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                    · exact hmember_origin first (by simp) hhead
                    · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
                | inr hparrow =>
                    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, res, _hetyp1, _hp1,
                        _hnempty, _hsub, hmap, heq_results, h_join, rfl⟩ := hparrow
                    have hmember_origin :
                        ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                          ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
                            qtypGuardTag qt_in = some k ∧
                            ctx.regime.lookup? k = some true ∧
                            qt_in.etyp.isFunctionType = false := by
                      intro srcRes hsrc_mem hsrc_contains
                      have hsrc_results : srcRes ∈ results := by
                        simpa [heq_results] using hsrc_mem
                      rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
                          (applyOne := fun tcl cursor bn =>
                            applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                              ctx result1 cursor bn fuelApp)
                          (base := result1.nextTag')
                          (hmono := fun tcl cursor bn result hct happly =>
                            Nat.le_trans hct (applyPFnTClosureAtCursor_nextTag_advance tcl ctx
                              st1 st2 p p1 etyp2 p2 pred2 result1 result cursor bn fuelApp happly))
                          (hbase := Nat.le_refl _) hmap hsrc_results with
                        ⟨tcl, _htcl_mem, cursor, bn, hcursorTag, happly_src⟩
                      rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have htag_src : qtypGuardTag qt_src = some k :=
                        joinTypeResults_lookup_member_guardTag_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src k hlookup_res_ctx hlookup_src_ctx htag
                      have hreg_src : (ctxAfter ctx srcRes).regime.lookup? k = some true :=
                        joinTypeResults_lookup_member_regime_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem k true hk
                      have hetyp_eq : qt_out.etyp = qt_src.etyp :=
                        joinTypeResults_lookup_member_etyp_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hlookup_src_ctx
                      have hnotfun_src : qt_src.etyp.isFunctionType = false := by
                        simpa [hetyp_eq.symm] using hnotfun
                      cases tcl with
                      | regular x pbody tenv =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyPFnTClosure (.regular x pbody tenv) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyPFnTClosure
                            unfold applyPFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          have hcontains_result1 : result1.memEnv'.contains l := by
                            have hcontains_cursor : rCursor.memEnv'.contains l :=
                              applyPFnTClosure_mem_subset
                                (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                                (result2 := rCursor) (fuel := fuelApp)
                                (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                                happly_old l hsrc_contains
                            simpa [rCursor] using hcontains_cursor
                          rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_result1 with
                            ⟨qt_mid, hlookup_mid⟩
                          have hlookup_preserved :
                              srcRes.memEnv'.lookup l = some qt_mid := by
                            exact
                              applyPFnTClosure_preserves_memEnv_lookup
                                (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                                (result2 := rCursor) (fuel := fuelApp)
                                (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                                happly_old l qt_mid (by simpa [rCursor] using hlookup_mid)
                          have hqt_mid : qt_src = qt_mid := by
                            rw [hlookup_src] at hlookup_preserved
                            exact Option.some.inj hlookup_preserved
                          have hmono_src :
                              Regime.monotoneStepExt result1.regime' srcRes.regime' (fun j => cursor.1 ≤ j) := by
                            exact
                              applyPFnTClosure_regime_mono
                                (tcl := PFnTClosure.regular x pbody tenv)
                                (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                                (r1 := rCursor) (r2 := srcRes) (fuel := fuelApp)
                                (IH := fun m _hlt e ctx' res' htc' =>
                                  by
                                    simpa [typecheck, ctxAfter] using regime_monotoneExt ctx' e m res' htc')
                                happly_old
                          have hk_lt : k < cursor.1 := by
                            have hmemBound :=
                              (typecheckExpr_preserves_predTagsBounded ctxFun e1 fuelApp result1
                                (by simpa [typecheck] using htc1) hbnd_ctxFun.2.1 hbnd_ctxFun.2.2).1
                            exact Nat.lt_of_lt_of_le
                              (qtypGuardTag_lt_of_predTagBounded (hmemBound l qt_mid hlookup_mid)
                                (hqt_mid ▸ htag_src)) hcursorTag
                          have hreg_mid : result1.regime'.lookup? k = some true :=
                            Regime.monotoneStepExt_lookup_back hmono_src (Nat.not_le.2 hk_lt)
                              (by simpa [ctxAfter] using hreg_src)
                          have htag_mid : qtypGuardTag qt_mid = some k := by
                            simpa [hqt_mid] using htag_src
                          have hnotfun_mid : qt_mid.etyp.isFunctionType = false := by
                            simpa [hqt_mid] using hnotfun_src
                          exact hbackToCtx_guard qt_mid k hlookup_mid htag_mid hreg_mid hnotfun_mid
                      | extern id x retSpec capturedEnv declaredArgQt captures =>
                          let rCursor : TypeResult :=
                            { result1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn }
                          have happly_old :
                              applyPFnTClosure (.extern id x retSpec capturedEnv declaredArgQt captures) st1 st2 p p1
                                etyp2 p2 pred2 ctx rCursor fuelApp = .ok srcRes := by
                            unfold applyPFnTClosure
                            unfold applyPFnTClosureAtCursor at happly_src
                            simpa [rCursor] using happly_src
                          have hmem_eq := applyPFnTClosure_extern_memEnv_eq
                            ctx st1 st2 p p1 etyp2 p2 pred2 rCursor srcRes fuelApp
                            id x retSpec capturedEnv declaredArgQt happly_old
                          have hlookup_mid : result1.memEnv'.lookup l = some qt_src := by
                            have hlookup_cursor : rCursor.memEnv'.lookup l = some qt_src := by
                              rw [← hmem_eq]; exact hlookup_src
                            simpa [rCursor] using hlookup_cursor
                          have hreg_mid : result1.regime'.lookup? k = some true := by
                            have hreg_src' : srcRes.regime'.lookup? k = some true := by
                              simpa [ctxAfter] using hreg_src
                            have hmemBound :=
                              (typecheckExpr_preserves_predTagsBounded ctxFun e1 fuelApp result1
                                (by simpa [typecheck] using htc1) hbnd_ctxFun.2.1 hbnd_ctxFun.2.2).1
                            have hk_lt : k < cursor.1 :=
                              Nat.lt_of_lt_of_le
                                (qtypGuardTag_lt_of_predTagBounded (hmemBound l qt_src hlookup_mid) htag_src)
                                hcursorTag
                            have hback := applyPFnTClosure_extern_regime_preserve_some_back
                              ctx st1 st2 p p1 etyp2 p2 pred2 rCursor srcRes fuelApp id x retSpec
                              capturedEnv declaredArgQt happly_old k true hk_lt hreg_src'
                            simpa [rCursor] using hback
                          exact hbackToCtx_guard qt_src k hlookup_mid htag_src hreg_mid hnotfun_src
                    rcases joinTypeResults_mem_contains_head_or_rest
                        ctx first rest res h_join l hcontains_res with
                      hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                    · exact hmember_origin first (by simp) hhead
                    · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
      | externVal _id typ poison pred =>
          have htc' : typecheckExternVal ctx _id typ poison pred fuel' = .ok res := by
            simpa [typecheckExpr, typecheck] using htc
          exact typecheckExternVal_preserves_lookup_origin ctx _id typ poison pred fuel' res htc' hwf
            hbnd hpc
            l qt_out hpre hlookup_out
      | externRef id refPoison refPred cellPoison cellPred =>
          simp only [typecheckExpr, typecheckExternRef] at htc
          simp [bind, Except.bind, pure, Except.pure] at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          split at htc <;> simp (config := { failIfUnchanged := false }) at htc
          cases htc
          have hfresh : ¬ctx.memEnv.contains ctx.nextLoc := by
            intro h; exact Nat.lt_irrefl ctx.nextLoc (hwf.1 ctx.nextLoc h)
          have hlne : l ≠ ctx.nextLoc := fun heq => hfresh (heq ▸ hpre)
          rw [MemoryTypeEnv_lookup_updateMemEnv_ne hlne] at hlookup_out
          exact ⟨fun hp => ⟨qt_out, hlookup_out, hp⟩,
                 fun k hg hr hfn => ⟨qt_out, hlookup_out, hg, hr, hfn⟩⟩
      | externFn id arg argTyp argPoison argPred retSpec effects cap =>
          unfold typecheckExpr at htc
          obtain ⟨argQt, _, htc_res⟩ :=
            typecheckExternFn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec effects res htc
          subst htc_res
          exact ⟨fun hp => ⟨qt_out, hlookup_out, hp⟩,
                 fun k hg hr hfn => ⟨qt_out, hlookup_out, hg, hr, hfn⟩⟩
      | externPfn id arg argTyp argPoison argPred retSpec cap =>
          unfold typecheckExpr at htc
          obtain ⟨argQt, _, htc_res⟩ :=
            typecheckExternPfn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec res htc
          subst htc_res
          exact ⟨fun hp => ⟨qt_out, hlookup_out, hp⟩,
                 fun k hg hr hfn => ⟨qt_out, hlookup_out, hg, hr, hfn⟩⟩

private lemma typecheckExpr_lookup_poison_origin_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr ctx e fuel = .ok res)
  (hwf : wfTypeContext ctx)
  (hbnd : TagBoundedCtx ctx)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp),
    res.memEnv'.lookup l = some qt_out →
    ctx.memEnv.contains l →
    qt_out.poison = false →
    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qt_in.poison = false := by
  intro l qt_out hlookup_out hpre hpoison_out
  exact (typecheckExpr_lookup_origin_of_pc_true_split
      (ctx := ctx) (e := e) (fuel := fuel) (res := res) htc hwf hbnd hpc l qt_out hlookup_out hpre).1 hpoison_out

private lemma typecheckExpr_lookup_guard_origin_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr ctx e fuel = .ok res)
  (hwf : wfTypeContext ctx)
  (hbnd : TagBoundedCtx ctx)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp) (k : Tag),
    res.memEnv'.lookup l = some qt_out →
    ctx.memEnv.contains l →
    qtypGuardTag qt_out = some k →
    res.regime'.lookup? k = some true →
    qt_out.etyp.isFunctionType = false →
    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧
      qtypGuardTag qt_in = some k ∧
      ctx.regime.lookup? k = some true ∧
      qt_in.etyp.isFunctionType = false := by
  intro l qt_out k hlookup_out hpre htag hk hnotfun
  exact (typecheckExpr_lookup_origin_of_pc_true_split
      (ctx := ctx) (e := e) (fuel := fuel) (res := res) htc hwf hbnd hpc l qt_out hlookup_out hpre).2
      k htag hk hnotfun

lemma typecheckExpr_clean_lookup_origin_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr ctx e fuel = .ok res)
  (hwf : wfTypeContext ctx)
  (hbnd : TagBoundedCtx ctx)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp),
    res.memEnv'.lookup l = some qt_out →
    ctx.memEnv.contains l →
    qtypCleanUnder res.regime' qt_out →
    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
  intro l qt_out hlookup_out hpre hclean_out
  cases hclean_out with
  | clean hpoison_out =>
      rcases typecheckExpr_lookup_poison_origin_of_pc_true
          (ctx := ctx) (e := e) (fuel := fuel) (res := res)
          htc hwf hbnd hpc l qt_out hlookup_out hpre hpoison_out with
        ⟨qt_in, hlookup_in, hpoison_in⟩
      exact ⟨qt_in, hlookup_in, qtypCleanUnder.clean hpoison_in⟩
  | guard k htag hk hnotfun =>
      rcases typecheckExpr_lookup_guard_origin_of_pc_true
          (ctx := ctx) (e := e) (fuel := fuel) (res := res)
          htc hwf hbnd hpc l qt_out k hlookup_out hpre htag hk hnotfun with
        ⟨qt_in, hlookup_in, htag_in, hk_in, hnotfun_in⟩
      exact ⟨qt_in, hlookup_in, qtypCleanUnder.guard k htag_in hk_in hnotfun_in⟩

end TypecheckInductionSig
