/-
  FaultRobustnessProofs.lean - Fault-robustness case proofs and step theorem.

  Contains stepFR_* case lemmas (literal, var, op, unaryop, newRef, seq, vlet,
  fn, pfn, ite, assign, deref, kwhile), the step-level IOFree theorem, and
  final fault-robustness bridges.

  Shared infrastructure is in StepFR.lean.
  The stepFR_app case is in StepFRApp.lean.
  The stepFR_assign case is in StepFRAssign.lean.
-/
import LeanProofs.StepFR
import LeanProofs.StepFRApp
import LeanProofs.StepFRAssign

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

private lemma stepFR_literal
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hvtyp : ∀ θ, valueHasETyp θ v res.qualType.etyp)
  (hpoison : res.qualType.poison = false)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls)
  (hpredNo : res.qualType.pred = Predicate.noPred)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFR mode ctx e res predSat tm := by
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma for literals
  have ⟨hcf₀, ho₀⟩ := terminatesTo_literal_inv' mode e v hval
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_literal_inv' mode e v hval
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  -- StepFR existential has structure:
  -- ∃ θ₀' θ₁', wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
  --   valueHasETyp θ₀' o₀ res.qualType.etyp ∧ valueHasETyp θ₁' o₁ res.qualType.etyp ∧
  --   wfTagMeaningCtx ... ∧ wfTypeContext (ctxAfter ctx res) ∧ wfConfig cf₀ ∧ wfConfig cf₁ ∧
  --   runtimeInstantiatesCtx ... ∧ runtimeInstantiatesCtx ... ∧
  --   regimeConsistentWithCtx ... ∧ consistentWithRegime ... ∧ consistentWithRegime ... ∧
  --   agreeOnClean ... ∧ valueConsistentWithRegime ... ∧ valueConsistentWithRegime ... ∧ resultAgreesIfClean ...
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- valueHasETyp θ₀ o₀ res.qualType.etyp
    simp [ho₀]; exact hvtyp θ₀
  · -- valueHasETyp θ₁ o₁ res.qualType.etyp
    simp [ho₁]; exact hvtyp θ₁
  · -- wfTagMeaningCtx tm (ctxAfter ctx res)
    simpa [hctxAfter] using hwfTm
  · -- wfTypeContext (ctxAfter ctx res)
    simpa [hctxAfter] using hwf
  · -- runtimeInstantiatesCtx for θ₀' (literal doesn't change context, configs unchanged)
    simpa [hctxAfter] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [hctxAfter] using hric₁
  · -- regimeConsistentWithCtx (literal doesn't change context)
    simpa [hctxAfter] using hreg
  · -- consistentWithRegime for run 0
    simpa [hctxAfter] using hcwr₀
  · -- consistentWithRegime for run 1
    simpa [hctxAfter] using hcwr₁
  · -- agreeOnClean for updated context (literal doesn't change context)
    simpa [hctxAfter] using hagree
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpredNo])
      (ho₀ ▸ closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hvtyp θ₀) hnotfun)
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpredNo])
      (ho₁ ▸ closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hvtyp θ₁) hnotfun)
  · -- resultAgreesIfClean
    intro _hclean
    have hval' : o₀ = o₁ := by
      simp [ho₀, ho₁]
    exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref hval'

private lemma stepFRSingleRunFinalCleanPcTrue_literal
  (mode : LeanPoison.EvalMode)
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (res : TypeResult) (v : Value)
  (hval : Expr.toValue? e = some v)
  (hvtyp : ∀ θ, valueHasETyp θ v res.qualType.etyp)
  (hnotfun : res.qualType.etyp.isFunctionType = false)
  (hpredNo : res.qualType.pred = Predicate.noPred)
  (hctxAfter : ctxAfter ctx res = ctx) :
  StepFRSingleRunFinalCleanPcTrue mode ctx e res predSat tm := by
  intro _hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg _hRbound hcwr a pm hwfcfg ht _hpc
  have ⟨hcf, ho⟩ := terminatesTo_literal_inv' mode e v hval
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  subst hcf
  have hvalc : valueConsistentWithRegime predSat ctx.regime res.qualType μ θ o := by
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpredNo])
      (ho ▸ closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hvtyp θ) hnotfun)
  exact
    singleRunFinalCleanWitness_of_same_state
      (ctx := ctx) (res := res) (predSat := predSat) (tm := tm)
      (μ := μ) (ρ := ρ) (θ := θ) (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
      (o := o) (a := a) (pm := pm)
      hctxAfter rfl (ho ▸ hvtyp θ) hvalc hwfTm hwf hric hreg hcwr hwfcfg

private lemma typecheckAssign_lookup_clean_back_to_result1_of_pc_true
  (ctx : TypeContext) (e2 : Expr) (fuel : Nat)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (htc2 : typecheckExpr .ioFree (updateCtxFromResult ctx result1) e2 fuel = .ok result2)
  (hInt : result2.qualType.etyp = ETyp.int)
  (h_mem :
    res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
  (h_regime : res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls)
  (hpc : ctx.pc = true) :
  ∀ l qt_mid qt_out,
    result1.memEnv'.lookup l = some qt_mid →
    res.memEnv'.lookup l = some qt_out →
    qtypCleanUnder res.regime' qt_out →
    qtypCleanUnder result1.regime' qt_mid := by
  intro l qt_mid qt_out hlookup_mid hlookup_out hclean_out
  rcases
    typecheckAssign_result2_lookup_clean_back_of_pc_true
      (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      hInt h_mem h_regime hpc l qt_out hlookup_out hclean_out
    with ⟨qt₂, hlookup₂, hclean₂⟩
  have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
    simpa [updateCtxFromResult] using hpc
  exact
    typecheckExpr_lookup_clean_back_of_pc_true
      (ctx := updateCtxFromResult ctx result1) (e := e2) (fuel := fuel) (res := result2)
      htc2 hpc2 l qt_mid qt₂
      (by simpa [updateCtxFromResult] using hlookup_mid)
      hlookup₂
      hclean₂

private lemma assign_preservesInheritedFinalCleanLocsOneRun_pc_true
  (ctx : TypeContext) (e2 : Expr) (fuel : Nat)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (μ : Memory) (cfg1 cfg2 : Config) (θ θ1 θ2 : RealizationMap)
  (a_w : Address) (n : Int)
  (htc2 : typecheckExpr .ioFree (updateCtxFromResult ctx result1) e2 fuel = .ok result2)
  (hRef : result1.qualType.etyp = ETyp.ref ls)
  (hInt : result2.qualType.etyp = ETyp.int)
  (h_mem :
    res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
  (h_regime : res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls)
  (hpc : ctx.pc = true)
  (hθ2wf : wfRealizationMap θ2)
  (hvalRef2 : valueHasETyp θ2 (Value.loc a_w) result1.qualType.etyp)
  (hric2 : runtimeInstantiatesCtx (ctxAfter (updateCtxFromResult ctx result1) result2) cfg2.memory cfg2.varEnv θ2)
  (hpres1 : PreservesInheritedFinalCleanLocsOneRun ctx result1 μ cfg1.memory θ θ1)
  (hpres2 : PreservesInheritedFinalCleanLocsOneRun (updateCtxFromResult ctx result1) result2 cfg1.memory cfg2.memory θ1 θ2) :
  PreservesInheritedFinalCleanLocsOneRun
    ctx res μ (Std.ExtTreeMap.insert cfg2.memory a_w n) θ θ2 := by
  have hpres_to_result2 :
      PreservesInheritedFinalCleanLocsOneRun ctx result2 μ cfg2.memory θ θ2 := by
    refine
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctx) (res1 := result1) (res2 := result2)
        ?_ hpres1 ?_
    · intro l qt_in qt_out hlookup_in hlookup_out hclean_out
      have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
        simpa [updateCtxFromResult] using hpc
      rcases
        typecheckExpr_clean_lookup_origin_of_pc_true
          (ctx := updateCtxFromResult ctx result1) (e := e2) (fuel := fuel) (res := result2)
          htc2 hpc2 l qt_out hlookup_out hclean_out
        with ⟨qt_mid, hlookup_mid, hclean_mid⟩
      exact ⟨qt_mid, by simpa [updateCtxFromResult] using hlookup_mid, by simpa [updateCtxFromResult] using hclean_mid⟩
    · simpa [ctxAfter, updateCtxFromResult] using hpres2
  have hpres_write :
      PreservesInheritedFinalCleanLocsOneRun
        (ctxAfter ctx result2) res
        cfg2.memory (Std.ExtTreeMap.insert cfg2.memory a_w n) θ2 θ2 := by
    simpa [ctxAfter, updateCtxFromResult] using
      assign_write_step_preserves_inherited_final_clean_pc_true
        (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
        (cfg2 := cfg2) (θ := θ2) (a_w := a_w) (n := n)
        hRef hvalRef2 hθ2wf hric2 h_mem hpc
  refine
    PreservesInheritedFinalCleanLocsOneRun.compose
      (ctx := ctx) (res1 := result2) (res2 := res)
      ?_ hpres_to_result2 hpres_write
  intro l qt_in qt_out _hlookup_in hlookup_out hclean_out
  exact
    typecheckAssign_result2_lookup_clean_back_of_pc_true
      (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      hInt h_mem h_regime hpc l qt_out hlookup_out hclean_out

private lemma not_qtypCleanUnder_of_poison_true_noPred
  {R : Regime} {qt : QTyp}
  (hpoison : qt.poison = true)
  (hpred : qt.pred = Predicate.noPred) :
  ¬ qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison' =>
      simp [hpoison] at hpoison'
  | guard k htag _ _ =>
      simp [qtypGuardTag, hpred] at htag

private lemma list_fold_joinPredicates_init_noPred
  (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) :
  ((xs.foldl
      (fun acc l0 =>
        match env[l0]? with
        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
        | none => acc)
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

private lemma assign_lookup_not_clean_of_pc_true_of_mem
    (ctx : TypeContext) (result1 result2 res : TypeResult) (ls : LocSet)
    (h_mem :
      res.memEnv' =
        match Std.ExtTreeSet.toList ls with
        | [l] =>
            updateMemEnv result2.memEnv' l
              { etyp := ETyp.int
                poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
        | _ =>
            updateLocsetWeak result2.memEnv' ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
              (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
    (hpc : ctx.pc = true)
    {l : Loc} {qt_out : QTyp}
    (hIn : l ∈ ls)
    (hlookup_out : res.memEnv'.lookup l = some qt_out) :
    ¬ qtypCleanUnder res.regime' qt_out := by
  intro hclean_out
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
    simpa [h_mem] using hlookup_out
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
                  pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x =
              some qt_out := by
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
          exact (not_qtypCleanUnder_of_poison_true_noPred rfl rfl) hclean_out
      | cons y ys =>
          have hlookup_weak :
              (updateLocsetWeak result2.memEnv' ls
                (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l =
              some qt_out := by
            simpa [hls] using hlookup_formula
          unfold updateLocsetWeak at hlookup_weak
          set joined :=
            LocSet.fold ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison),
                if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
              (fun (accP, accPred) l0 =>
                match result2.memEnv'.get? l0 with
                | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                | none => (accP, accPred)) with hjoined
          set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
          dsimp at hlookup_weak
          unfold LocSet.fold at hlookup_weak
          rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
          have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
          have hlookup_final :
              (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l =
              some finalQt :=
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
            simpa using
              list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
          have hpred : finalQt.pred = Predicate.noPred := by
            simp [finalQt, joined, hpc]
            unfold LocSet.fold
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
            simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
          exact (not_qtypCleanUnder_of_poison_true_noPred hpoison hpred) hclean_out

private lemma assign_updated_lookup_shape_of_pc_true
    (ctx : TypeContext) (result1 result2 res : TypeResult) (ls : LocSet)
    (h_mem :
      res.memEnv' =
        match Std.ExtTreeSet.toList ls with
        | [l] =>
            updateMemEnv result2.memEnv' l
              { etyp := ETyp.int
                poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
        | _ =>
            updateLocsetWeak result2.memEnv' ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
              (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
    (hpc : ctx.pc = true)
    {l : Loc} {qt_out : QTyp}
    (hIn : l ∈ ls)
    (hlookup_out : res.memEnv'.lookup l = some qt_out) :
    qt_out.poison = true ∧ qt_out.pred = Predicate.noPred := by
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
    simpa [h_mem] using hlookup_out
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
                  pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }).lookup x =
              some qt_out := by
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
          exact ⟨rfl, rfl⟩
      | cons y ys =>
          have hlookup_weak :
              (updateLocsetWeak result2.memEnv' ls
                (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).lookup l =
              some qt_out := by
            simpa [hls] using hlookup_formula
          unfold updateLocsetWeak at hlookup_weak
          set joined :=
            LocSet.fold ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison),
                if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
              (fun (accP, accPred) l0 =>
                match result2.memEnv'.get? l0 with
                | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                | none => (accP, accPred)) with hjoined
          set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
          dsimp at hlookup_weak
          unfold LocSet.fold at hlookup_weak
          rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlookup_weak
          have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hIn
          have hlookup_final :
              (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l =
              some finalQt :=
            list_fold_updateMemEnv_lookup_eq_of_mem ls.toList result2.memEnv' l finalQt hInList rfl
          have hqt : qt_out = finalQt := by
            exact Option.some.inj <| by
              calc
                some qt_out =
                    (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) result2.memEnv').lookup l := by
                      symm
                      exact hlookup_weak
                _ = some finalQt := hlookup_final
          subst hqt
          have hpoison : finalQt.poison = true := by
            simp [finalQt, joined, hpc]
            unfold LocSet.fold
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
            simpa using
              list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
          have hpred : finalQt.pred = Predicate.noPred := by
            simp [finalQt, joined, hpc]
            unfold LocSet.fold
            rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
            simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
          exact ⟨hpoison, hpred⟩

private lemma assign_final_clean_preservation
  (ctx : TypeContext) (e2 : Expr) (fuel' : Nat)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (μ : Memory) (cfg1 cfg2 cf : Config)
  (θ θ1 θ2 : RealizationMap)
  (aw : Address) (n : Int)
  (hRef : result1.qualType.etyp = ETyp.ref ls)
  (hInt : result2.qualType.etyp = ETyp.int)
  (htc2_expr : typecheckExpr .ioFree (ctxAfter ctx result1) e2 fuel' = .ok result2)
  (hmem_res :
    res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
  (hRegime : res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls)
  (hpc : ctx.pc = true)
  (hvloc1 : valueHasETyp θ1 (Value.loc aw) result1.qualType.etyp)
  (hθext2 : wfExtendsMap θ1 θ2)
  (hθ2wf : wfRealizationMap θ2)
  (hric2 : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ2)
  (hmem : cf.memory = Std.ExtTreeMap.insert cfg2.memory aw n)
  (hpres1 : PreservesInheritedFinalCleanLocsOneRun ctx result1 μ cfg1.memory θ θ1)
  (hpres2 : PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx result1) result2 cfg1.memory cfg2.memory θ1 θ2) :
  PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
  refine ⟨?_⟩
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  have hnotin : l ∉ ls := by
    intro hIn
    exact
      (assign_lookup_not_clean_of_pc_true_of_mem
        (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
        hmem_res hpc hIn hlookup_out) hclean_out
  rcases
    typecheckAssign_result2_lookup_clean_back_of_pc_true
      (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      hInt hmem_res hRegime hpc l qt_out hlookup_out hclean_out
    with ⟨qt_mid, hlookup_mid, hclean_mid⟩
  have hpc_mid : (ctxAfter ctx result1).pc = true := by
    simpa [ctxAfter] using hpc
  rcases
    typecheckExpr_clean_lookup_origin_of_pc_true
      (ctx := ctxAfter ctx result1) (e := e2) (fuel := fuel') (res := result2)
      htc2_expr hpc_mid l qt_mid hlookup_mid hclean_mid
    with ⟨qt_pre, hlookup_pre_ctx, hclean_pre⟩
  have hpres_l1 :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctx) (res := result1) (μ_in := μ) (μ_out := cfg1.memory)
      (θ_in := θ) (θ_out := θ1) hpres1
      hlookup_in (by simpa [ctxAfter] using hlookup_pre_ctx) hclean_pre
  have hpres_l2 :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctxAfter ctx result1) (res := result2)
      (μ_in := cfg1.memory) (μ_out := cfg2.memory)
      (θ_in := θ1) (θ_out := θ2) hpres2
      hlookup_pre_ctx hlookup_mid hclean_mid
  have hpres_mid :
      PreservesInheritedCleanLocOneRun μ cfg2.memory θ θ2 l :=
    PreservesInheritedCleanLocOneRun.trans hpres_l1 hpres_l2
  have hvloc2 : valueHasETyp θ2 (Value.loc aw) result1.qualType.etyp := by
    exact valueHasETyp_extends hθext2.1 hvloc1
  have hwrite_pres :
      PreservesInheritedFinalCleanLocsOneRun
        (ctxAfter (updateCtxFromResult ctx result1) result2) res
        cfg2.memory cf.memory θ2 θ2 := by
    simpa [ctxAfter, updateCtxFromResult, hmem] using
      assign_write_step_preserves_inherited_final_clean_pc_true
        (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
        (cfg2 := cfg2) (θ := θ2) (a_w := aw) (n := n)
        hRef hvloc2 hθ2wf hric2 hmem_res hpc
  have hpres_write :=
    PreservesInheritedFinalCleanLocsOneRun.apply
      (ctx := ctxAfter (updateCtxFromResult ctx result1) result2) (res := res)
      (μ_in := cfg2.memory) (μ_out := cf.memory)
      (θ_in := θ2) (θ_out := θ2) hwrite_pres
      (by simpa [ctxAfter, updateCtxFromResult] using hlookup_mid)
      hlookup_out hclean_out
  exact PreservesInheritedCleanLocOneRun.trans hpres_mid hpres_write

private lemma assign_single_run_post_transport_pc_true
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (result1 result2 res : TypeResult) (ls : LocSet)
  (cfg2 cf : Config) (θ : RealizationMap) (a_w : Address) (n : Int)
  (hpredlaws : PredSatLaws predSat tm)
  (hwfTm2 : wfTagMeaningCtx tm (ctxAfter (ctxAfter ctx result1) result2))
  (hwf2 : wfTypeContext (ctxAfter (ctxAfter ctx result1) result2))
  (hric2 : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx result1) result2) cfg2.memory cfg2.varEnv θ)
  (hreg2 : regimeConsistentWithCtx (ctxAfter (ctxAfter ctx result1) result2))
  (hcwr2 :
    consistentWithRegime predSat
      (ctxAfter (ctxAfter ctx result1) result2).regime
      (ctxAfter (ctxAfter ctx result1) result2)
      cfg2.memory cfg2.varEnv θ)
  (hRef : result1.qualType.etyp = ETyp.ref ls)
  (hvalRef : valueHasETyp θ (Value.loc a_w) result1.qualType.etyp)
  (hθwf : wfRealizationMap θ)
  (hmem : cf.memory = Std.ExtTreeMap.insert cfg2.memory a_w n)
  (hvar : cf.varEnv = cfg2.varEnv)
  (hNextLoc : res.nextLoc' = ls.fold result2.nextLoc' (fun acc l => max acc (l + 1)))
  (hNextTag : res.nextTag' = result2.nextTag')
  (hRegime : res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls)
  (hmem_res :
    res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred))
  (htag_res : res.tagEnv' = invalidateTagDeps result2.tagEnv' ls)
  (hpc : ctx.pc = true) :
  wfTagMeaningCtx tm (ctxAfter ctx res) ∧
  wfTypeContext (ctxAfter ctx res) ∧
  runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ ∧
  regimeConsistentWithCtx (ctxAfter ctx res) ∧
  consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) cf.memory cf.varEnv θ := by
  rcases valueHasETyp_loc_inv hvalRef with ⟨ls', lw, hRef', hwrite, hlwIn'⟩
  have hls : ls' = ls := by
    rw [hRef] at hRef'
    cases hRef'
    rfl
  have hlwIn : lw ∈ ls := by
    simpa [hls] using hlwIn'
  have hstored_pred_respects : PredRespectsTagMeaning tm Predicate.noPred := by
    intro k arg_name pred_body var_env hpred
    simp at hpred
  have hstored_qtyp :
      QTypRespectsTagMeaning tm
        { etyp := ETyp.int
          poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
          pred := Predicate.noPred } := by
    exact
      QTypRespectsTagMeaning_int_of_predRespects
        tm
        (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
        Predicate.noPred
        hstored_pred_respects
  have hEnvTm_res2 : EnvRespectsTagMeaning tm ctx.varEnv result2.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using hwfTm2
  have hPredSat_mem :
      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
    intro k μ μ' v
    exact predSat_mem_noPred_compat hpredlaws θ k μ μ' v
  have hqtypPredHolds_mem :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg2.memory v ↔
          qtypPredHolds predSat qt cf.memory v := by
    intro qt v
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ cfg2.memory cf.memory qt v
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hEnvTm_res : EnvRespectsTagMeaning tm ctx.varEnv res.memEnv' := by
      rw [hmem_res]
      cases hlsToList : Std.ExtTreeSet.toList ls with
      | nil =>
          simpa [hlsToList, hpc] using
            (EnvRespectsTagMeaning_updateLocsetWeak
              tm ctx.varEnv result2.memEnv' ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
              Predicate.noPred
              hEnvTm_res2
              hstored_pred_respects)
      | cons x xs =>
          cases xs with
          | nil =>
              simpa [hlsToList, hpc] using
                (EnvRespectsTagMeaning_updateMemEnv
                  tm ctx.varEnv result2.memEnv' x
                  { etyp := ETyp.int
                    poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                    pred := Predicate.noPred }
                  (by simp)
                  hEnvTm_res2 hstored_qtyp)
          | cons y ys =>
              simpa [hlsToList, hpc] using
                (EnvRespectsTagMeaning_updateLocsetWeak
                  tm ctx.varEnv result2.memEnv' ls
                  (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                  Predicate.noPred
                  hEnvTm_res2
                  hstored_pred_respects)
    exact wfTagMeaningCtx_ctxAfter tm ctx res hEnvTm_res
  · intro l hcontains
    have hcontains' : res.memEnv'.contains l = true := by
      simpa [ctxAfter] using hcontains
    have hsplit : result2.memEnv'.contains l = true ∨ l ∈ ls := by
      rw [hmem_res] at hcontains'
      exact
        assign_memEnv_formula_contains_eq_or_mem
          result2.memEnv' ls
          (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
          (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
          l hcontains'
    cases hsplit with
    | inl hOld =>
        have hOldCtx :
            (ctxAfter (ctxAfter ctx result1) result2).memEnv.contains l := by
          simpa [ctxAfter] using hOld
        have hltOld' : l < (ctxAfter (ctxAfter ctx result1) result2).nextLoc := by
          exact hwf2 l hOldCtx
        have hltOld : l < result2.nextLoc' := by
          simpa [ctxAfter] using hltOld'
        have hbase : result2.nextLoc' ≤ res.nextLoc' := by
          rw [hNextLoc]
          unfold LocSet.fold
          rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
          exact list_fold_max_ge_init ls.toList result2.nextLoc'
        exact Nat.lt_of_lt_of_le hltOld hbase
    | inr hIn =>
        have hle : l + 1 ≤ res.nextLoc' := by
          rw [hNextLoc]
          exact locset_fold_max_succ_ge_of_mem ls result2.nextLoc' l hIn
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self l) hle
  · unfold runtimeInstantiatesCtx at hric2 ⊢
    rcases hric2 with ⟨hmem₂, hvars₂⟩
    constructor
    · intro l a hlookup
      have hmem_old := hmem₂ l a hlookup
      constructor
      · have h_old_contains : result2.memEnv'.contains l = true := by
          simpa [ctxAfter] using hmem_old.1
        have h_new_contains : res.memEnv'.contains l = true := by
          rw [hmem_res]
          exact
            assign_memEnv_formula_contains_of_contains
              result2.memEnv' ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
              (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
              l h_old_contains
        simpa [ctxAfter] using h_new_contains
      · have hμ_old : cfg2.memory.contains a = true := by
          simpa using hmem_old.2
        have hμ_new : cf.memory.contains a = true := by
          rw [hmem, Std.ExtTreeMap.contains_insert]
          simp [hμ_old]
        simpa using hμ_new
    · intro x qt hlookup
      have hlookup_ctx2 :
          (ctxAfter (ctxAfter ctx result1) result2).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₂ hlookup_ctx2
      refine ⟨v, ?_, hvtyp⟩
      simpa [hvar] using hvlookup
  · unfold regimeConsistentWithCtx at hreg2 ⊢
    constructor
    · have htag_res2_R2 : tagEnvConsistentWithRegime result2.tagEnv' result2.regime' := by
        simpa [ctxAfter] using hreg2.1
      have htag_inv :
          tagEnvConsistentWithRegime (invalidateTagDeps result2.tagEnv' ls)
            (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
        tagEnvConsistentWithRegime_invalidateRegimeDeps result2.tagEnv' result2.regime' ls htag_res2_R2
      simpa [ctxAfter, htag_res, hRegime] using htag_inv
    · have hbound2 : result2.regime'.bound ≤ result2.nextTag' := by
        simpa [ctxAfter] using hreg2.2
      have hbound_res2 : (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).bound ≤ result2.nextTag' := by
        simpa [invalidateRegimeDeps] using hbound2
      simpa [ctxAfter, hRegime, hNextTag] using hbound_res2
  · unfold consistentWithRegime
    constructor
    · intro l qt k hlookup hguard hkR
      have hlookup_res : res.memEnv'.lookup l = some qt := by
        simpa [ctxAfter] using hlookup
      have hcontains_res : res.memEnv'.contains l = true := by
        exact (Std.ExtTreeMap.contains_iff_mem).2 <|
          memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
      have hcontains_formula :
          (match Std.ExtTreeSet.toList ls with
            | [l0] =>
                updateMemEnv result2.memEnv' l0
                  { etyp := ETyp.int
                    poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                    pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
            | _ =>
                updateLocsetWeak result2.memEnv' ls
                  (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                  (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)).contains l = true := by
        simpa [hmem_res] using hcontains_res
      have hsplit : result2.memEnv'.contains l = true ∨ l ∈ ls := by
        exact
          assign_memEnv_formula_contains_eq_or_mem
            result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
            l hcontains_formula
      cases hsplit with
      | inl hOld =>
          by_cases hIn : l ∈ ls
          · have ⟨_hpoison, hpred_out⟩ :=
              assign_updated_lookup_shape_of_pc_true
                (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
                hmem_res hpc hIn hlookup_res
            simp [qtypGuardTag, hpred_out] at hguard
          · have hlookup_ctx2 :
              (ctxAfter (ctxAfter ctx result1) result2).memEnv.lookup l = some qt := by
              have hlookup_result2 : result2.memEnv'.lookup l = some qt := by
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
                    some qt := by
                  simpa [hmem_res] using hlookup_res
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
                rwa [hlookup_eq] at hlookup_formula
              simpa [ctxAfter] using hlookup_result2
            have hkR_result2 : result2.regime'.lookup? k ≠ none := by
              have hkR_inv :
                  (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k ≠ none := by
                simpa [ctxAfter, hRegime] using hkR
              exact
                invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
                  result2.regime' result2.tagEnv' ls k hkR_inv
            have hloc := hcwr2.1 l qt k hlookup_ctx2 hguard hkR_result2
            cases hloc with
            | noPred_ok hnp =>
                simp [hnp] at hguard
            | guardOnly_ok k' hgo =>
                exact locsRegime.guardOnly_ok (l, qt) k' hgo
            | withPred_ok k' arg_name pred_body var_env a n_old b hclos hreg hreal hmem_old hcons =>
                have hk_eq : k' = k := by
                  have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                    simpa using hclos
                  have hguard' : qtypGuardTag qt = some k' := by
                    simp [qtypGuardTag, hclos']
                  have : some k' = some k := by
                    calc
                      some k' = qtypGuardTag qt := by symm; exact hguard'
                      _ = some k := hguard
                  exact Option.some.inj this
                have hkR_inv :
                    (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k ≠ none := by
                  simpa [ctxAfter, hRegime] using hkR
                have hkeep : (invalidateTagDeps result2.tagEnv' ls).contains k = true :=
                  invalidateRegimeDeps_survives_of_lookup_ne_none result2.regime' result2.tagEnv' ls k hkR_inv
                have hlookup_eq :
                    (ctxAfter ctx res).regime.lookup? k = result2.regime'.lookup? k := by
                  simpa [ctxAfter, hRegime] using
                    invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag result2.regime' result2.tagEnv' ls k hkeep
                have hreg_result2 : result2.regime'.lookup? k = some b := by
                  simpa [ctxAfter, hk_eq] using hreg
                have hregR : (ctxAfter ctx res).regime.lookup? k' = some b := by
                  calc
                    (ctxAfter ctx res).regime.lookup? k' = (ctxAfter ctx res).regime.lookup? k := by
                      simp [hk_eq]
                    _ = result2.regime'.lookup? k := hlookup_eq
                    _ = some b := hreg_result2
                have hmem_final : cf.memory.lookup a = some n_old := by
                  have ha_ne : a ≠ a_w := by
                    intro ha
                    have hlookup_lw : θ.lookup lw = some a := by
                      simpa [ha] using hwrite
                    have hl_eq : l = lw := hθwf _ _ _ hreal hlookup_lw
                    exact hIn (by simpa [hl_eq] using hlwIn)
                  have hcmp : compare a_w a ≠ Ordering.eq := by
                    intro hce
                    exact ha_ne ((Nat.compare_eq_eq).1 hce).symm
                  simpa [hmem, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hmem_old
                have hcons_final :
                    (b = true → qtypPredHolds predSat qt cf.memory (Value.num n_old)) ∧
                    (b = false → ¬ qtypPredHolds predSat qt cf.memory (Value.num n_old)) := by
                  constructor
                  · intro hbtrue
                    exact (hqtypPredHolds_mem qt (Value.num n_old)).1 (hcons.1 hbtrue)
                  · intro hbfalse hholds_new
                    exact (hcons.2 hbfalse) ((hqtypPredHolds_mem qt (Value.num n_old)).2 hholds_new)
                exact
                  locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n_old b
                    hclos hregR hreal hmem_final hcons_final
      | inr hIn =>
          have ⟨_hpoison, hpred_out⟩ :=
            assign_updated_lookup_shape_of_pc_true
              (ctx := ctx) (result1 := result1) (result2 := result2) (res := res) (ls := ls)
              hmem_res hpc hIn hlookup_res
          simp [qtypGuardTag, hpred_out] at hguard
    · constructor
      · intro x qt k hlookup hguard hkR
        have hkR_result2 : result2.regime'.lookup? k ≠ none := by
          have hkR_inv :
              (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k ≠ none := by
            simpa [ctxAfter, hRegime] using hkR
          exact
            invalidateRegimeDeps_lookup_ne_none_implies_original_ne_none
              result2.regime' result2.tagEnv' ls k hkR_inv
        have hvars :=
          hcwr2.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard hkR_result2
        cases hvars with
        | noPred_ok hnp =>
            exact varsRegime.noPred_ok (x, qt) hnp
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar_old hcons =>
            have hk_eq : k' = k := by
              have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                simpa using hclos
              have hguard' : qtypGuardTag qt = some k' := by
                simp [qtypGuardTag, hclos']
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact hguard'
                  _ = some k := hguard
              exact Option.some.inj this
            have hkR_inv :
                (invalidateRegimeDeps result2.regime' result2.tagEnv' ls).lookup? k ≠ none := by
              simpa [ctxAfter, hRegime] using hkR
            have hkeep : (invalidateTagDeps result2.tagEnv' ls).contains k = true :=
              invalidateRegimeDeps_survives_of_lookup_ne_none result2.regime' result2.tagEnv' ls k hkR_inv
            have hlookup_eq :
                (ctxAfter ctx res).regime.lookup? k = result2.regime'.lookup? k := by
              simpa [ctxAfter, hRegime] using
                invalidateRegimeDeps_lookup_eq_lookup_of_surviving_tag result2.regime' result2.tagEnv' ls k hkeep
            have hreg_result2 : result2.regime'.lookup? k = some b := by
              simpa [ctxAfter, hk_eq] using hreg
            have hregR : (ctxAfter ctx res).regime.lookup? k' = some b := by
              calc
                (ctxAfter ctx res).regime.lookup? k' = (ctxAfter ctx res).regime.lookup? k := by
                  simp [hk_eq]
                _ = result2.regime'.lookup? k := hlookup_eq
                _ = some b := hreg_result2
            have hcons_final :
                (b = true → qtypPredHolds predSat qt cf.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf.memory v) := by
              constructor
              · intro hbtrue
                exact (hqtypPredHolds_mem qt v).1 (hcons.1 hbtrue)
              · intro hbfalse hholds_new
                exact (hcons.2 hbfalse) ((hqtypPredHolds_mem qt v).2 hholds_new)
            have hvar_final : cf.varEnv.lookup x = some v := by
              simpa [hvar] using hvar_old
            exact
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b
                hclos hregR hvar_final hcons_final
      · intro x qt v hlookup hlookup_v
        have hcap :=
          hcwr2.2.2 x qt v
            (by simpa [ctxAfter] using hlookup)
            (by simpa [hvar] using hlookup_v)
        have hmono_res2_to_final :
            Regime.monotoneStep
              (ctxAfter (ctxAfter ctx result1) result2).regime
              (ctxAfter ctx res).regime := by
          simpa [ctxAfter, hRegime] using
            invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls
        have hcap_final_regime :
            closureCapturedVarsRegime predSat (ctxAfter ctx res).regime qt cfg2.memory θ v :=
          closureCapturedVarsRegime_monotone hmono_res2_to_final hcap
        exact closureCapturedVarsRegime_transport_μ hqtypPredHolds_mem hcap_final_regime

private lemma stepFRSingleRunFinalCleanPcTrue_assign
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctx (Expr.assign e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue .ioFree ctx (Expr.assign e1 e2) res predSat tm := by
  classical
  have htc' : typecheckAssign .ioFree ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨result1, result2, ls, htc1, hRef, htc2, hInt, hNextLoc, hNextTag, hRegime, hEtyp, hPoison, hPred⟩ :=
    typecheckAssign_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr .ioFree ctx e1 fuel' = .ok result1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc2_expr_raw :
      typecheckExpr
          .ioFree
          { ctx with
            memEnv := result1.memEnv', tagEnv := result1.tagEnv',
            nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
          e2 fuel' = .ok result2 := by
    simpa [Nat.succ_sub_one] using htc2
  have htc1' : typecheck .ioFree ctx e1 fuel' = .ok result1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree (ctxAfter ctx result1) e2 fuel' = .ok result2 := by
    simpa [typecheck, ctxAfter] using htc2_expr_raw
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht hpc
  have hinv := terminatesTo_assign_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hinv with ⟨cfg1, cfg2, aw, n, ht_e1, ht_e2, ho, hmem, hvar, _hnext, _hpm⟩
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm result1 htc1'
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 (Value.loc aw)
      hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hvloc1, hTm1, hwf1, hwfcfg1, hric1, hreg1, hcwr1, _hvalc1, hpres1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hmono1 : Regime.monotoneStep ctx.regime result1.regime' :=
    regime_monotone ctx e1 fuel' result1 htc1'
  have hRbound1 : regimeBounded (ctxAfter ctx result1).regime := by
    simpa [ctxAfter] using
      regimeBounded_of_monotoneStep ctx.regime result1.regime' hRbound hmono1
  have hpc1 : (ctxAfter ctx result1).pc = true := by
    simpa [ctxAfter] using hpc
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 (ctxAfter ctx result1) hTm1 result2 htc2'
  rcases
    hIH2 hpredlaws hTm1 cfg1.memory cfg1.varEnv θ1 cfg2 (Value.num n)
      hθ1wf hwf1 hric1 hreg1 hRbound1 hcwr1
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hvnum2, hTm2, hwf2, hwfcfg2, hric2, hreg2, hcwr2, _hvalc2, hpres2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hθ2wf : wfRealizationMap θ2 := hθext2.2 hθ1wf
  have hvloc2 : valueHasETyp θ2 (Value.loc aw) result1.qualType.etyp := by
    exact valueHasETyp_extends hθext2.1 hvloc1
  have hassign_eq :
      { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc result1.qualType.poison, pred := Predicate.noPred }
        memEnv' :=
          match Std.ExtTreeSet.toList ls with
          | [l] =>
              updateMemEnv result2.memEnv' l
                { etyp := ETyp.int
                  poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                  pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
          | _ =>
              updateLocsetWeak result2.memEnv' ls
                (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
                (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)
        tagEnv' := invalidateTagDeps result2.tagEnv' ls
        nextLoc' := ls.fold result2.nextLoc' (fun acc l => max acc (l + 1))
        nextTag' := result2.nextTag'
        regime' := invalidateRegimeDeps result2.regime' result2.tagEnv' ls } = res := by
    cases hq1 : result1.qualType with
    | mk etyp1 p1 pred1 =>
        cases hq2 : result2.qualType with
        | mk etyp2 p2 pred2 =>
            have hRef' := hRef
            have hInt' := hInt
            simp [hq1, hq2] at hRef' hInt'
            have htc_assign_simp := htc'
            simp [typecheckAssign, htc1_expr, htc2_expr_raw, hq1, hq2, hRef', hInt', bind, Except.bind, pure, Except.pure] at htc_assign_simp
            simpa [hq1, hq2] using htc_assign_simp
  have hmem_assign := congrArg TypeResult.memEnv' hassign_eq
  have htag_assign := congrArg TypeResult.tagEnv' hassign_eq
  have hmem_res :
      res.memEnv' =
        match Std.ExtTreeSet.toList ls with
        | [l] =>
            updateMemEnv result2.memEnv' l
              { etyp := ETyp.int
                poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
                pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
        | _ =>
            updateLocsetWeak result2.memEnv' ls
              (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
              (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred) := by
    simpa using hmem_assign.symm
  have htag_res : res.tagEnv' = invalidateTagDeps result2.tagEnv' ls := by
    simpa using htag_assign.symm
  rcases
    assign_single_run_post_transport_pc_true
      (ctx := ctx) (predSat := predSat) (tm := tm)
      (result1 := result1) (result2 := result2) (res := res) (ls := ls)
      (cfg2 := cfg2) (cf := cf) (θ := θ2) (a_w := aw) (n := n)
      hpredlaws hTm2 hwf2 hric2 hreg2 hcwr2
      hRef hvloc2 hθ2wf hmem hvar hNextLoc hNextTag hRegime hmem_res htag_res hpc
    with ⟨hTm_final, hwf_final, hric_final, hreg_final, hcwr_final⟩
  have hvalc_final :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ2 o := by
    subst ho
    refine
      valueConsistentWithRegime.noTag
        (predSat := predSat) (R := (ctxAfter ctx res).regime)
        (qt := res.qualType) (μ := cf.memory) (v := Value.unit)
        ?_ ?_
    · simp [qtypGuardTag, hPred]
    · exact
        closureCapturedVarsRegime_nonClosure_of_nonFunctionType
          (by simpa [hEtyp] using valueHasETyp.unit (θ := θ2))
          (by simp [hEtyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    exact
      assign_final_clean_preservation
        (ctx := ctx) (e2 := e2) (fuel' := fuel')
        (result1 := result1) (result2 := result2) (res := res) (ls := ls)
        (μ := μ) (cfg1 := cfg1) (cfg2 := cfg2) (cf := cf)
        (θ := θ) (θ1 := θ1) (θ2 := θ2)
        (aw := aw) (n := n)
        hRef hInt
        (by simpa [ctxAfter] using htc2_expr_raw)
        hmem_res hRegime hpc hvloc1 hθext2 hθ2wf hric2 hmem hpres1 hpres2
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved .ioFree (Expr.assign e1 e2) _ cf o ht hwfcfg).1
  refine ⟨θ2, hθext, ?_, hTm_final, hwf_final, hwfcfg_final, hric_final, hreg_final, hcwr_final, hvalc_final, hpres_final⟩
  subst ho
  simpa [hEtyp] using valueHasETyp.unit (θ := θ2)

private lemma stepFRSingleRunFinalCleanPcTrue_seq
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctx (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue .ioFree ctx (Expr.seq e1 e2) res predSat tm := by
  have htc' : typecheckSeq .ioFree ctx e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_seq_succ] at htc
    exact htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctx e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctx e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht hpc
  have hstruct := terminatesTo_seq_inv' e1 e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hstruct with ⟨cfg1, v1, ht_e1, ht_e2, _hpm1, _hpm2⟩
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm res1 htc1'
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hv1, hTm1, hwf1, hwfcfg1, hric1, hreg1, hcwr1, hvalc1, hpres1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [hctx', ctxAfter] using hTm1
  have hpc1 : ctx'.pc = true := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpc
  have hmono1 : Regime.monotoneStep ctx.regime res1.regime' :=
    regime_monotone ctx e1 fuel' res1 htc1'
  have hRbound1 : regimeBounded ctx'.regime := by
    have hctx'_regime : ctx'.regime = res1.regime' := by
      simp [hctx', updateCtxFromResult]
    rw [hctx'_regime]
    exact regimeBounded_of_monotoneStep ctx.regime res1.regime' hRbound hmono1
  have hric1' : runtimeInstantiatesCtx ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', ctxAfter] using hric1
  have hreg1' : regimeConsistentWithCtx ctx' := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hreg1
  have hcwr1' : consistentWithRegime predSat ctx'.regime ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hcwr1
  have hwf1' : wfTypeContext ctx' := by
    simpa [hctx', ctxAfter] using hwf1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res htc2'
  rcases
    hIH2 hpredlaws hwfTm' cfg1.memory cfg1.varEnv θ1 cf o
      hθ1wf hwf1' hric1' hreg1' hRbound1 hcwr1'
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hv2, hTm2, hwf2, hwfcfg2, hric2, hreg2, hcwr2, hvalc2, hpres2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res cfg1.memory cf.memory θ1 θ2 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hpres2
  have hclean_back :
      ∀ l qt_in qt_out,
        ctx.memEnv.lookup l = some qt_in →
        res.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true
        (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res)
        (by simpa [hctx', ctxAfter] using htc2')
        (by simpa [ctxAfter] using hpc)
        l qt_out hlookup_out hclean_out
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [ctxAfter] using hlookup_mid, by simpa [ctxAfter] using hclean_mid⟩
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctx) (res1 := res1) (res2 := res)
        hclean_back hpres1 hpres2'
  refine ⟨θ2, hθext, hv2, ?_, ?_, hwfcfg2, ?_, ?_, ?_, ?_, hpres_final⟩
  · simpa [hctxAfter] using hTm2
  · simpa [hctxAfter] using hwf2
  · simpa [hctxAfter] using hric2
  · simpa [hctxAfter] using hreg2
  · simpa [hctxAfter] using hcwr2
  · simpa [hctxAfter] using hvalc2

private lemma stepFRSingleRunFinalCleanPcTrue_unaryop
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (op : UnaryOp) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctx (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue .ioFree ctx (Expr.unaryop op e) res predSat tm := by
  have htc' : typecheckUnaryOp .ioFree ctx op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctx op e (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctx e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht hpc
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctx hwfTm res1 htc1'
  have hstruct := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o rfl ht
  rcases hstruct with ⟨cfg', v', ht_e, h_evalop, hmem, hvar, _hnext, _hpure⟩
  rcases
    hIH hpredlaws hwfTm μ ρ θ cfg' v'
      hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht_e hpc
    with ⟨θ', hθext, hvtyp, hTm', hwf', hwfcfg', hric', hreg', hcwr', hvalc', hpres'⟩
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime]
  have hvaltyp_final : valueHasETyp θ' o res.qualType.etyp := by
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v' o θ' res1.qualType.etyp result_etyp h_op h_evalop
  have hvalc_final :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ' o := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact
      valueConsistentWithRegime.noTag
        (predSat := predSat) (R := (ctxAfter ctx res).regime)
        (qt := res.qualType) (μ := cf.memory) (v := o)
        (by simp [qtypGuardTag, h_ret_pred])
        (closureCapturedVarsRegime_nonClosure_of_nonFunctionType hvaltyp_final hnotfun_res)
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ' := by
    rcases hpres' with ⟨hpres_fn⟩
    refine ⟨?_⟩
    intro l qt_in qt_out hlookup_in hlookup_out hclean_out
    have hlookup_out1 : res1.memEnv'.lookup l = some qt_out := by
      simpa [h_mem] using hlookup_out
    have hclean_out1 : qtypCleanUnder res1.regime' qt_out := by
      simpa [h_regime] using hclean_out
    simpa [hmem] using hpres_fn l qt_in qt_out hlookup_in hlookup_out1 hclean_out1
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf o ht hwfcfg).1
  refine ⟨θ', hθext, hvaltyp_final, ?_, ?_, hwfcfg_final, ?_, ?_, ?_, hvalc_final, hpres_final⟩
  · simpa [hctxAfter] using hTm'
  · simpa [hctxAfter] using hwf'
  · simpa [hctxAfter, hmem, hvar] using hric'
  · simpa [hctxAfter] using hreg'
  · simpa [hctxAfter, hmem, hvar] using hcwr'

private lemma stepFRSingleRunFinalCleanPcTrue_op
  (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctx (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue .ioFree ctx (Expr.op e1 op e2) res predSat tm := by
  have htc' : typecheckOp .ioFree ctx e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime,
          h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctx e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext :=
    { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
  have htc1' : typecheck .ioFree ctx e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht hpc
  have hstruct := terminatesTo_op_inv' e1 op e2
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  rcases hstruct with ⟨cfg1, v1, v2, ht_e1, ht_e2, h_evalop, hpm1, hpm2⟩
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctx hwfTm res1 htc1'
  rcases
    hIH1 hpredlaws hwfTm μ ρ θ cfg1 v1
      hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht_e1 hpc
    with ⟨θ1, hθext1, hv1, hTm1, hwf1, hwfcfg1, hric1, hreg1, hcwr1, hvalc1, hpres1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [ctx', ctxAfter] using hTm1
  have hwf1' : wfTypeContext ctx' := by
    simpa [ctx', ctxAfter] using hwf1
  have hric1' : runtimeInstantiatesCtx ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [ctx', ctxAfter] using hric1
  have hreg1' : regimeConsistentWithCtx ctx' := by
    simpa [ctx', ctxAfter] using hreg1
  have hcwr1' : consistentWithRegime predSat ctx'.regime ctx' cfg1.memory cfg1.varEnv θ1 := by
    simpa [ctx', ctxAfter] using hcwr1
  have hpc1 : ctx'.pc = true := by
    simp [ctx']
    exact hpc
  have hmono1 : Regime.monotoneStep ctx.regime res1.regime' :=
    regime_monotone ctx e1 fuel' res1 htc1'
  have hRbound1 : regimeBounded ctx'.regime := by
    have hctx'_regime : ctx'.regime = res1.regime' := by simp [ctx']
    rw [hctx'_regime]
    exact regimeBounded_of_monotoneStep ctx.regime res1.regime' hRbound hmono1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res2 htc2'
  rcases
    hIH2 hpredlaws hwfTm' cfg1.memory cfg1.varEnv θ1 cf v2
      hθ1wf hwf1' hric1' hreg1' hRbound1 hcwr1'
      cfg1.nextAddr cfg1.pureMode hwfcfg1 ht_e2 hpc1
    with ⟨θ2, hθext2, hv2, hTm2, hwf2, hwfcfg2, hric2, hreg2, hcwr2, hvalc2, hpres2⟩
  have hθext : wfExtendsMap θ θ2 := wfExtendsMap_trans hθext1 hθext2
  have hctxAfter : ctxAfter ctx res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag, h_regime]
  have hpres2' :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctx res1) res2 cfg1.memory cf.memory θ1 θ2 := by
    simpa [ctx', ctxAfter] using hpres2
  have hclean_back :
      ∀ l qt_in qt_out,
        ctx.memEnv.lookup l = some qt_in →
        res2.memEnv'.lookup l = some qt_out →
        qtypCleanUnder res2.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l _qt_in qt_out _hlookup_in hlookup_out hclean_out
    rcases
      typecheckExpr_clean_lookup_origin_of_pc_true
        (ctx := ctxAfter ctx res1) (e := e2) (fuel := fuel') (res := res2)
        (by simpa [ctx', ctxAfter] using htc2')
        (by simpa [ctxAfter] using hpc)
        l qt_out
        (by simpa using hlookup_out)
        (by simpa using hclean_out)
      with ⟨qt_mid, hlookup_mid, hclean_mid⟩
    exact ⟨qt_mid, by simpa [ctxAfter] using hlookup_mid, by simpa [ctxAfter] using hclean_mid⟩
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ2 := by
    have hpres_to_res2 :
        PreservesInheritedFinalCleanLocsOneRun ctx res2 μ cf.memory θ θ2 := by
      exact
        PreservesInheritedFinalCleanLocsOneRun.compose
          (ctx := ctx) (res1 := res1) (res2 := res2)
          hclean_back hpres1 hpres2'
    rcases hpres_to_res2 with ⟨hpres_fn⟩
    refine ⟨?_⟩
    intro l qt_in qt_out hlookup_in hlookup_out hclean_out
    have hlookup_out2 : res2.memEnv'.lookup l = some qt_out := by
      simpa [h_mem] using hlookup_out
    have hclean_out2 : qtypCleanUnder res2.regime' qt_out := by
      simpa [h_regime] using hclean_out
    exact hpres_fn l qt_in qt_out hlookup_in hlookup_out2 hclean_out2
  have hvaltyp_final : valueHasETyp θ2 o res.qualType.etyp := by
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v1 v2 o θ2 res1.qualType.etyp res2.qualType.etyp result_etyp
      (OpEType.complete h_op) h_evalop
  have hvalc_final :
      valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType cf.memory θ2 o := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op).2.2
    exact
      valueConsistentWithRegime.noTag
        (predSat := predSat) (R := (ctxAfter ctx res).regime)
        (qt := res.qualType) (μ := cf.memory) (v := o)
        (by simp [qtypGuardTag, h_ret_pred])
        (closureCapturedVarsRegime_nonClosure_of_nonFunctionType hvaltyp_final hnotfun_res)
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved .ioFree (Expr.op e1 op e2) _ cf o ht hwfcfg).1
  have hcfg_eq : cfg1.pureMode = pm := by
    simpa using hpm1
  refine ⟨θ2, hθext, hvaltyp_final, ?_, ?_, hwfcfg_final, ?_, ?_, ?_, hvalc_final, hpres_final⟩
  · simpa [hctxAfter] using hTm2
  · simpa [hctxAfter] using hwf2
  · simpa [hctxAfter, hcfg_eq] using hric2
  · simpa [hctxAfter] using hreg2
  · simpa [hctxAfter, hcfg_eq] using hcwr2

private lemma stepFRSingleRunFinalCleanPcTrue_fn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck .ioFree ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue mode ctxᵢ (Expr.fn x paramType body returnType) res predSat tm := by
  have htcFn : typecheckFn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  let res_expected : TypeResult := {
    qualType :=
      ⟨ETyp.arrow paramType returnType ctxᵢ.pc
          [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
        ctxᵢ.pc, Predicate.noPred⟩
    memEnv' := ctxᵢ.memEnv
    tagEnv' := ctxᵢ.tagEnv
    nextLoc' := ctxᵢ.nextLoc
    nextTag' := ctxᵢ.nextTag
    regime' := ctxᵢ.regime
  }
  have hres : res = res_expected := by
    have htc' := htcFn
    simp [typecheckFn] at htc'
    cases htc'
    rfl
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter, hres, res_expected]
  intro _hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg _hRbound hcwr a pm hwfcfg ht _hpc
  have ⟨hcf, ho⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
  subst hcf
  have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
    subst ho
    have hcover : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure
      (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp) (hcover := hcover) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ.lookup y := by symm; exact hvlookup
          _ = some v := hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  have hvalc : valueConsistentWithRegime predSat ctxᵢ.regime res.qualType μ θ o := by
    subst ho
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected]) ?_
    refine .intro ?_
    apply deepValueQTypProperty.closure x body ρ
      (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
      [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
    · rfl
    · simp [hres, res_expected]
    · simp
    · constructor
      · intro y qt_y k_y hlookup_σ hguard hkR
        exact hcwr.2.1 y qt_y k_y
          (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
          hguard hkR
      · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
          fun y qt hlookup_σ =>
            let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
            ⟨v, hv⟩,
          fun y qt v hlookup_σ hlookup_ρ =>
            let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
            by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
    · intro y qt_y v_y hlookup_σ hlookup_ρ
      exact (hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
        hlookup_ρ).1
  exact
    singleRunFinalCleanWitness_of_same_state
      (ctx := ctxᵢ) (res := res) (predSat := predSat) (tm := tm)
      (μ := μ) (ρ := ρ) (θ := θ)
      (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
      (o := o) (a := a) (pm := pm)
      hctxAfter rfl hvaltyp hvalc hwfTm hwf hric hreg hcwr hwfcfg

private lemma stepFRSingleRunFinalCleanPcTrue_pfn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck .ioFree ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue mode ctxᵢ (Expr.pfn x paramType body returnType) res predSat tm := by
  have htcPfn : typecheckPfn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody] at htcPfn
  | ok pbody =>
      let res_expected : TypeResult := {
        qualType :=
          ⟨ETyp.parrow paramType returnType ctxᵢ.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
            ctxᵢ.pc, Predicate.noPred⟩
        memEnv' := ctxᵢ.memEnv
        tagEnv' := ctxᵢ.tagEnv
        nextLoc' := ctxᵢ.nextLoc
        nextTag' := ctxᵢ.nextTag
        regime' := ctxᵢ.regime
      }
      have hres : res = res_expected := by
        have htc' := htcPfn
        simp [typecheckPfn, hbody] at htc'
        cases htc'
        rfl
      have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
        simp [ctxAfter, hres, res_expected]
      intro _hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg _hRbound hcwr a pm hwfcfg ht _hpc
      have ⟨hcf, ho⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
      subst hcf
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
        subst ho
        have hcover : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure
          (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv)
          (hpure := hto) (htcl := by simp) (hcover := hcover) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ.lookup y := by symm; exact hvlookup
              _ = some v := hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      have hvalc : valueConsistentWithRegime predSat ctxᵢ.regime res.qualType μ θ o := by
        subst ho
        refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected]) ?_
        refine .intro ?_
        apply deepValueQTypProperty.peClosure x body pbody ρ
          (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
          [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · exact hto
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          exact (hcwr.2.2 y qt_y v_y
            (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
            hlookup_ρ).1
      exact
        singleRunFinalCleanWitness_of_same_state
          (ctx := ctxᵢ) (res := res) (predSat := predSat) (tm := tm)
          (μ := μ) (ρ := ρ) (θ := θ)
          (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
          (o := o) (a := a) (pm := pm)
          hctxAfter rfl hvaltyp hvalc hwfTm hwf hric hreg hcwr hwfcfg

private lemma var_valueConsistentWithRegime_of_typecheck
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (name : Name) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
  (htc : typecheckVar ctxᵢ name = .ok res)
  (hρ : ρ.lookup name = some v)
  (hcwr : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ) :
  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime res.qualType μ θ v := by
  have hregime' : res.regime' = ctxᵢ.regime :=
    typecheckVar_preserves_regime ctxᵢ name res htc
  have hreg_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by
    simp [ctxAfter, hregime']
  simp [hreg_after]
  cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
  | none =>
      simp [typecheckVar, hlookup_ctx] at htc
  | some qt =>
      cases hpred : qt.pred with
      | noPred =>
          have hres :
              res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
            have htc'' := htc
            cases hqt : qt with
            | mk etyp poison pred =>
                have hpred' : pred = Predicate.noPred := by
                  simpa [hqt] using hpred
                simp [typecheckVar, hlookup_ctx, hpred', hqt, pure, Except.pure] at htc''
                cases htc''
                rfl
          exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
            (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardOnly k =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardOnly k := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              exact valueConsistentWithRegime.guardOnly_ok k (by simp [hres, hpred])
                (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardOnly k := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
      | guardClosure k arg_name pred_body var_env =>
          cases htag : ctxᵢ.tagEnv.get? k with
          | none =>
              have hres :
                  res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                have htc'' := htc
                cases hqt : qt with
                | mk etyp poison pred =>
                    have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                      simpa [hqt] using hpred
                    have htag' : ctxᵢ.tagEnv[k]? = none := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases hft : etyp.isFunctionType with
                    | true =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                        cases htc''
                    | false =>
                        simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                        cases htc''
                        simp [hpred']
              have hnclos : closureCapturedVarsRegime predSat ctxᵢ.regime res.qualType μ θ v :=
                closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ)
              cases hk : ctxᵢ.regime.lookup? k with
              | none =>
                  exact valueConsistentWithRegime.notInRegime k (by simp [qtypGuardTag, hres, hpred]) hk
                    hnclos
              | some b =>
                  have htag_qt : qtypGuardTag qt = some k := by
                    simp [qtypGuardTag, hpred]
                  have hvr : varsRegime predSat ctxᵢ.regime μ ρ (name, qt) :=
                    hcwr.2.1 name qt k hlookup_ctx htag_qt (by simp [hk])
                  cases hvr with
                  | noPred_ok hnp =>
                      exfalso
                      simp [hnp] at htag_qt
                  | guardOnly_ok _k hgo =>
                      exfalso
                      simp [hpred] at hgo
                  | withPred_ok k' arg_name' pred_body' var_env' v' b' hclos hregime hvar hconsist =>
                      have hk' : k' = k := by
                        have hclos' : qt.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                          simpa using hclos
                        have : some k' = some k := by
                          simpa [qtypGuardTag, hclos'] using htag_qt
                        exact Option.some.inj this
                      cases hk'
                      have hb' : b' = b := by
                        have : some b' = some b := by simpa [hregime] using hk
                        exact Option.some.inj this
                      cases hb'
                      have hv' : v' = v := by
                        have : some v' = some v := by simpa [hvar] using hρ
                        exact Option.some.inj this
                      cases hv'
                      cases b with
                      | false =>
                          have hnot_qt : ¬ qtypPredHolds predSat qt μ v := (hconsist.2 rfl)
                          have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                            qtypPredHolds_transport_pred_not (predSat := predSat) (qt := qt) (qt' := res.qualType)
                              (by simp [hres]) hnot_qt
                          exact valueConsistentWithRegime.inRegimeFalse k
                            (by simp [qtypGuardTag, hres, hpred]) hk hnot_res
                            hnclos
                      | true =>
                          have hholds_qt : qtypPredHolds predSat qt μ v := (hconsist.1 rfl)
                          have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := qt) (qt' := res.qualType)
                              (by simp [hres]) hholds_qt
                          exact valueConsistentWithRegime.inRegimeTrue k
                            (by simp [qtypGuardTag, hres, hpred]) hk hholds_res
                            hnclos
          | some tv =>
              cases tv with
              | mk b deps =>
                  have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                    simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                  cases b with
                  | true =>
                      have hres :
                          res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))
                  | false =>
                      have hres :
                          res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                        have htc'' := htc
                        cases hqt : qt with
                        | mk etyp poison pred =>
                            have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                              simpa [hqt] using hpred
                            have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                              simpa using htag'
                            cases hft : etyp.isFunctionType with
                            | true =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                cases htc''
                            | false =>
                                simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                cases htc''
                                rfl
                      exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres])
                        (closureCapturedVarsRegime_transport_etyp (by simp [hres]) (hcwr.2.2 name qt v hlookup_ctx hρ))

private lemma stepFRSingleRunFinalCleanPcTrue_var
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck .ioFree ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue mode ctxᵢ (Expr.var name) res predSat tm := by
  have htc' : typecheckVar ctxᵢ name = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter,
      typecheckVar_preserves_memEnv ctxᵢ name res htc',
      typecheckVar_preserves_tagEnv ctxᵢ name res htc',
      typecheckVar_preserves_nextLoc ctxᵢ name res htc',
      typecheckVar_preserves_nextTag ctxᵢ name res htc',
      typecheckVar_preserves_regime ctxᵢ name res htc']
  intro _hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg _hRbound hcwr a pm hwfcfg ht _hpc
  rcases
    terminatesTo_var_inv' mode name
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o ht
    with ⟨v, hlookup, hcf, ho⟩
  subst hcf
  have hvaltyp : valueHasETyp θ o res.qualType.etyp := by
    rw [ho]
    exact var_valueHasETyp_of_typecheck ctxᵢ μ ρ θ name res v htc' hθwf hric hlookup
  have hvalc : valueConsistentWithRegime predSat ctxᵢ.regime res.qualType μ θ o := by
    rw [ho]
    simpa [hctxAfter] using
      var_valueConsistentWithRegime_of_typecheck
        (ctxᵢ := ctxᵢ) (predSat := predSat) (name := name) (res := res)
        (μ := μ) (ρ := ρ) (θ := θ) (v := v)
        htc' hlookup hcwr
  exact
    singleRunFinalCleanWitness_of_same_state
      (ctx := ctxᵢ) (res := res) (predSat := predSat) (tm := tm)
      (μ := μ) (ρ := ρ) (θ := θ)
      (cf := { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
      (o := o) (a := a) (pm := pm)
      hctxAfter rfl hvaltyp hvalc hwfTm hwf hric hreg hcwr hwfcfg

private lemma stepFR_var
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (name : Name) (res : TypeResult) (fuel : Nat)
  (htc : typecheck .ioFree ctxᵢ (Expr.var name) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.var name) res predSat tm := by
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have htagR : tagEnvConsistentWithRegime ctxᵢ.tagEnv ctxᵢ.regime := hreg.1
  -- Use inversion lemma to extract config and value
  have hinv₀ := terminatesTo_var_inv' mode name
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have hinv₁ := terminatesTo_var_inv' mode name
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hinv₀ with ⟨v₀', hlookup₀, hcf₀, hv₀⟩
  rcases hinv₁ with ⟨v₁', hlookup₁, hcf₁, hv₁⟩
  -- Substitute: o₀ = v₀', o₁ = v₁'
  subst hv₀ hv₁
  -- After subst hcf₀/hcf₁, cf₀ and cf₁ become the original input configs
  subst hcf₀ hcf₁
  -- StepFR existential structure:
  -- ∃ θ₀' θ₁', wfExtendsMap θ₀ θ₀' ∧ wfExtendsMap θ₁ θ₁' ∧
  --            wfTypeContext (ctxAfter ctx res) ∧
  --            wfConfig cf₀ ∧ wfConfig cf₁ ∧
  --            runtimeInstantiatesCtx ... ∧ runtimeInstantiatesCtx ... ∧
  --            regimeConsistentWithCtx ... ∧ agreeOnClean ... ∧ valueConsistentWithRegime ... ∧ valueConsistentWithRegime ... ∧ resultAgreesIfClean ...
  have htc' : typecheckVar ctxᵢ name = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  have hmem : res.memEnv' = ctxᵢ.memEnv :=
    typecheckVar_preserves_memEnv ctxᵢ name res htc'
  have htag : res.tagEnv' = ctxᵢ.tagEnv :=
    typecheckVar_preserves_tagEnv ctxᵢ name res htc'
  have hnextLoc : res.nextLoc' = ctxᵢ.nextLoc :=
    typecheckVar_preserves_nextLoc ctxᵢ name res htc'
  have hnextTag : res.nextTag' = ctxᵢ.nextTag :=
    typecheckVar_preserves_nextTag ctxᵢ name res htc'
  have hregime' : res.regime' = ctxᵢ.regime :=
    typecheckVar_preserves_regime ctxᵢ name res htc'
  have hreg_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by
    simp [ctxAfter, hregime']
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
    | none =>
        simp [typecheckVar, hlookup_ctx] at htc'
    | some qt =>
        have hqtTm : QTypRespectsTagMeaning tm qt :=
          wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ name qt hwfTm hlookup_ctx
        cases hpred : qt.pred with
        | noPred =>
            have hres :
                res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
              have htc'' := htc'
              cases hqt : qt with
              | mk etyp poison pred =>
                  have hpred' : pred = Predicate.noPred := by
                    simpa [hqt] using hpred
                  simp [typecheckVar, hlookup_ctx, hpred', hqt, pure, Except.pure] at htc''
                  cases htc''
                  rfl
            have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
            have hpredEq : res.qualType.pred = qt.pred := by simp [hres, hpred]
            exact fun {qt'} {k} {d} hinq hqd =>
              (QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
        | guardOnly k =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardOnly k := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                have hpredEq : res.qualType.pred = qt.pred := by simp [hres]
                exact fun {qt'} {k} {d} hinq hqd =>
                  (QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
            | some tv =>
                cases tv with
                | mk b deps =>
                    have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases b with
                    | true =>
                        have hres :
                            res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
                    | false =>
                        have hres :
                            res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
        | guardClosure k arg_name pred_body var_env =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType = ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                have hpredEq : res.qualType.pred = qt.pred := by simp [hres]
                exact fun {qt'} {k} {d} hinq hqd =>
                  (QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hpredEq) hinq hqd
            | some tv =>
                cases tv with
                | mk b deps =>
                    have htag' : ctxᵢ.tagEnv[k]? = some (TagVal.mk b deps) := by
                      simpa [Std.ExtTreeMap.get?_eq_getElem?] using htag
                    cases b with
                    | true =>
                        have hres :
                            res.qualType = ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
                    | false =>
                        have hres :
                            res.qualType = ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  simp
                        have hetyp : res.qualType.etyp = qt.etyp := by simp [hres]
                        have hguard : qtypGuardDesc? res.qualType = none := by
                          simp [hres, qtypGuardDesc?]
                        exact fun {qt'} {k} {d} hinq hqd =>
                          (QTypRespectsTagMeaning_transport_etyp_noGuard
                            (tm := tm) (qt := qt) (qt' := res.qualType) hqtTm hetyp hguard) hinq hqd
  have hvcons
      (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (v : Value)
      (hρ : ρ.lookup name = some v)
    (hcwr : consistentWithRegime predSat ctxᵢ.regime ctxᵢ μ ρ θ)
    (hric : runtimeInstantiatesCtx ctxᵢ μ ρ θ) :
    valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime res.qualType μ θ v := by
    exact
      var_valueConsistentWithRegime_of_typecheck
        (ctxᵢ := ctxᵢ) (predSat := predSat) (name := name) (res := res)
        (μ := μ) (ρ := ρ) (θ := θ) (v := v)
        htc' hρ hcwr
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (θ₀ = θ₀')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- wfExtendsMap θ₁ θ₁ (θ₁ = θ₁')
    refine ⟨?_, ?_⟩
    · intro l a hlookup; exact hlookup
    · intro hwf'; exact hwf'
  · -- valueHasETyp θ₀ o₀ res.qualType.etyp
    exact var_valueHasETyp_of_typecheck ctxᵢ μ₀ ρ₀ θ₀ name res o₀ htc' hθ₀ hric₀ hlookup₀
  · -- valueHasETyp θ₁ o₁ res.qualType.etyp
    exact var_valueHasETyp_of_typecheck ctxᵢ μ₁ ρ₁ θ₁ name res o₁ htc' hθ₁ hric₁ hlookup₁
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res): typecheckVar does not change varEnv/memEnv
    simpa [ctxAfter, hmem] using hwfTm
  · -- wfTypeContext (ctxAfter ctxᵢ res): typecheckVar does not change the context
    simpa [ctxAfter, wfTypeContext, hmem, hnextLoc] using hwf
  · -- wfConfig cf₀ (unchanged since var doesn't modify config)
    exact hwfcfg₀
  · -- wfConfig cf₁ (unchanged since var doesn't modify config)
    exact hwfcfg₁
  · -- runtimeInstantiatesCtx for θ₀' (var doesn't change context or config)
    simpa [ctxAfter, hmem] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [ctxAfter, hmem] using hric₁
  · -- regimeConsistentWithCtx (var doesn't change tagEnv or nextTag or regime)
    -- (ctxAfter ctxᵢ res).regime = res.regime' = ctxᵢ.regime
    simpa [ctxAfter, regimeConsistentWithCtx, htag, hnextTag, hregime'] using hreg
  · -- consistentWithRegime for run 0 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using hcwr₀
  · -- consistentWithRegime for run 1 (var doesn't change context)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using hcwr₁
  · -- agreeOnClean for ctxAfter: typecheckVar doesn't change the context (including regime)
    simpa [ctxAfter, hmem, htag, hnextLoc, hnextTag, hregime'] using hagree
  · -- valueConsistentWithRegime for cf₀
    exact hvcons μ₀ ρ₀ θ₀ o₀ hlookup₀ hcwr₀ hric₀
  · -- valueConsistentWithRegime for cf₁
    exact hvcons μ₁ ρ₁ θ₁ o₁ hlookup₁ hcwr₁ hric₁
  · -- Result agreement for clean outputs (requires predicate/tagEnv analysis).
    -- Key: (ctxAfter ctxᵢ res).regime = res.regime' = ctxᵢ.regime
    have hregime_after : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [ctxAfter, hregime']
    -- Rewrite the goal to use ctxᵢ.regime so the rest of the proof works
    simp only [hregime_after]
    intro hclean
    have htc' : typecheckVar ctxᵢ name = .ok res := by
      simpa [typecheck, typecheckExpr] using htc
    cases hlookup_ctx : ctxᵢ.varEnv.lookup name with
    | none =>
        -- typecheckVar cannot succeed if the variable is missing
        simp [typecheckVar, hlookup_ctx] at htc'
    | some qt =>
        have hvar_agree_of_clean :
            qtypCleanUnder ctxᵢ.regime qt →
            agreeVarUnder predSat ctxᵢ.regime μ₀ ρ₀ μ₁ ρ₁ θ₀ θ₁ (name, qt) := by
          intro hclean_qt
          exact (hagree.2 name qt hlookup_ctx hclean_qt)
        cases hpred : qt.pred with
        | noPred =>
            have hres :
                res.qualType =
                  ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, Predicate.noPred⟩ := by
              have htc'' := htc'
              cases hqt : qt with
              | mk etyp poison pred =>
                  have hpred' : pred = Predicate.noPred := by
                    simpa [hqt] using hpred
                  simp [typecheckVar, hlookup_ctx, hpred', hqt] at htc''
                  cases htc''
                  rfl
            have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
              cases hclean with
              | clean hpoison_res =>
                  simpa [hres] using hpoison_res
              | guard k htag hreg _ =>
                  exfalso
                  simp [qtypGuardTag, hres] at htag
            have hpc_poison := joinPoison_eq_false hjoin
            have hpc : ctxᵢ.pc = false := hpc_poison.1
            have hpoison : qt.poison = false := hpc_poison.2
            have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
              exact qtypCleanUnder.clean hpoison
            have hvar := hvar_agree_of_clean hclean_qt
            have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
              agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
            have hres_eq : res.qualType = qt := by
              cases qt with
              | mk etyp poison pred =>
                  cases hpred
                  simp [hres, hpc, joinPoison]
            have hres_agree :
                agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
              simpa [hres_eq] using hval
            exact hres_agree
        | guardOnly k =>
          cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType =
                      ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardOnly k := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                cases hclean with
                | clean hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_eq : res.qualType = qt := by
                      cases qt with
                      | mk etyp poison pred =>
                          cases hpred
                          simp [hres, hpc, joinPoison]
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      simpa [hres_eq] using hval
                    simpa [hlookup₀, hlookup₁] using hres_agree
                | guard k' htag' hregime hnotfun_res =>
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hnotfun_qt : qt.etyp.isFunctionType = false := by
                      simpa [hres] using hnotfun_res
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                        | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Arrow types are function types, contradicting hnotfun_res
                            simp only [hres, hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.true_or] at hnotfun_res
                            cases hnotfun_res
                        | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                            -- dirty_internal_arrow requires isArrow = true, contradicting hnotfun_res
                            simp only [hres, ETyp.isFunctionType] at hnotfun_res
                            rw [hisArrow, Bool.true_or] at hnotfun_res
                            cases hnotfun_res
                        | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Parrow types are function types, contradicting hnotfun_res
                            simp only [hres, hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.or_true] at hnotfun_res
                            cases hnotfun_res
                        | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                            -- dirty_internal_parrow requires isParrow = true, contradicting hnotfun_res
                            simp only [hres, ETyp.isFunctionType] at hnotfun_res
                            rw [hisParrow, Bool.or_true] at hnotfun_res
                            cases hnotfun_res
                        | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                            have htagRes : qtypGuardTag res.qualType = some k := by
                              simp [qtypGuardTag, hres, hpred]
                            have hetyp' : res.qualType.etyp = qt.etyp := by
                              simp [hres]
                            exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                              hlookup1 hin hv1 hlookup2 hv2
                      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
                    simpa [hlookup₀, hlookup₁] using hres_agree
            | some tv =>
                cases tv with
                | mk b deps =>
                    cases b with
                    | true =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                                simpa using htag
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  rfl
                        have hpc : ctxᵢ.pc = false := by
                          -- clean result requires pc = false
                          cases hclean with
                          | clean hpoison_res =>
                              simpa [hres] using hpoison_res
                          | guard k_guard htag_guard hreg_guard _ =>
                              exfalso
                              simp [qtypGuardTag, hres] at htag_guard
                        have hregime : ctxᵢ.regime.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hnotfun_qt : qt.etyp.isFunctionType = false := by
                          -- If qt.etyp were a function type, typecheckVar would have thrown an error
                          by_contra h
                          simp at h
                          -- From htc', typecheckVar succeeded
                          have htc'' := htc'
                          cases qt with
                          | mk etyp poison pred =>
                              have : pred = Predicate.guardOnly k := by simpa using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by simpa using htag
                              simp [this, h, typecheckVar, hlookup_ctx, htag', throw] at htc''
                              cases htc''
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow (by simp [hres, hpc]) hnotfun' hnotref' hEq
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Arrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                              -- Dirty arrow: qt.etyp is arrow but hnotfun_qt says it's not a function type
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisArrow, Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Parrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                              -- Dirty parrow: qt.etyp is parrow but hnotfun_qt says it's not a function type
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisParrow, Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                        simpa [hlookup₀, hlookup₁] using hres_agree
                    | false =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardOnly k := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                                simpa using htag
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  rfl
                        -- poisoned result is not clean
                        exfalso
                        cases hclean with
                        | clean hpoison =>
                            have : false = true := by
                              calc
                                false = res.qualType.poison := by symm; exact hpoison
                                _ = true := by simp [hres]
                            cases this
                        | guard k_guard htag_guard hreg_guard _ =>
                            simp [qtypGuardTag, hres] at htag_guard
        | guardClosure k arg_name pred_body var_env =>
            cases htag : ctxᵢ.tagEnv.get? k with
            | none =>
                have hres :
                    res.qualType =
                      ⟨qt.etyp, joinPoison ctxᵢ.pc qt.poison, qt.pred⟩ := by
                  have htc'' := htc'
                  cases hqt : qt with
                  | mk etyp poison pred =>
                      have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                        simpa [hqt] using hpred
                      have htag' : ctxᵢ.tagEnv[k]? = none := by
                        simpa using htag
                      cases hft : etyp.isFunctionType with
                      | true =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                          cases htc''
                      | false =>
                          simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                          cases htc''
                          simp [hpred']
                cases hclean with
                | clean hpoison_res =>
                    have hjoin : joinPoison ctxᵢ.pc qt.poison = false := by
                      have hpoison_res' := hpoison_res
                      simp [hres] at hpoison_res'
                      exact hpoison_res'
                    have hpc_poison := joinPoison_eq_false hjoin
                    have hpc : ctxᵢ.pc = false := hpc_poison.1
                    have hpoison : qt.poison = false := hpc_poison.2
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      exact qtypCleanUnder.clean hpoison
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      have hqt_eq : qt = ⟨qt.etyp, false, qt.pred⟩ := by
                        cases qt with
                        | mk etyp poison pred =>
                            simpa [hpoison]
                      have hres_eq : res.qualType = qt := by
                        have : res.qualType = ⟨qt.etyp, false, qt.pred⟩ := by
                          simp [hres, hpoison, hpc, joinPoison]
                        exact this.trans hqt_eq.symm
                      simpa [hres_eq] using hval
                    simpa [hlookup₀, hlookup₁] using hres_agree
                | guard k' htag' hregime hnotfun_res =>
                    have hk : k = k' := by
                      have : some k = some k' := by
                        simpa [qtypGuardTag, hres, hpred] using htag'
                      exact Option.some.inj this
                    subst hk
                    have hnotfun_qt : qt.etyp.isFunctionType = false := by
                      simpa [hres] using hnotfun_res
                    have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                      have htag_qt : qtypGuardTag qt = some k := by
                        simp [qtypGuardTag, hpred]
                      exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                    have hvar := hvar_agree_of_clean hclean_qt
                    have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                      agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                    have hres_agree :
                        agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                      cases hval with
                      | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                        | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Arrow types are function types, contradicts hnotfun_qt
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.true_or] at hnotfun_qt
                            cases hnotfun_qt
                        | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                            exfalso
                            simp only [ETyp.isFunctionType] at hnotfun_qt
                            rw [hisArrow, Bool.true_or] at hnotfun_qt
                            cases hnotfun_qt
                        | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                            -- Parrow types are function types, contradicts hnotfun_qt
                            exfalso
                            simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                              Bool.or_true] at hnotfun_qt
                            cases hnotfun_qt
                        | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                            exfalso
                            simp only [ETyp.isFunctionType] at hnotfun_qt
                            rw [hisParrow, Bool.or_true] at hnotfun_qt
                            cases hnotfun_qt
                      | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
                      | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                          have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                            intro ⟨ls, h⟩
                            apply hnotref
                            exact ⟨ls, by simpa [hres] using h⟩
                          have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                            simpa [hres] using hnotfun
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          exact agreeValueUnder.withPred_true_eq k htagRes hregime hnotfun' hnotref' hEq
                      | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                          have htagRes : qtypGuardTag res.qualType = some k := by
                            simp [qtypGuardTag, hres, hpred]
                          have hetyp' : res.qualType.etyp = qt.etyp := by
                            simp [hres]
                          exact agreeValueUnder.withPred_true_ref k htagRes hregime (hetyp'.trans hetyp)
                            hlookup1 hin hv1 hlookup2 hv2
                    simpa [hlookup₀, hlookup₁] using hres_agree
            | some tv =>
                cases tv with
                | mk b deps =>
                    cases b with
                    | true =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, ctxᵢ.pc, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by
                                simpa using htag
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  rfl
                        have hpc : ctxᵢ.pc = false := by
                          cases hclean with
                          | clean hpoison => simpa [hres] using hpoison
                          | guard k_guard htag_guard hreg_guard _ =>
                              exfalso
                              simp [qtypGuardTag, hres] at htag_guard
                        have hregime : ctxᵢ.regime.lookup? k = some true := by
                          exact htagR k deps (by simpa [htag] using htag)
                        have hnotfun_qt : qt.etyp.isFunctionType = false := by
                          -- If qt.etyp were a function type, typecheckVar would have thrown an error
                          by_contra h
                          simp at h
                          -- From htc', typecheckVar succeeded
                          have htc'' := htc'
                          cases qt with
                          | mk etyp poison pred =>
                              have : pred = Predicate.guardClosure k arg_name pred_body var_env := by simpa using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨true, deps⟩ := by simpa using htag
                              simp [this, h, typecheckVar, hlookup_ctx, htag', throw] at htc''
                              cases htc''
                        have hclean_qt : qtypCleanUnder ctxᵢ.regime qt := by
                          have htag_qt : qtypGuardTag qt = some k := by
                            simp [qtypGuardTag, hpred]
                          exact qtypCleanUnder.guard k htag_qt hregime hnotfun_qt
                        have hvar := hvar_agree_of_clean hclean_qt
                        have hval : agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ :=
                          agreeValueUnder_of_agreeVarUnder hvar hlookup₀ hlookup₁
                        have hres_agree :
                            agreeValueUnder predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
                          cases hval with
                          | clean_eq_nonref_nonarrow _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | clean_internal_arrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Arrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisArrow, Bool.true_or] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_internal_parrow hclean hetyp htcl hmatch hcap hv₁ hv₂ =>
                              -- Parrow types are function types, contradicts hnotfun_qt
                              exfalso
                              simp only [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow,
                                Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
                              exfalso
                              simp only [ETyp.isFunctionType] at hnotfun_qt
                              rw [hisParrow, Bool.or_true] at hnotfun_qt
                              cases hnotfun_qt
                          | clean_ref _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                          | withPred_true_eq _ _ _ hnotfun hnotref hEq =>
                              have hnotref' : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
                                intro ⟨ls, h⟩
                                apply hnotref
                                exact ⟨ls, by simpa [hres] using h⟩
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              have hnotfun' : res.qualType.etyp.isFunctionType = false := by
                                simpa [hres] using hnotfun
                              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison' hnotfun' hnotref' hEq
                          | withPred_true_ref _ _ _ hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                              have hetyp' : res.qualType.etyp = qt.etyp := by
                                simp [hres]
                              have hpoison' : res.qualType.poison = false := by
                                simp [hres, hpc]
                              exact agreeValueUnder.clean_ref hpoison' (hetyp'.trans hetyp)
                                hlookup1 hin hv1 hlookup2 hv2
                        simpa [hlookup₀, hlookup₁] using hres_agree
                    | false =>
                        have hres :
                            res.qualType =
                              ⟨qt.etyp, true, Predicate.noPred⟩ := by
                          have htc'' := htc'
                          cases hqt : qt with
                          | mk etyp poison pred =>
                              have hpred' : pred = Predicate.guardClosure k arg_name pred_body var_env := by
                                simpa [hqt] using hpred
                              have htag' : ctxᵢ.tagEnv[k]? = some ⟨false, deps⟩ := by
                                simpa using htag
                              cases hft : etyp.isFunctionType with
                              | true =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, throw] at htc''
                                  cases htc''
                              | false =>
                                  simp [typecheckVar, hlookup_ctx, hpred', hqt, htag', hft, pure, Except.pure] at htc''
                                  cases htc''
                                  rfl
                        -- poisoned result is not clean
                        exfalso
                        cases hclean with
                        | clean hpoison =>
                            have : false = true := by
                              calc
                                false = res.qualType.poison := by symm; exact hpoison
                                _ = true := by simp [hres]
                            cases this
                        | guard k_guard htag_guard hreg_guard _ =>
                            simp [qtypGuardTag, hres] at htag_guard

-- World-free version of stepFRW_op
-- TODO: Needs refactoring - StepFR structure changed and terminatesTo lemmas need adjusting
private lemma stepFR_op
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (op : Op) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.op e1 op e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.op e1 op e2) res predSat tm := by
  -- Parse typecheck result
  have htc' : typecheckOp .ioFree ctxᵢ e1 e2 (Nat.succ fuel') op = .ok res := by
    simp [typecheck, typecheckExpr_op_succ] at htc
    exact htc
  obtain ⟨res1, res2, result_etyp, htc1, htc2, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime,
          h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckOp_structure ctxᵢ e1 e2 op (Nat.succ fuel') res htc'
  let ctx' : TypeContext :=
    { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res2 := by
    simpa [ctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  -- Use world-free inversion lemma for binary op
  have hstruct₀ := terminatesTo_op_inv' e1 op e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, v₀2, ht₀_e1, ht₀_e2, h_evalop₀, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_op_inv' e1 op e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, v₁2, ht₁_e1, ht₁_e2, h_evalop₁, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1, hres_agree1⟩
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simpa [ctx', ctxAfter] using _hTm1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res2 htc2'
  -- Prepare for IH2: need wf maps and agreement for ctx'
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [ctx', ctxAfter] using hwf1
  -- runtimeInstantiatesCtx and regimeConsistentWithCtx come directly from IH1
  -- Just need to transfer from ctxAfter ctxᵢ res1 to ctx' (which are equal)
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hric₁1
  have htagR1' : regimeConsistentWithCtx ctx' := by
    -- Comes directly from IH1; `ctx'` is exactly `ctxAfter ctxᵢ res1`.
    simpa [ctx', ctxAfter] using htagR1
  -- Regime monotonicity (typing can only drop entries).
  have h_mono : Regime.monotoneStep ctxᵢ.regime res1.regime' :=
    regime_monotone ctxᵢ e1 fuel' res1 htc1'
  -- agreeOnClean from IH1 directly applies since ctx' = ctxAfter ctxᵢ res1
  have hctx'_eq : ctx' = ctxAfter ctxᵢ res1 := by simp [ctx', ctxAfter]
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simp only [hctx'_eq]
    exact hagree_clean1
  -- consistentWithRegime from IH1 uses (ctxAfter ctxᵢ res1).regime = res1.regime' = ctx'.regime
  -- So hcwr₀1 and hcwr₁1 directly give what we need
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx', ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx', ctxAfter] using hcwr₁1
  -- regimeBounded transfers via monotonicity (bounds are equal)
  have hRbound' : regimeBounded ctx'.regime := by
    have hctx'_regime : ctx'.regime = res1.regime' := by simp [ctx']
    rw [hctx'_regime]
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound h_mono
  -- Apply IH for e2
  -- Note: cfg₀1.pureMode = cfg₁1.pureMode = pm (from inversion lemmas)
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  -- Convert ht₁_e2 to use cfg₀1.pureMode
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cf₁ v₁2 := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e2 :=
    hIH2 hpredlaws hwfTm' cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ v₀2 v₁2
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res2 := by
    simp [ctxAfter, ctx', h_mem, h_tag, h_loc, h_ntag, h_regime]
  -- IH2 gives agreeOnClean predSat (ctxAfter ctx' res2).regime ...
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res2, the regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  -- IH2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) (ctxAfter ctx' res2).regime
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res2, this directly gives what we need
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hnonfun_args :
        res1.qualType.etyp.isFunctionType = false ∧
        res2.qualType.etyp.isFunctionType = false ∧
        result_etyp.isFunctionType = false :=
      opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_args.2.2
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_ret_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun_res hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · -- valueHasETyp θ₀2 o₀ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v₀1 v₀2 o₀ θ₀2 res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₀
  · -- valueHasETyp θ₁2 o₁ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalOp op v₁1 v₁2 o₁ θ₁2 res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₁
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · -- valueConsistentWithRegime for cf₀
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opEType_implies_nonfun op res1.qualType.etyp
        res2.qualType.etyp result_etyp h_op).2.2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalOp op v₀1 v₀2 o₀ θ₀2
              res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₀)
        hnotfun_res')
  · -- valueConsistentWithRegime for cf₁
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opEType_implies_nonfun op res1.qualType.etyp
        res2.qualType.etyp result_etyp h_op).2.2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalOp op v₁1 v₁2 o₁ θ₁2
              res1.qualType.etyp res2.qualType.etyp result_etyp (OpEType.complete h_op) h_evalop₁)
        hnotfun_res')
  intro hclean
  have hpoison_res : res.qualType.poison = false := by
    cases hclean with
    | clean hpoison => exact hpoison
    | guard k htag hreg _ =>
        exfalso
        simp [qtypGuardTag, h_ret_pred] at htag
  have hjoin :
      joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) = false := by
    calc
      joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison res2.qualType.poison) =
          res.qualType.poison := by symm; exact h_ret_poison
      _ = false := by exact hpoison_res
  have hjoin_pc := joinPoison_eq_false hjoin
  have hjoin_12 := joinPoison_eq_false hjoin_pc.2
  -- hres_agree1 expects qtypCleanUnder (ctxAfter ctxᵢ res1).regime from IH1
  have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := qtypCleanUnder.clean hjoin_12.1
  -- hres_agree2 expects qtypCleanUnder (ctxAfter ctx' res2).regime from IH2
  have hclean2 : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType := qtypCleanUnder.clean hjoin_12.2
  have hagree_v1 :
      agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 res1.qualType v₀1 v₁1 :=
    hres_agree1 hclean1
  have hagree_v2 :
      agreeValueUnder predSat (ctxAfter ctx' res2).regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType v₀2 v₁2 :=
    hres_agree2 hclean2
  have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
    intro ⟨ls, h_etyp⟩
    have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
      simp [h_etyp, opEType?]
    rw [hnone] at h_op; cases h_op
  have hnotref2 : ¬ ∃ ls, res2.qualType.etyp = ETyp.ref ls := by
    intro ⟨ls, h_etyp⟩
    have hnone : opEType? op res1.qualType.etyp res2.qualType.etyp = none := by
      simp [h_etyp, opEType?]
    rw [hnone] at h_op; cases h_op
  have hnonfun_args :
      res1.qualType.etyp.isFunctionType = false ∧
      res2.qualType.etyp.isFunctionType = false ∧
      result_etyp.isFunctionType = false :=
    opEType_implies_nonfun op res1.qualType.etyp res2.qualType.etyp result_etyp h_op
  have hv1Eq : v₀1 = v₁1 :=
    agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hnonfun_args.1 hagree_v1
  have hv2Eq : v₀2 = v₁2 :=
    agreeValueUnder_nonref_eq_of_clean hclean2 hnotref2 hnonfun_args.2.1 hagree_v2
  have hEval₁' : LeanPoison.evalOp op v₀1 v₀2 = some o₁ := by
    simpa [hv1Eq, hv2Eq] using h_evalop₁
  have hEq : o₀ = o₁ := by
    have : some o₀ = some o₁ := by
      calc some o₀ = LeanPoison.evalOp op v₀1 v₀2 := by symm; exact h_evalop₀
           _ = some o₁ := hEval₁'
    exact Option.some.inj this
  have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
    intro ⟨ls, h_etyp⟩
    have h_etyp' : result_etyp = ETyp.ref ls := by simpa [h_ret_etyp] using h_etyp
    have h_op' : opEType? op res1.qualType.etyp res2.qualType.etyp = some (ETyp.ref ls) := by
      simpa [h_etyp'] using h_op
    exact (opEType_ne_ref op res1.qualType.etyp res2.qualType.etyp ls) h_op'
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    simpa [h_ret_etyp] using hnonfun_args.2.2
  exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq

-- World-free version of stepFRW_unaryop
private lemma stepFR_unaryop
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (op : UnaryOp) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.unaryop op e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.unaryop op e) res predSat tm := by
  have htc' : typecheckUnaryOp .ioFree ctxᵢ op e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_unaryop_succ] at htc
    exact htc
  obtain ⟨res1, result_etyp, htc1, h_op, h_mem, h_tag, h_loc, h_ntag, h_regime, h_ret_etyp, h_ret_poison, h_ret_pred⟩ :=
    typecheckUnaryOp_structure ctxᵢ op e (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm res1 htc1'
  -- Use world-free inversion lemma for unaryop
  have hstruct₀ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', v₀', ht₀_e, h_evalop₀, hmem₀, hvar₀, _hnext₀, _hpure₀⟩
  have hstruct₁ := terminatesTo_unaryop_inv' .ioFree op e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', v₁', ht₁_e, h_evalop₁, hmem₁, hvar₁, _hnext₁, _hpure₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' v₀' v₁'
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨hresTm_e, hstep_e⟩
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, _hvtyp₀, _hvtyp₁, _hTm, hwf', _hwfcf₀', _hwfcf₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e⟩
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime]
  -- IH gives agreeOnClean with output regime (ctxAfter ctxᵢ res1).regime = res1.regime'
  -- Since ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 (for unaryop), regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  -- IH gives regimeConsistentWithCtx with output regime
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using hreg'
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hcwr₀'
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hcwr₁'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.unaryop op e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hnonfun_arg :
        res1.qualType.etyp.isFunctionType = false ∧
        result_etyp.isFunctionType = false :=
      opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using hnonfun_arg.2
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_ret_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun_res hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · -- valueHasETyp θ₀' o₀ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v₀' o₀ θ₀' res1.qualType.etyp result_etyp h_op h_evalop₀
  · -- valueHasETyp θ₁' o₁ res.qualType.etyp
    rw [h_ret_etyp]
    exact valueHasETyp_of_evalUnaryOp op v₁' o₁ θ₁' res1.qualType.etyp result_etyp h_op h_evalop₁
  · simpa [hctxAfter] using _hTm
  · simpa [hctxAfter] using hwf'
  · -- valueConsistentWithRegime for cf₀
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalUnaryOp op v₀' o₀ θ₀'
              res1.qualType.etyp result_etyp h_op h_evalop₀)
        hnotfun_res')
  · -- valueConsistentWithRegime for cf₁
    have hnotfun_res' : res.qualType.etyp.isFunctionType = false := by
      simpa [h_ret_etyp] using (opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op).2
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_ret_pred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
        (by rw [h_ret_etyp]; exact valueHasETyp_of_evalUnaryOp op v₁' o₁ θ₁'
              res1.qualType.etyp result_etyp h_op h_evalop₁)
        hnotfun_res')
  intro hclean
  have hpoison_res : res.qualType.poison = false := by
    cases hclean with
    | clean hpoison => exact hpoison
    | guard k htag hreg _ =>
        exfalso
        simp [qtypGuardTag, h_ret_pred] at htag
  have hjoin : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
    calc
      joinPoison ctxᵢ.pc res1.qualType.poison = res.qualType.poison := by
        symm
        exact h_ret_poison
      _ = false := by exact hpoison_res
  have hres1_poison : res1.qualType.poison = false :=
    (joinPoison_eq_false hjoin).2
  -- hres_agree_e expects qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType
  have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := by
    exact qtypCleanUnder.clean hres1_poison
  have hagree_v :
      agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType v₀' v₁' :=
    hres_agree_e hclean1
  have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
    intro hcontra
    rcases hcontra with ⟨ls, h_etyp⟩
    have hnone : opUnaryEType? op res1.qualType.etyp = none := by
      simp [h_etyp, opUnaryEType?]
    rw [hnone] at h_op
    cases h_op
  have hnonfun_arg : res1.qualType.etyp.isFunctionType = false ∧ result_etyp.isFunctionType = false :=
    opUnaryEType_implies_nonfun op res1.qualType.etyp result_etyp h_op
  have hvEq : v₀' = v₁' :=
    agreeValueUnder_nonref_eq_of_clean hclean1 hnotref1 hnonfun_arg.1 hagree_v
  have hEval₁' : LeanPoison.evalUnaryOp op v₀' = some o₁ := by
    simpa [hvEq] using h_evalop₁
  have hEq : o₀ = o₁ := by
    have : some o₀ = some o₁ := by
      calc
        some o₀ = LeanPoison.evalUnaryOp op v₀' := by
          symm
          exact h_evalop₀
        _ = some o₁ := by
          exact hEval₁'
    exact Option.some.inj this
  have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
    intro hcontra
    rcases hcontra with ⟨ls, h_etyp⟩
    have h_etyp' : result_etyp = ETyp.ref ls := by
      simpa [h_ret_etyp] using h_etyp
    have h_op' : opUnaryEType? op res1.qualType.etyp = some (ETyp.ref ls) := by
      simpa [h_etyp'] using h_op
    exact (opUnaryEType_ne_ref op res1.qualType.etyp ls) h_op'
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    simpa [h_ret_etyp] using hnonfun_arg.2
  exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref hEq

private lemma stepFRSingleRunFinalCleanPcTrue_newRef
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFRSingleRunFinalCleanPcTrue .ioFree ctxᵢ (Expr.newRef e) res predSat tm := by
  classical
  have htc' : typecheckNewRef .ioFree ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, l, htc1, hl, h_etyp1, h_etyp, _h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht hpc
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm res1 htc1'
  have hstruct := terminatesTo_newRef_inv' .ioFree e
    { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } cf o rfl ht
  rcases hstruct with ⟨cfg', n, ht_e, ho, hmem, _hnext, hvar, _hpm⟩
  rcases
    hIH hpredlaws hwfTm μ ρ θ cfg' (Value.num n)
      hθwf hwf hric hregCtx hRbound hcwr a pm hwfcfg ht_e hpc
    with ⟨θ1, hθext1, hvnum1, hTm1, hwf1, hwfcfg1, hric1, hreg1, hcwr1, _hvalc1, hpres1⟩
  have hθ1wf : wfRealizationMap θ1 := hθext1.2 hθwf
  have hregime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime := by
    simp [ctxAfter, h_regime]
  let θ' := θ1.update l cfg'.nextAddr
  let storedQt : QTyp :=
    ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison,
      if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  have h_fresh : θ1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by
      simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg'.memory cfg'.varEnv θ1 l hwf1 hric1 hge
  have hθext' : wfExtendsMap θ1 θ' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst h_eq
        rw [h_fresh] at hlookup
        cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp
          have : l = l' := LawfulEqCmp.eq_of_compare hcmp
          exact h_eq this.symm
        have h_theta_def : θ' = θ1.insert l cfg'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]
        simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]
        exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a0 hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ1.get? l' ≠ some cfg'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ1.lookup l' = some cfg'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]
          exact h_eq
        have h_contains : cfg'.memory.contains cfg'.nextAddr := (hric1.1 l' cfg'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a0, θ1.get? k₁ = some a0 → θ1.get? k₂ = some a0 → k₁ = k₂ := by
        intro k₁ k₂ a0 h1 h2
        exact hWF k₁ k₂ a0 h1 h2
      have hlookup1' : (θ1.insert l cfg'.nextAddr).get? l₁ = some a0 := hlookup1
      have hlookup2' : (θ1.insert l cfg'.nextAddr).get? l₂ = some a0 := hlookup2
      exact
        ExtTreeMap_insert_preserves_injectivity
          θ1 l cfg'.nextAddr h_fresh_value' h_inj' l₁ l₂ a0 hlookup1' hlookup2'
  have hθext : wfExtendsMap θ θ' := wfExtendsMap_trans hθext1 hθext'
  have hEnvTm_res1 : EnvRespectsTagMeaning tm ctxᵢ.varEnv res1.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using hTm1
  have hstored_qtyp : QTypRespectsTagMeaning tm storedQt := by
    have hnotfun : storedQt.etyp.isFunctionType = false := by
      simp [storedQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? storedQt = none := by
      simp [storedQt, hpc, qtypGuardDesc?]
    intro qt k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm storedQt hnotfun hguard) hinq hqd
  have hEnvTm_res : EnvRespectsTagMeaning tm ctxᵢ.varEnv res.memEnv' := by
    have hEnvTm_upd :
        EnvRespectsTagMeaning tm ctxᵢ.varEnv (updateMemEnv res1.memEnv' l storedQt) := by
      exact
        EnvRespectsTagMeaning_updateMemEnv
          tm ctxᵢ.varEnv res1.memEnv' l storedQt
          (by simp [storedQt]) hEnvTm_res1 hstored_qtyp
    simpa [h_mem, storedQt] using hEnvTm_upd
  have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) := by
    intro l' hcontains
    simp [ctxAfter] at hcontains ⊢
    rw [h_mem] at hcontains
    rw [h_loc]
    by_cases h_eq : l' = l
    · subst h_eq
      rw [hl]
      exact Nat.lt_succ_self res1.nextLoc'
    · have hmem' : l' ∈ updateMemEnv res1.memEnv' l storedQt :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have h_isSome : ((updateMemEnv res1.memEnv' l storedQt)[l']?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem'
      have h_cmp_ne : compare l l' ≠ Ordering.eq := by
        intro hcmp
        have : l = l' := LawfulEqCmp.eq_of_compare hcmp
        exact h_eq this.symm
      have h_isSome' : (res1.memEnv'[l']?).isSome = true := by
        simpa [storedQt, updateMemEnv, ExtTreeMap.getElem?_insert, h_cmp_ne] using h_isSome
      have hmem_old : l' ∈ res1.memEnv' := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 h_isSome'
      have hcontains_old : res1.memEnv'.contains l' = true := (Std.ExtTreeMap.contains_iff_mem).2 hmem_old
      have hlt : l' < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l' = true := by
          simpa [ctxAfter] using hcontains_old
        exact hwf1 l' this
      exact Nat.lt_succ_of_lt hlt
  have hric_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    unfold runtimeInstantiatesCtx
    rcases hric1 with ⟨hmem1, hvars1⟩
    constructor
    · intro l' a' hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a' = cfg'.nextAddr := by
          have hself : θ'.lookup l = some cfg'.nextAddr := by
            simp [θ', RealizationMap.update, RealizationMap.lookup]
          have : (some a' : Option Address) = some cfg'.nextAddr := by
            calc
              some a' = θ'.lookup l := by symm; exact hlookup
              _ = some cfg'.nextAddr := hself
          exact Option.some.inj this
        subst a'
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by
            rw [h_mem]
            simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf.memory.contains cfg'.nextAddr := by
          rw [hmem]
          simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hlookup_old : θ1.lookup l' = some a' := by
          simpa [θ', RealizationMap_lookup_update_ne h_eq] using hlookup
        have hmem_old := hmem1 l' a' hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by
          simpa [ctxAfter] using hmem_old.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]
            simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf.memory.contains a' := by
          have hμ1 : cfg'.memory.contains a' := hmem_old.2
          rw [hmem, ExtTreeMap.contains_insert]
          simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      have hlookup1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars1 hlookup1
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar] using hvlookup
      · exact valueHasETyp_extends hθext'.1 hvtyp
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [ctxAfter, h_regime, h_tag, h_ntag] using hreg1
  have hqtypPredHolds_mem :
      ∀ (qt : QTyp) (v : Value),
        qtypPredHolds predSat qt cfg'.memory v ↔ qtypPredHolds predSat qt cf.memory v := by
    intro qt v
    exact qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ1 cfg'.memory cf.memory qt v
  have hcwr_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf.memory cf.varEnv θ' := by
    constructor
    · intro l0 qt k hlookup hguard hkR
      by_cases h_eq : l0 = l
      · subst l0
        have hlookup' : res.memEnv'.lookup l = some qt := by
          simpa [ctxAfter] using hlookup
        rw [h_mem] at hlookup'
        have hqt : qt = storedQt := by
          have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
            simp [storedQt, updateMemEnv, MemoryTypeEnv.lookup]
          have : (some qt : Option QTyp) = some storedQt := by
            calc
              some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by
                symm
                exact hlookup'
              _ = some storedQt := hself
          exact Option.some.inj this
        subst hqt
        exact locsRegime.noPred_ok (l, storedQt) (by simp [storedQt, hpc, qtypGuardTag])
      · have hlookup_res1 : res1.memEnv'.lookup l0 = some qt := by
          have hlookup' : res.memEnv'.lookup l0 = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          rw [MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq] at hlookup'
          exact hlookup'
        have hkR1 : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hregime_eq] using hkR
        have hloc := hcwr1.1 l0 qt k (by simpa [ctxAfter] using hlookup_res1) hguard hkR1
        cases hloc with
        | noPred_ok hpred =>
            exact locsRegime.noPred_ok (l0, qt) hpred
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l0, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a_old n_old b hclos hreg hreal hmem_old hcons =>
            have hreal' : θ'.lookup l0 = some a_old := by
              simpa [θ', RealizationMap_lookup_update_ne h_eq] using hreal
            have hcontains_addr : cfg'.memory.contains a_old = true := Memory_contains_of_lookup hmem_old
            have hneq_addr : a_old ≠ cfg'.nextAddr := by
              intro haeq
              subst haeq
              exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr hcontains_addr)
            have hmem_same : cf.memory.lookup a_old = cfg'.memory.lookup a_old := by
              rw [hmem]
              simpa [Memory.update] using
                (Memory_lookup_update_ne (μ := cfg'.memory) (a := a_old) (a' := cfg'.nextAddr) (v := n) hneq_addr)
            have hmem_final : cf.memory.lookup a_old = some n_old := by
              rw [hmem_same]
              exact hmem_old
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq] using hreg
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf.memory (Value.num n_old)) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf.memory (Value.num n_old)) := by
              constructor
              · intro hb
                exact (hqtypPredHolds_mem qt (Value.num n_old)).1 (hcons.1 hb)
              · intro hb hholds
                exact (hcons.2 hb) ((hqtypPredHolds_mem qt (Value.num n_old)).2 hholds)
            exact
              locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a_old n_old b
                hclos hreg' hreal' hmem_final hcons'
    constructor
    · intro x qt k hlookup hguard hkR
      have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hkR1 : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hvars := hcwr1.2.1 x qt k hlookup_old hguard hkR1
      cases hvars with
      | noPred_ok hpred =>
          exact varsRegime.noPred_ok (x, qt) hpred
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar_old hcons =>
          have hvar' : cf.varEnv.lookup x = some v := by
            simpa [hvar] using hvar_old
          have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
            simpa [hregime_eq] using hreg
          have hcons' :
              (b = true → qtypPredHolds predSat qt cf.memory v) ∧
              (b = false → ¬ qtypPredHolds predSat qt cf.memory v) := by
            constructor
            · intro hb
              exact (hqtypPredHolds_mem qt v).1 (hcons.1 hb)
            · intro hb hholds
              exact (hcons.2 hb) ((hqtypPredHolds_mem qt v).2 hholds)
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hvar' hcons'
    · intro x qt v hlookup hlookup_v
      have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hlookup_v_old : cfg'.varEnv.lookup x = some v := by
        simpa [hvar] using hlookup_v
      have hcap :
          closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime qt cfg'.memory θ1 v := by
        rw [hregime_eq]
        exact hcwr1.2.2 x qt v hlookup_old hlookup_v_old
      exact closureCapturedVarsRegime_transport_μ_θ hqtypPredHolds_mem hθext'.1 hcap
  have hclean_back :
      ∀ l0 qt_in qt_out,
        ctxᵢ.memEnv.lookup l0 = some qt_in →
        res.memEnv'.lookup l0 = some qt_out →
        qtypCleanUnder res.regime' qt_out →
        ∃ qt_mid, res1.memEnv'.lookup l0 = some qt_mid ∧ qtypCleanUnder res1.regime' qt_mid := by
    intro l0 qt_in qt_out hlookup_in hlookup_out hclean_out
    by_cases h_eq : l0 = l
    · subst l0
      have hcontains_in : ctxᵢ.memEnv.contains l = true :=
        memEnv_contains_of_lookup_some ctxᵢ.memEnv l qt_in hlookup_in
      have hlt_ctx : l < ctxᵢ.nextLoc := hwf l hcontains_in
      have hmono_next : ctxᵢ.nextLoc ≤ res1.nextLoc' :=
        typecheck_nextLoc_mono ctxᵢ e fuel' res1 htc1'
      have hlt_res1 : l < res1.nextLoc' := Nat.lt_of_lt_of_le hlt_ctx hmono_next
      have : False := by simp [hl] at hlt_res1
      exact this.elim
    · have hlookup_mid : res1.memEnv'.lookup l0 = some qt_out := by
        rw [h_mem] at hlookup_out
        rw [MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq] at hlookup_out
        exact hlookup_out
      have hclean_mid : qtypCleanUnder res1.regime' qt_out := by
        simpa [h_regime] using hclean_out
      exact ⟨qt_out, hlookup_mid, hclean_mid⟩
  have hwrite_pres :
      PreservesInheritedFinalCleanLocsOneRun (ctxAfter ctxᵢ res1) res cfg'.memory cf.memory θ1 θ' := by
    refine ⟨?_⟩
    intro l0 qt_in qt_out hlookup_in _hlookup_out _hclean_out
    by_cases h_eq : l0 = l
    · subst l0
      have hcontains_mid : res1.memEnv'.contains l = true :=
        memEnv_contains_of_lookup_some res1.memEnv' l qt_in hlookup_in
      have hlt_mid : l < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l = true := by
          simpa [ctxAfter] using hcontains_mid
        exact hwf1 l this
      have : False := by simp [hl] at hlt_mid
      exact this.elim
    · cases hθ1lookup : θ1.lookup l0 with
      | none =>
          have hθout : θ'.lookup l0 = none := by
            simpa [θ', RealizationMap_lookup_update_ne h_eq] using hθ1lookup
          exact .both_unrealized hθ1lookup hθout
      | some a_old =>
          have hcontains_addr : cfg'.memory.contains a_old = true := by
            exact (hric1.1 l0 a_old hθ1lookup).2
          rcases Memory_lookup_some_of_contains hcontains_addr with ⟨n_old, hlookup_mem_in⟩
          have hneq_addr : a_old ≠ cfg'.nextAddr := by
            intro haeq
            subst haeq
            exact Nat.lt_irrefl cfg'.nextAddr (hwfcfg1.1 cfg'.nextAddr hcontains_addr)
          have hθout : θ'.lookup l0 = some a_old := by
            simpa [θ', RealizationMap_lookup_update_ne h_eq] using hθ1lookup
          have hmem_same : cf.memory.lookup a_old = cfg'.memory.lookup a_old := by
            rw [hmem]
            simpa [Memory.update] using
              (Memory_lookup_update_ne (μ := cfg'.memory) (a := a_old) (a' := cfg'.nextAddr) (v := n) hneq_addr)
          have hlookup_mem_out : cf.memory.lookup a_old = some n_old := by
            rw [hmem_same]
            exact hlookup_mem_in
          exact .preserve_value a_old n_old hθ1lookup hlookup_mem_in hθout hlookup_mem_out
  have hpres_final :
      PreservesInheritedFinalCleanLocsOneRun ctxᵢ res μ cf.memory θ θ' := by
    exact
      PreservesInheritedFinalCleanLocsOneRun.compose
        (ctx := ctxᵢ) (res1 := res1) (res2 := res)
        hclean_back hpres1 hwrite_pres
  have hvaltyp_final : valueHasETyp θ' o res.qualType.etyp := by
    subst ho
    rw [h_etyp]
    have hlookup : θ'.lookup l = some cfg'.nextAddr := by
      simp [θ', RealizationMap.update, RealizationMap.lookup]
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  have hTm_final : wfTagMeaningCtx tm (ctxAfter ctxᵢ res) := by
    exact wfTagMeaningCtx_ctxAfter tm ctxᵢ res hEnvTm_res
  have hvalc_final :
      valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime res.qualType cf.memory θ' o := by
    subst ho
    refine valueConsistentWithRegime.noTag ?_ ?_
    · simp [qtypGuardTag, h_pred]
    · exact
        .intro (.nonClosure
          (by intro xp body ρcap h; simp at h)
          (by intro xp body ρcap h; simp at h))
  have hwfcfg_final : wfConfig cf := by
    exact (wfConfig_preserved .ioFree (Expr.newRef e) _ cf o ht hwfcfg).1
  refine
    ⟨θ', hθext, hvaltyp_final, hTm_final, hwf_final, hwfcfg_final,
      hric_final, hreg_final, hcwr_final, hvalc_final, hpres_final⟩

private lemma joinMemEnvsStrong_lookup_cleanUnder_left_of_contains
    (env1 env2 : MemoryTypeEnv) (R1 R2 : Regime) (l : Loc) (qt : QTyp)
    (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
    (hclean_join : qtypCleanUnder (joinRegimes R1 R2) qt)
    (hcontains1 : env1.contains l) :
    ∃ qt1, env1.lookup l = some qt1 ∧ qtypCleanUnder R1 qt1 := by
  rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
  cases hclean_join with
  | clean hpoison =>
      have henv1 : env1.lookup l ≠ none := by
        intro hnone
        rw [hlookup1] at hnone
        contradiction
      rcases joinMemEnvsStrong_lookup_clean_left env1 env2 l qt hlookup_join hpoison henv1 with
        ⟨qt1', hlookup1', _hetyp, hpoison1'⟩
      exact ⟨qt1', hlookup1', qtypCleanUnder.clean hpoison1'⟩
  | guard k htag hk _hnotfun =>
      have htag1 : qtypGuardTag qt1 = some k :=
        joinMemEnvsStrong_lookup_guardTag_left env1 env2 l qt qt1 k hlookup_join hlookup1 htag
      have hk1 : R1.lookup? k = some true :=
        joinRegimes_lookup_some_left R1 R2 k true hk
      have hnotfun1 : qt1.etyp.isFunctionType = false := by
        rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1]
        native_decide
      exact ⟨qt1, hlookup1, qtypCleanUnder.guard k htag1 hk1 hnotfun1⟩

private lemma joinMemEnvsStrong_lookup_cleanUnder_right_of_contains
    (env1 env2 : MemoryTypeEnv) (R1 R2 : Regime) (l : Loc) (qt : QTyp)
    (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
    (hclean_join : qtypCleanUnder (joinRegimes R1 R2) qt)
    (hcontains2 : env2.contains l) :
    ∃ qt2, env2.lookup l = some qt2 ∧ qtypCleanUnder R2 qt2 := by
  rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
  cases hclean_join with
  | clean hpoison =>
      have henv2 : env2.lookup l ≠ none := by
        intro hnone
        rw [hlookup2] at hnone
        contradiction
      rcases joinMemEnvsStrong_lookup_clean_right env1 env2 l qt hlookup_join hpoison henv2 with
        ⟨qt2', hlookup2', _hetyp, hpoison2'⟩
      exact ⟨qt2', hlookup2', qtypCleanUnder.clean hpoison2'⟩
  | guard k htag hk _hnotfun =>
      have htag2 : qtypGuardTag qt2 = some k :=
        joinMemEnvsStrong_lookup_guardTag_right env1 env2 l qt qt2 k hlookup_join hlookup2 htag
      have hk2 : R2.lookup? k = some true :=
        joinRegimes_lookup_some_right R1 R2 k true hk
      have hnotfun2 : qt2.etyp.isFunctionType = false := by
        rw [memEnv_lookup_etyp_int env2 l qt2 hlookup2]
        native_decide
      exact ⟨qt2, hlookup2, qtypCleanUnder.guard k htag2 hk2 hnotfun2⟩

-- World-free version of stepFRW_newRef
private lemma stepFR_newRef
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.newRef e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.newRef e) res predSat tm := by
  -- Parse typecheck result
  have htc' : typecheckNewRef .ioFree ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, l, htc1, hl, h_etyp1, h_etyp, h_poison, h_pred, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckNewRef_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm res1 htc1'
  -- Use world-free inversion lemma for newRef
  have hstruct₀ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ rfl ht₀
  rcases hstruct₀ with ⟨cfg₀', n₀, ht₀_e, ho₀, hmem₀, hnext₀, hvar₀, hpm₀⟩
  have hstruct₁ := terminatesTo_newRef_inv' .ioFree e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ rfl ht₁
  rcases hstruct₁ with ⟨cfg₁', n₁, ht₁_e, ho₁, hmem₁, hnext₁, hvar₁, hpm₁⟩
  -- Apply IH for e
  have hstep_e :=
    hIH hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.num n₀) (Value.num n₁)
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨hresTm1, hstep_e⟩
  rcases hstep_e with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e⟩
  -- Derive regime equality: newRef preserves regime (res.regime' = res1.regime')
  -- From typecheckNewRef_structure, we already have h_regime
  -- This gives us (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime
  have hregime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctxᵢ res1).regime := by
    simp [ctxAfter, h_regime]
  -- Fresh logical location l = res1.nextLoc' is not realized after evaluating e
  have h_fresh₀ : θ₀1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg₀'.memory cfg₀'.varEnv θ₀1 l hwf1 hric₀1 hge
  have h_fresh₁ : θ₁1.lookup l = none := by
    have hge : l ≥ (ctxAfter ctxᵢ res1).nextLoc := by simp [ctxAfter, hl]
    exact freshLoc_not_realized (ctxAfter ctxᵢ res1) cfg₁'.memory cfg₁'.varEnv θ₁1 l hwf1 hric₁1 hge
  -- Extended maps: θ₀' = θ₀1.update l cfg₀'.nextAddr, θ₁' = θ₁1.update l cfg₁'.nextAddr
  let θ₀' := θ₀1.update l cfg₀'.nextAddr
  let θ₁' := θ₁1.update l cfg₁'.nextAddr
  -- Prove wfExtendsMap for the extended maps
  have hθext₀' : wfExtendsMap θ₀1 θ₀' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst h_eq; rw [h_fresh₀] at hlookup; cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have h_theta_def : θ₀' = θ₀1.insert l cfg₀'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]; simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]; exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ₀1.get? l' ≠ some cfg₀'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ₀1.lookup l' = some cfg₀'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]; exact h_eq
        have h_contains : cfg₀'.memory.contains cfg₀'.nextAddr := (hric₀1.1 l' cfg₀'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg₀'.nextAddr (hwfcf₀1.1 cfg₀'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a, θ₀1.get? k₁ = some a → θ₀1.get? k₂ = some a → k₁ = k₂ := by
        intro k₁ k₂ a h1 h2; exact hWF k₁ k₂ a h1 h2
      have hlookup1' : (θ₀1.insert l cfg₀'.nextAddr).get? l₁ = some a := hlookup1
      have hlookup2' : (θ₀1.insert l cfg₀'.nextAddr).get? l₂ = some a := hlookup2
      exact ExtTreeMap_insert_preserves_injectivity θ₀1 l cfg₀'.nextAddr h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
  have hθext₁' : wfExtendsMap θ₁1 θ₁' := by
    refine ⟨?_, ?_⟩
    · intro l' a' hlookup
      simp [RealizationMap.lookup]
      by_cases h_eq : l' = l
      · subst l'; rw [h_fresh₁] at hlookup; cases hlookup
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have h_theta_def : θ₁' = θ₁1.insert l cfg₁'.nextAddr := rfl
        rw [h_theta_def, ExtTreeMap.getElem?_insert]; simp [hcmp]
        simp [RealizationMap.lookup] at hlookup
        rw [← ExtTreeMap.get?_eq_getElem?]; exact hlookup
    · intro hWF
      simp only [wfRealizationMap] at hWF ⊢
      unfold RealizationMap.isInjective
      intro l₁ l₂ a hlookup1 hlookup2
      have h_fresh_value' : ∀ l', θ₁1.get? l' ≠ some cfg₁'.nextAddr := by
        intro l' h_eq
        have h_lookup : θ₁1.lookup l' = some cfg₁'.nextAddr := by
          rw [RealizationMap.lookup, ExtTreeMap.get?_eq_getElem?]; exact h_eq
        have h_contains : cfg₁'.memory.contains cfg₁'.nextAddr := (hric₁1.1 l' cfg₁'.nextAddr h_lookup).2
        exact Nat.lt_irrefl cfg₁'.nextAddr (hwfcf₁1.1 cfg₁'.nextAddr h_contains)
      have h_inj' : ∀ k₁ k₂ a, θ₁1.get? k₁ = some a → θ₁1.get? k₂ = some a → k₁ = k₂ := by
        intro k₁ k₂ a h1 h2; exact hWF k₁ k₂ a h1 h2
      have hlookup1' : (θ₁1.insert l cfg₁'.nextAddr).get? l₁ = some a := hlookup1
      have hlookup2' : (θ₁1.insert l cfg₁'.nextAddr).get? l₂ = some a := hlookup2
      exact ExtTreeMap_insert_preserves_injectivity θ₁1 l cfg₁'.nextAddr h_fresh_value' h_inj' l₁ l₂ a hlookup1' hlookup2'
  -- Prove wfTypeContext for result
  have hwf_result : wfTypeContext (ctxAfter ctxᵢ res) := by
    intro l' hcontains
    simp [ctxAfter] at hcontains ⊢
    rw [h_mem] at hcontains
    rw [h_loc]
    by_cases h_eq : l' = l
    · subst h_eq; rw [hl]; exact Nat.lt_succ_self res1.nextLoc'
    · have hmem : l' ∈ updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩ :=
        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have h_isSome : ((updateMemEnv res1.memEnv' l ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩)[l']?).isSome = true :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      have h_cmp_ne : compare l l' ≠ Ordering.eq := by
        intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
      have h_isSome' : (res1.memEnv'[l']?).isSome = true := by
        simpa [updateMemEnv, ExtTreeMap.getElem?_insert, h_cmp_ne] using h_isSome
      have hmem' : l' ∈ res1.memEnv' := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 h_isSome'
      have hcontains' : res1.memEnv'.contains l' = true := (Std.ExtTreeMap.contains_iff_mem).2 hmem'
      have hlt : l' < res1.nextLoc' := by
        have : (ctxAfter ctxᵢ res1).memEnv.contains l' := by simpa [ctxAfter] using hcontains'
        exact hwf1 l' this
      exact Nat.lt_succ_of_lt hlt
  -- Prove runtimeInstantiatesCtx for θ₀'
  have hric₀' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    unfold runtimeInstantiatesCtx
    rcases hric₀1 with ⟨hmem₀1, hvars₀1⟩
    constructor
    · intro l' a hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a = cfg₀'.nextAddr := by
          have hself : θ₀'.lookup l = some cfg₀'.nextAddr := by simp [θ₀', RealizationMap.update, RealizationMap.lookup]
          have : (some a : Option Address) = some cfg₀'.nextAddr := by
            calc some a = θ₀'.lookup l := by symm; exact hlookup
                 _ = some cfg₀'.nextAddr := by exact hself
          exact Option.some.inj this
        subst a
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by rw [h_mem]; simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf₀.memory.contains cfg₀'.nextAddr := by
          rw [hmem₀]; simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have hlookup_old : θ₀1.lookup l' = some a := by
          have hget : (θ₀1.insert l cfg₀'.nextAddr).get? l' = some a := by
            simpa [θ₀', RealizationMap.update, RealizationMap.lookup] using hlookup
          have hElem : (θ₀1.insert l cfg₀'.nextAddr)[l']? = some a := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hget
          have hElem2 : θ₀1[l']? = some a := by simpa [ExtTreeMap.getElem?_insert, hcmp] using hElem
          have : θ₀1.get? l' = some a := by simpa [ExtTreeMap.get?_eq_getElem?] using hElem2
          simpa [RealizationMap.lookup] using this
        have hmem := hmem₀1 l' a hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by simpa [ctxAfter] using hmem.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]; simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf₀.memory.contains a := by
          have hμ1 : cfg₀'.memory.contains a := hmem.2
          rw [hmem₀, ExtTreeMap.contains_insert]; simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₀1 (by simpa [ctxAfter] using hlookup)
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar₀] using hvlookup
      · exact valueHasETyp_extends hθext₀'.1 hvtyp
  -- Prove runtimeInstantiatesCtx for θ₁'
  have hric₁' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    unfold runtimeInstantiatesCtx
    rcases hric₁1 with ⟨hmem₁1, hvars₁1⟩
    constructor
    · intro l' a hlookup
      by_cases h_eq : l' = l
      · subst l'
        have ha : a = cfg₁'.nextAddr := by
          have hself : θ₁'.lookup l = some cfg₁'.nextAddr := by simp [θ₁', RealizationMap.update, RealizationMap.lookup]
          have : (some a : Option Address) = some cfg₁'.nextAddr := by
            calc some a = θ₁'.lookup l := by symm; exact hlookup
                 _ = some cfg₁'.nextAddr := by exact hself
          exact Option.some.inj this
        subst a
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l := by
          have : res.memEnv'.contains l := by rw [h_mem]; simp [updateMemEnv, ExtTreeMap.contains_insert]
          simpa [ctxAfter] using this
        have hμ_mem : cf₁.memory.contains cfg₁'.nextAddr := by
          rw [hmem₁]; simp [ExtTreeMap.contains_insert]
        exact ⟨hctx_mem, hμ_mem⟩
      · have hcmp : compare l l' ≠ Ordering.eq := by
          intro hcmp; have : l = l' := LawfulEqCmp.eq_of_compare hcmp; exact h_eq this.symm
        have hlookup_old : θ₁1.lookup l' = some a := by
          have hget : (θ₁1.insert l cfg₁'.nextAddr).get? l' = some a := by
            simpa [θ₁', RealizationMap.update, RealizationMap.lookup] using hlookup
          have hElem : (θ₁1.insert l cfg₁'.nextAddr)[l']? = some a := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hget
          have hElem2 : θ₁1[l']? = some a := by simpa [ExtTreeMap.getElem?_insert, hcmp] using hElem
          have : θ₁1.get? l' = some a := by simpa [ExtTreeMap.get?_eq_getElem?] using hElem2
          simpa [RealizationMap.lookup] using this
        have hmem := hmem₁1 l' a hlookup_old
        have hctx_mem1 : res1.memEnv'.contains l' := by simpa [ctxAfter] using hmem.1
        have hctx_mem : (ctxAfter ctxᵢ res).memEnv.contains l' := by
          have : res.memEnv'.contains l' := by
            rw [h_mem, updateMemEnv, ExtTreeMap.contains_insert]; simp [hctx_mem1]
          simpa [ctxAfter] using this
        have hμ_mem : cf₁.memory.contains a := by
          have hμ1 : cfg₁'.memory.contains a := hmem.2
          rw [hmem₁, ExtTreeMap.contains_insert]; simp [hμ1]
        exact ⟨hctx_mem, hμ_mem⟩
    · intro x qt hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁1 (by simpa [ctxAfter] using hlookup)
      refine ⟨v, ?_, ?_⟩
      · simpa [hvar₁] using hvlookup
      · exact valueHasETyp_extends hθext₁'.1 hvtyp
  -- Prove regimeConsistentWithCtx (IH gives with output regime)
  have hreg' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    -- htagR1 gives regimeConsistentWithCtx (ctxAfter ctxᵢ res1); use hregime_eq to transfer
    unfold regimeConsistentWithCtx
    rw [hregime_eq]
    simpa [ctxAfter, h_tag, h_ntag] using htagR1
  -- Prove agreeOnClean (using output regime from IH)
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    rw [hregime_eq]
    have hqtypPredHolds_mem₀ :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v :=
      qtypPredHolds_mem_compat_of_predSatLaws
        (hpredlaws := hpredlaws) (θ := θ₀1) (μ := cfg₀'.memory) (μ' := cf₀.memory)
    have hqtypPredHolds_mem₁ :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v :=
      qtypPredHolds_mem_compat_of_predSatLaws
        (hpredlaws := hpredlaws) (θ := θ₁1) (μ := cfg₁'.memory) (μ' := cf₁.memory)
    exact agreeOnClean_newRef_extend
      predSat (ctxAfter ctxᵢ res1).regime ctxᵢ res1 res l ETyp.int
      cfg₀' cfg₁' cf₀ cf₁ n₀ n₁ cfg₀'.nextAddr cfg₁'.nextAddr θ₀1 θ₁1 θ₀' θ₁'
      h_mem h_etyp1 rfl rfl rfl hmem₀ hmem₁ hvar₀ hvar₁ rfl rfl
      hθext₀' hθext₁' hwfcf₀1 hwfcf₁1 hqtypPredHolds_mem₀ hqtypPredHolds_mem₁
      hagree_clean_e hres_agree_e
  -- Derive wfConfig for final configs
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.newRef e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  -- consistentWithRegime for extended realization maps
  -- Key insight: res.regime' = res1.regime' (newRef doesn't change regime)
  -- For newRef:
  -- 1. New location l has a fresh address with storedQt whose pred is gated by ctxᵢ.pc
  -- 2. Old locations transfer from hcwr₀1/hcwr₁1
  -- 3. VarEnv is unchanged
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    classical
    let storedQt : QTyp :=
      ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
    have hPredSat_mem :
        ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
      intro k μ μ' v
      exact predSat_mem_noPred_compat hpredlaws θ₀1 k μ μ' v
    have hqtypPredHolds_mem :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₀'.memory v ↔ qtypPredHolds predSat qt cf₀.memory v := by
      intro qt v
      constructor
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cf₀.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).1 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cf₀.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).1 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cfg₀'.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).2 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cfg₀'.memory v :=
              (hPredSat_mem _ cfg₀'.memory cf₀.memory v).2 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
    constructor
    · intro l0 qt k hlookup hguard hkR
      by_cases h_eq : l0 = l
      · subst l0
        have hqt : qt = storedQt := by
          have hlookup' : res.memEnv'.lookup l = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
            simp [updateMemEnv, storedQt, MemoryTypeEnv.lookup]
          have : (some qt : Option QTyp) = some storedQt := by
            calc
              some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by symm; exact hlookup'
              _ = some storedQt := by exact hself
          exact Option.some.inj this
        subst hqt
        -- New logical location: realized at the freshly allocated address.
        have hreal : θ₀'.lookup l = some cfg₀'.nextAddr := by
          simp [θ₀', RealizationMap.update, RealizationMap.lookup]
        have hmem_new : cf₀.memory.lookup cfg₀'.nextAddr = some n₀ := by
          rw [hmem₀]
          simp [Memory.lookup]
        cases hpred_case : storedQt.pred with
        | noPred =>
            -- Contradiction: no guard tag.
            have hnone : qtypGuardTag storedQt = none := by
              simp [qtypGuardTag, hpred_case]
            have hne : (none : Option Tag) ≠ some k := by simp
            exact (hne (hnone.symm.trans hguard)).elim
        | guardOnly k0 =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            exact locsRegime.guardOnly_ok (l, storedQt) k (by simpa [storedQt, hpred_case])
        | guardClosure k0 arg_name pred_body var_env =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            -- Determine the regime's boolean for k.
            cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
            | none =>
                exact (hkR hk).elim
            | some b =>
                have hval0 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                      res1.qualType cfg₀'.memory θ₀1 (Value.num n₀) := by
                  simpa [hregime_eq] using _hval_consist₀
                have hpc_false : ctxᵢ.pc = false := by
                  cases hpc : ctxᵢ.pc with
                  | false => exact rfl
                  | true =>
                      simp [storedQt, hpc] at hpred_case
                have hpred_res1 :
                    res1.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                  simpa [storedQt, hpc_false] using hpred_case
                have htag_res1 : qtypGuardTag res1.qualType = some k := by
                  simp [qtypGuardTag, hpred_res1]
                have hpredEq : res1.qualType.pred = storedQt.pred := by
                  simp [storedQt, hpc_false]
                have hconsist_old :
                      (b = true → qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀)) := by
                    cases hb : b with
                    | true =>
                        have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                          simpa [hb] using hk
                        have hholds_res1 :
                            qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) := by
                          cases hval0 with
                          | noTag hnotag =>
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeTrue k' htag hkR' hholds =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              -- hkR' must match hktrue
                              have : some true = some true := by
                                calc
                                  some true = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some true := hktrue
                              exact hholds
                          | inRegimeFalse k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              -- Contradiction with hktrue
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by simpa using hkR'
                              simp [this] at hktrue
                        have hholds_stored_old :
                            qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀) :=
                          qtypPredHolds_transport_pred (predSat := predSat) (qt := res1.qualType) (qt' := storedQt)
                            (μ := cfg₀'.memory) (v := Value.num n₀) hpredEq hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro _; exact hholds_stored_old
                        · intro hbfalse; cases hbfalse
                    | false =>
                        have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                          simpa [hb] using hk
                        have hnot_res1 :
                            ¬ qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) := by
                          cases hval0 with
                          | noTag hnotag =>
                              intro _
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeFalse k' htag hkR' hnot =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some false = some false := by
                                calc
                                  some false = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some false := hkfalse
                              exact hnot
                          | inRegimeTrue k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by simpa using hkR'
                              simp [this] at hkfalse
                        have hnot_stored_old :
                            ¬ qtypPredHolds predSat storedQt cfg₀'.memory (Value.num n₀) := by
                          intro hholds_stored
                          have hholds_res1 :
                              qtypPredHolds predSat res1.qualType cfg₀'.memory (Value.num n₀) :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := storedQt) (qt' := res1.qualType)
                              (μ := cfg₀'.memory) (v := Value.num n₀) (by simp [hpredEq]) hholds_stored
                          exact hnot_res1 hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro hbtrue; cases hbtrue
                        · intro _; exact hnot_stored_old
                have hconsist :
                    (b = true → qtypPredHolds predSat storedQt cf₀.memory (Value.num n₀)) ∧
                    (b = false → ¬ qtypPredHolds predSat storedQt cf₀.memory (Value.num n₀)) := by
                  constructor
                  · intro hbtrue
                    have hholds_old := hconsist_old.1 hbtrue
                    exact (hqtypPredHolds_mem storedQt (Value.num n₀)).1 hholds_old
                  · intro hbfalse hholds_new
                    have hholds_old := (hqtypPredHolds_mem storedQt (Value.num n₀)).2 hholds_new
                    exact (hconsist_old.2 hbfalse) hholds_old
                exact
                  locsRegime.withPred_ok (l, storedQt) k arg_name pred_body var_env cfg₀'.nextAddr n₀ b
                    (by simpa [storedQt, hpred_case]) hk hreal hmem_new hconsist
      · -- Old location: use IH and transport across the realization-map/memory updates.
        have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l0 = some qt := by
          have hlookup' : res.memEnv'.lookup l0 = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hEq :
              (updateMemEnv res1.memEnv' l storedQt).lookup l0 = res1.memEnv'.lookup l0 :=
            MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq
          have hlookup_old' : res1.memEnv'.lookup l0 = some qt := by
            have htmp := hlookup'
            rw [hEq] at htmp
            exact htmp
          simpa [ctxAfter] using hlookup_old'
        have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hregime_eq] using hkR
        have hloc := hcwr₀1.1 l0 qt k hlookup_old hguard hkR_old
        -- Rebuild locsRegime for the updated θ/memory.
        cases hloc with
        | noPred_ok hnp =>
            exact locsRegime.noPred_ok (l0, qt) hnp
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l0, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
            have hreal' : θ₀'.lookup l0 = some a := by
              -- θ₀' differs from θ₀1 only at l.
              have := RealizationMap_lookup_update_ne (θ := θ₀1) (l := l) (l' := l0) (addr := cfg₀'.nextAddr) h_eq
              simpa [θ₀', this] using hreal
            have hne : a ≠ cfg₀'.nextAddr := by
              intro hcontra
              have hcontains : cfg₀'.memory.contains cfg₀'.nextAddr := by
                have : cfg₀'.memory.contains a := Memory_contains_of_lookup hmem
                simpa [hcontra] using this
              exact (nextAddr_not_in_memory cfg₀' hwfcf₀1) hcontains
            have hmem' : cf₀.memory.lookup a = some n := by
              have hmem₀' : cf₀.memory = Memory.update cfg₀'.memory cfg₀'.nextAddr n₀ := by
                simpa [Memory.update] using hmem₀
              rw [hmem₀']
              rw [Memory_lookup_update_ne (μ := cfg₀'.memory) (a := a) (a' := cfg₀'.nextAddr) (v := n₀) hne]
              exact hmem
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf₀.memory (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₀.memory (Value.num n)) := by
              constructor
              · intro hbtrue
                have hholds_old := hcons.1 hbtrue
                exact (hqtypPredHolds_mem qt (Value.num n)).1 hholds_old
              · intro hbfalse hholds_new
                have hholds_old := (hqtypPredHolds_mem qt (Value.num n)).2 hholds_new
                exact (hcons.2 hbfalse) hholds_old
            have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq.symm] using hreg
            exact locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
    constructor
    · intro x qt k hlookup hguard hkR
      have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hvars := hcwr₀1.2.1 x qt k (by simpa [ctxAfter] using hlookup) hguard hkR_old
      cases hvars with
      | noPred_ok hnp =>
          exact varsRegime.noPred_ok (x, qt) hnp
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
          have hcons' :
              (b = true → qtypPredHolds predSat qt cf₀.memory v) ∧
              (b = false → ¬ qtypPredHolds predSat qt cf₀.memory v) := by
            constructor
            · intro hbtrue
              have hholds_old := hcons.1 hbtrue
              exact (hqtypPredHolds_mem qt v).1 hholds_old
            · intro hbfalse hholds_new
              have hholds_old := (hqtypPredHolds_mem qt v).2 hholds_new
              exact (hcons.2 hbfalse) hholds_old
          have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
            simpa [hregime_eq.symm] using hreg
          have hvar' : cf₀.varEnv.lookup (x, qt).1 = some v := by
            simpa [hvar₀] using hvar
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregR hvar' hcons'
    · intro x qt v hlookup hlookup_v
      have hlookup_res1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hlookup_v_old : cfg₀'.varEnv.lookup x = some v := by
        simpa [hvar₀] using hlookup_v
      have hcap := hcwr₀1.2.2 x qt v hlookup_res1 hlookup_v_old
      rw [← hregime_eq] at hcap
      exact closureCapturedVarsRegime_transport_μ_θ hqtypPredHolds_mem hθext₀'.1 hcap
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    classical
    let storedQt : QTyp :=
      ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
    have hPredSat_mem :
        ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v := by
      intro k μ μ' v
      exact predSat_mem_noPred_compat hpredlaws θ₁1 k μ μ' v
    have hqtypPredHolds_mem :
        ∀ (qt : QTyp) (v : Value),
          qtypPredHolds predSat qt cfg₁'.memory v ↔ qtypPredHolds predSat qt cf₁.memory v := by
      intro qt v
      constructor
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cf₁.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).1 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cf₁.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).1 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
      · intro h
        cases h with
        | noPred_ok hpred =>
            exact qtypPredHolds.noPred_ok hpred
        | guardClosure_ok hpred hSat =>
            have hSat' : predSat _ cfg₁'.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).2 hSat
            exact qtypPredHolds.guardClosure_ok hpred hSat'
        | guardOnly_ok hpred hSat =>
            have hSat' : predSat _ cfg₁'.memory v :=
              (hPredSat_mem _ cfg₁'.memory cf₁.memory v).2 hSat
            exact qtypPredHolds.guardOnly_ok hpred hSat'
    constructor
    · intro l0 qt k hlookup hguard hkR
      by_cases h_eq : l0 = l
      · subst l0
        have hqt : qt = storedQt := by
          have hlookup' : res.memEnv'.lookup l = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hself : (updateMemEnv res1.memEnv' l storedQt).lookup l = some storedQt := by
            simp [updateMemEnv, storedQt, MemoryTypeEnv.lookup]
          have : (some qt : Option QTyp) = some storedQt := by
            calc
              some qt = (updateMemEnv res1.memEnv' l storedQt).lookup l := by symm; exact hlookup'
              _ = some storedQt := by exact hself
          exact Option.some.inj this
        subst hqt
        have hreal : θ₁'.lookup l = some cfg₁'.nextAddr := by
          simp [θ₁', RealizationMap.update, RealizationMap.lookup]
        have hmem_new : cf₁.memory.lookup cfg₁'.nextAddr = some n₁ := by
          rw [hmem₁]
          simp [Memory.lookup]
        cases hpred_case : storedQt.pred with
        | noPred =>
            have hnone : qtypGuardTag storedQt = none := by
              simp [qtypGuardTag, hpred_case]
            have hne : (none : Option Tag) ≠ some k := by simp
            exact (hne (hnone.symm.trans hguard)).elim
        | guardOnly k0 =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            exact locsRegime.guardOnly_ok (l, storedQt) k (by simpa [storedQt, hpred_case])
        | guardClosure k0 arg_name pred_body var_env =>
            have hk0 : k0 = k := by
              have htag : qtypGuardTag storedQt = some k := by simpa using hguard
              have : some k0 = some k := by simpa [qtypGuardTag, hpred_case] using htag
              exact Option.some.inj this
            subst k0
            cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
            | none =>
                exact (hkR hk).elim
              | some b =>
                  have hval1 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                        res1.qualType cfg₁'.memory θ₁1 (Value.num n₁) := by
                    simpa [hregime_eq] using _hval_consist₁
                  have hpc_false : ctxᵢ.pc = false := by
                    cases hpc : ctxᵢ.pc with
                    | false => exact rfl
                    | true =>
                        simp [storedQt, hpc] at hpred_case
                  have hpred_res1 :
                      res1.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
                    simpa [storedQt, hpc_false] using hpred_case
                  have htag_res1 : qtypGuardTag res1.qualType = some k := by
                    simp [qtypGuardTag, hpred_res1]
                  have hpredEq : res1.qualType.pred = storedQt.pred := by
                    simp [storedQt, hpc_false]
                  have hconsist_old :
                      (b = true → qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁)) := by
                    cases hb : b with
                    | true =>
                        have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                          simpa [hb] using hk
                        have hholds_res1 :
                            qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) := by
                          cases hval1 with
                          | noTag hnotag =>
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeTrue k' htag hkR' hholds =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some true = some true := by
                                calc
                                  some true = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some true := hktrue
                              exact hholds
                          | inRegimeFalse k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by simpa using hkR'
                              simp [this] at hktrue
                        have hholds_stored_old :
                            qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁) :=
                          qtypPredHolds_transport_pred (predSat := predSat) (qt := res1.qualType) (qt' := storedQt)
                            (μ := cfg₁'.memory) (v := Value.num n₁) hpredEq hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro _; exact hholds_stored_old
                        · intro hbfalse; cases hbfalse
                    | false =>
                        have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                          simpa [hb] using hk
                        have hnot_res1 :
                            ¬ qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) := by
                          cases hval1 with
                          | noTag hnotag =>
                              intro _
                              have : (none : Option Tag) ≠ some k := by simp
                              exact (this (hnotag.symm.trans htag_res1)).elim
                          | guardOnly_ok _k hgo =>
                              cases (hpred_res1.symm.trans hgo)
                          | notInRegime k' htag hnone =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              exact (hkR (by simpa using hnone)).elim
                          | inRegimeFalse k' htag hkR' hnot =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : some false = some false := by
                                calc
                                  some false = (ctxAfter ctxᵢ res).regime.lookup? k := by symm; exact hkR'
                                  _ = some false := hkfalse
                              exact hnot
                          | inRegimeTrue k' htag hkR' _ =>
                              have hk' : k' = k := by
                                have : some k' = some k := by
                                  calc
                                    some k' = qtypGuardTag res1.qualType := by symm; exact htag
                                    _ = some k := htag_res1
                                exact Option.some.inj this
                              subst k'
                              have : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by simpa using hkR'
                              simp [this] at hkfalse
                        have hnot_stored_old :
                            ¬ qtypPredHolds predSat storedQt cfg₁'.memory (Value.num n₁) := by
                          intro hholds_stored
                          have hholds_res1 :
                              qtypPredHolds predSat res1.qualType cfg₁'.memory (Value.num n₁) :=
                            qtypPredHolds_transport_pred (predSat := predSat) (qt := storedQt) (qt' := res1.qualType)
                              (μ := cfg₁'.memory) (v := Value.num n₁) (by simp [hpredEq]) hholds_stored
                          exact hnot_res1 hholds_res1
                        refine ⟨?_, ?_⟩
                        · intro hbtrue; cases hbtrue
                        · intro _; exact hnot_stored_old
                  have hconsist :
                      (b = true → qtypPredHolds predSat storedQt cf₁.memory (Value.num n₁)) ∧
                      (b = false → ¬ qtypPredHolds predSat storedQt cf₁.memory (Value.num n₁)) := by
                    constructor
                    · intro hbtrue
                      have hholds_old := hconsist_old.1 hbtrue
                      exact (hqtypPredHolds_mem storedQt (Value.num n₁)).1 hholds_old
                    · intro hbfalse hholds_new
                      have hholds_old := (hqtypPredHolds_mem storedQt (Value.num n₁)).2 hholds_new
                      exact (hconsist_old.2 hbfalse) hholds_old
                  exact
                    locsRegime.withPred_ok (l, storedQt) k arg_name pred_body var_env cfg₁'.nextAddr n₁ b
                      (by simpa [storedQt, hpred_case]) hk hreal hmem_new hconsist
      · have hlookup_old : (ctxAfter ctxᵢ res1).memEnv.lookup l0 = some qt := by
          have hlookup' : res.memEnv'.lookup l0 = some qt := by
            simpa [ctxAfter] using hlookup
          rw [h_mem] at hlookup'
          have hEq :
              (updateMemEnv res1.memEnv' l storedQt).lookup l0 = res1.memEnv'.lookup l0 :=
            MemoryTypeEnv_lookup_updateMemEnv_ne (Γ := res1.memEnv') (l := l) (l' := l0) (qt := storedQt) h_eq
          have hlookup_old' : res1.memEnv'.lookup l0 = some qt := by
            have htmp := hlookup'
            rw [hEq] at htmp
            exact htmp
          simpa [ctxAfter] using hlookup_old'
        have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hregime_eq] using hkR
        have hloc := hcwr₁1.1 l0 qt k hlookup_old hguard hkR_old
        cases hloc with
        | noPred_ok hnp =>
            exact locsRegime.noPred_ok (l0, qt) hnp
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l0, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b hclos hreg hreal hmem hcons =>
            have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hregime_eq.symm] using hreg
            have hreal' : θ₁'.lookup l0 = some a := by
              have :=
                RealizationMap_lookup_update_ne
                  (θ := θ₁1) (l := l) (l' := l0) (addr := cfg₁'.nextAddr) h_eq
              simpa [θ₁', this] using hreal
            have hne : a ≠ cfg₁'.nextAddr := by
              intro hcontra
              have hcontains : cfg₁'.memory.contains cfg₁'.nextAddr := by
                have : cfg₁'.memory.contains a := Memory_contains_of_lookup hmem
                simpa [hcontra] using this
              exact (nextAddr_not_in_memory cfg₁' hwfcf₁1) hcontains
            have hmem' : cf₁.memory.lookup a = some n := by
              have hmem₁' : cf₁.memory = Memory.update cfg₁'.memory cfg₁'.nextAddr n₁ := by
                simpa [Memory.update] using hmem₁
              rw [hmem₁']
              rw [Memory_lookup_update_ne (μ := cfg₁'.memory) (a := a) (a' := cfg₁'.nextAddr) (v := n₁) hne]
              exact hmem
            have hcons' :
                (b = true → qtypPredHolds predSat qt cf₁.memory (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₁.memory (Value.num n)) := by
              constructor
              · intro hbtrue
                have hholds_old := hcons.1 hbtrue
                exact (hqtypPredHolds_mem qt (Value.num n)).1 hholds_old
              · intro hbfalse hholds_new
                have hholds_old := (hqtypPredHolds_mem qt (Value.num n)).2 hholds_new
                exact (hcons.2 hbfalse) hholds_old
            exact locsRegime.withPred_ok (l0, qt) k' arg_name pred_body var_env a n b hclos hregR hreal' hmem' hcons'
    constructor
    · intro x qt k hlookup hguard hkR
      have hkR_old : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hregime_eq] using hkR
      have hvars := hcwr₁1.2.1 x qt k (by simpa [ctxAfter] using hlookup) hguard hkR_old
      cases hvars with
      | noPred_ok hnp =>
          exact varsRegime.noPred_ok (x, qt) hnp
      | guardOnly_ok k' hgo =>
          exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env v b hclos hreg hvar hcons =>
          have hregR : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
            simpa [hregime_eq.symm] using hreg
          have hcons' :
              (b = true → qtypPredHolds predSat qt cf₁.memory v) ∧
              (b = false → ¬ qtypPredHolds predSat qt cf₁.memory v) := by
            constructor
            · intro hbtrue
              have hholds_old := hcons.1 hbtrue
              exact (hqtypPredHolds_mem qt v).1 hholds_old
            · intro hbfalse hholds_new
              have hholds_old := (hqtypPredHolds_mem qt v).2 hholds_new
              exact (hcons.2 hbfalse) hholds_old
          have hvar' : cf₁.varEnv.lookup x = some v := by
            simpa [hvar₁] using hvar
          exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregR hvar' hcons'
    · intro x qt v hlookup hlookup_v
      have hlookup_res1 : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
        simpa [ctxAfter] using hlookup
      have hlookup_v_old : cfg₁'.varEnv.lookup x = some v := by
        simpa [hvar₁] using hlookup_v
      have hcap := hcwr₁1.2.2 x qt v hlookup_res1 hlookup_v_old
      rw [← hregime_eq] at hcap
      exact closureCapturedVarsRegime_transport_μ_θ hqtypPredHolds_mem hθext₁'.1 hcap
  let storedQt : QTyp := ⟨ETyp.int, joinPoison ctxᵢ.pc res1.qualType.poison, if ctxᵢ.pc = true then Predicate.noPred else res1.qualType.pred⟩
  have hres1_desc :
      ∀ {qt k d}, QTypInQTyp qt res1.qualType →
        qtypGuardDesc? qt = some (k, d) →
        tm.lookup k = some d := by
    intro qt k d hinq hqd
    exact hresTm1 hinq hqd
  have hstored_desc :
      ∀ {qt k d}, QTypInQTyp qt storedQt →
        qtypGuardDesc? qt = some (k, d) →
        tm.lookup k = some d := by
    intro qt k d hinq hqd
    have hnotfun : storedQt.etyp.isFunctionType = false := by
      simp [storedQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hEq : qt = storedQt := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
    subst hEq
    have hpc_false : ctxᵢ.pc = false := by
      cases hpc : ctxᵢ.pc with
      | false => exact rfl
      | true =>
          simp [storedQt, qtypGuardDesc?, hpc] at hqd
    have hqd' : qtypGuardDesc? res1.qualType = some (k, d) := by
      simpa [storedQt, qtypGuardDesc?, hpc_false] using hqd
    exact hres1_desc (QTypInQTyp.self res1.qualType) hqd'
  have hEnvTm_res1 : EnvRespectsTagMeaning tm ctxᵢ.varEnv res1.memEnv' := by
    simpa [wfTagMeaningCtx, ctxAfter] using _hTm1
  have hEnvTm_res : EnvRespectsTagMeaning tm ctxᵢ.varEnv res.memEnv' := by
    have hEnvTm_upd : EnvRespectsTagMeaning tm ctxᵢ.varEnv (res1.memEnv'.update l storedQt) := by
      exact EnvRespectsTagMeaning_memEnv_ext tm ctxᵢ.varEnv res1.memEnv' l storedQt (by simp [storedQt]) hEnvTm_res1 hstored_desc
    simpa [h_mem, storedQt, updateMemEnv] using hEnvTm_upd
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
      simp [h_etyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, h_pred]
    intro qt' k d hinq hqd
    exact (QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun_res hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀', θ₁', ?_, ?_, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀', hric₁', hreg', hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀'
    exact wfExtendsMap_trans hθext₀1 hθext₀'
  · -- wfExtendsMap θ₁ θ₁'
    exact wfExtendsMap_trans hθext₁1 hθext₁'
  · -- valueHasETyp for run 0
    subst ho₀
    rw [h_etyp]
    have hlookup : θ₀'.lookup l = some cfg₀'.nextAddr := by
      simp [RealizationMap.lookup]
      rw [← ExtTreeMap.get?_eq_getElem?]
      exact ExtTreeMap.getElem?_insert_self
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  · -- valueHasETyp for run 1
    subst ho₁
    rw [h_etyp]
    have hlookup : θ₁'.lookup l = some cfg₁'.nextAddr := by
      simp [RealizationMap.lookup]
      rw [← ExtTreeMap.get?_eq_getElem?]
      exact ExtTreeMap.getElem?_insert_self
    exact valueHasETyp.loc (l := l) hlookup (by simp [LocSet.singleton])
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
    exact wfTagMeaningCtx_ctxAfter tm ctxᵢ res hEnvTm_res
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    exact hwf_result
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_pred])
      (.intro (.nonClosure (by intro xp bd rc h; simp [ho₀] at h)
                           (by intro xp bd rc h; simp [ho₀] at h)))
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, h_pred])
      (.intro (.nonClosure (by intro xp bd rc h; simp [ho₁] at h)
                           (by intro xp bd rc h; simp [ho₁] at h)))
  · -- resultAgreesIfClean
    intro hclean
    have hpoison_res : res.qualType.poison = false := by
      cases hclean with
      | clean hpoison => exact hpoison
      | guard k htag hreg _ =>
          exfalso
          simp [qtypGuardTag, h_pred] at htag
    have hlookup1 : θ₀'.lookup l = some cfg₀'.nextAddr := by
      simp [RealizationMap.lookup]; rw [← ExtTreeMap.get?_eq_getElem?]; exact ExtTreeMap.getElem?_insert_self
    have hlookup2 : θ₁'.lookup l = some cfg₁'.nextAddr := by
      simp [RealizationMap.lookup]; rw [← ExtTreeMap.get?_eq_getElem?]; exact ExtTreeMap.getElem?_insert_self
    have hin1 : l ∈ LocSet.singleton l := by simp [LocSet.singleton]
    exact agreeValueUnder.clean_ref hpoison_res h_etyp hlookup1 hin1 ho₀ hlookup2 ho₁

-- World-free version of stepFRW_seq
private lemma stepFR_seq
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.seq e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.seq e1 e2) res predSat tm := by
  -- Parse typecheck result
  have htc' : typecheckSeq .ioFree ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_seq_succ] at htc
    exact htc
  obtain ⟨res1, ctx', htc1, hctx', htc2⟩ :=
    typecheckSeq_structure ctxᵢ e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  -- Use world-free inversion lemma for seq
  have hstruct₀ := terminatesTo_seq_inv' e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, ht₀_e1, ht₀_e2, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_seq_inv' e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, ht₁_e1, ht₁_e2, hpm₁1, hpm₁2⟩
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1, hres_agree1⟩
  have hwfTm' : wfTagMeaningCtx tm ctx' := by simpa [hctx', ctxAfter] using _hTm1
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res htc2'
  -- Prepare for IH2
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
  -- hric₀1, hric₁1, htagR1 are already extracted from hstep_e1 for (ctxAfter ctxᵢ res1)
  -- Since ctx' = ctxAfter ctxᵢ res1, we convert them
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [hctx', ctxAfter] using hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', ctxAfter] using hric₁1
  have htagR1' : regimeConsistentWithCtx ctx' := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using htagR1
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hcwr₀1
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hcwr₁1
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [hctx', updateCtxFromResult, ctxAfter] using hagree_clean1
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq : cfg₁1 = { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    cases cfg₁1; simp only [Config.mk.injEq, true_and]; exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by rw [← hcfg₁1_eq]; exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr, pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]; exact hwfcf₁1
  -- Apply IH for e2
  -- Note: ctx'.regime = res1.regime' which may differ from ctxᵢ.regime
  -- Use regime monotonicity to relate them
  have h_mono : Regime.monotoneStep ctxᵢ.regime res1.regime' := regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hRbound' : regimeBounded ctx'.regime := by
    have hctx'_regime : ctx'.regime = res1.regime' := by simp [hctx', updateCtxFromResult]
    rw [hctx'_regime]
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound h_mono
  have hstep_e2 :=
    hIH2 hpredlaws hwfTm' cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' htagR1' hRbound' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, hwfcf₀2, hwfcf₁2, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2, hres_agree2⟩
  -- Combine extension maps
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctx' res := by
    simp only [ctxAfter, hctx', updateCtxFromResult]
  -- IH2 gives agreeOnClean with (ctxAfter ctx' res).regime
  -- Since ctxAfter ctxᵢ res = ctxAfter ctx' res, their regimes are equal
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree_clean2
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  -- IH2 gives regimeConsistentWithCtx with output regime, transfer via hctxAfter
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  refine ⟨hresTm2, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2, hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · exact _hvtyp₀2
  · exact _hvtyp₁2
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · -- valueConsistentWithRegime for cf₀
    -- The result of `seq` is exactly the result of `e2`; reuse IH2.
    simpa [hctxAfter] using _hval_consist₀2
  · -- valueConsistentWithRegime for cf₁
    simpa [hctxAfter] using _hval_consist₁2
  -- Since res is directly the result of e2, hres_agree2 gives us the result directly
  -- IH2 gives resultAgreesIfClean with (ctxAfter ctx' res).regime = (ctxAfter ctxᵢ res).regime
  simpa [hctxAfter] using hres_agree2

-- World-free version of stepFRW_vlet
private lemma stepFR_vlet
  (ctxᵢ : TypeContext) (predSat : PredSat)
  (vname : Name) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (tm : TagMeaning) (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.vlet vname e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.vlet vname e1 e2) res predSat tm := by
  -- Parse typecheck result
  have htc' : typecheckVlet .ioFree ctxᵢ vname e1 e2 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr_vlet_succ] at htc
    exact htc
  obtain ⟨res1, res2, ctx', htc1, hctx', htc2, h_ret_etyp, h_mem, h_tag, h_loc, h_ntag,
          h_ret_regime, h_ret_poison, h_ret_pred⟩ :=
    typecheckVlet_structure ctxᵢ vname e1 e2 (Nat.succ fuel') res htc'
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have htc2' : typecheck .ioFree ctx' e2 fuel' = .ok res2 := by
    simpa [hctx', typecheck, Nat.succ_sub_one] using htc2
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  -- Use world-free inversion lemma for vlet
  have hstruct₀ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, v₀1, cfg₀3, ht₀_e1, ht₀_e2, hcf₀_eq, hpm₀1, hpm₀2⟩
  have hstruct₁ := terminatesTo_vlet_inv' vname e1 e2
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, v₁1, cfg₁3, ht₁_e1, ht₁_e2, hcf₁_eq, hpm₁1, hpm₁2⟩
  -- Define intermediate configs with extended varEnv
  let cfg₀2 : Config := { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 }
  let cfg₁2 : Config := { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 }
  -- Apply IH for e1
  have hstep_e1 :=
    hIH1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 v₀1 v₁1
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree_clean1, _hval_consist₀1, _hval_consist₁1, hres_agree1⟩
  have hres1_desc :
      ∀ {qt k d}, QTypInQTyp qt res1.qualType →
        qtypGuardDesc? qt = some (k, d) →
        tm.lookup k = some d := by
    intro qt k d hinq hqd
    exact hresTm1 hinq hqd
  have hwfTm' : wfTagMeaningCtx tm ctx' := by
    simp only [hctx']
    exact wfTagMeaningCtx_varEnv_ext tm (ctxAfter ctxᵢ res1) vname res1.qualType _hTm1 hres1_desc
  have hIH2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctx' hwfTm' res2 htc2'
  -- Prepare for IH2
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf1' : wfTypeContext ctx' := by simpa [hctx', ctxAfter] using hwf1
  have hric₀1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxAfter] using hric₀1
  have hric₁1_mem : runtimeInstantiatesCtx { ctxᵢ with memEnv := res1.memEnv' } cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxAfter] using hric₁1
  -- hv₀1_typed, hv₁1_typed come from IH1 (StepFR now includes valueHasETyp)
  -- wfValue from wfConfig_preservedW (needs terminatesToW)
  let w_default := LeanProofs.defaultWorld
  have ht₀_e1_w : terminatesToW .ioFree w_default w_default e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 v₀1 := by
    rcases ht₀_e1 with ⟨fuel₀, verbose₀, hpure₀⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
    exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
  have ht₁_e1_w : terminatesToW .ioFree w_default w_default e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 v₁1 := by
    rcases ht₁_e1 with ⟨fuel₁, verbose₁, hpure₁⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
    exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
  have hv₀1_wf : wfValue cfg₀1.nextAddr v₀1 :=
    (wfConfig_preservedW .ioFree w_default w_default e1 { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cfg₀1 v₀1 ht₀_e1_w hwfcfg₀).2
  have hv₁1_wf : wfValue cfg₁1.nextAddr v₁1 :=
    (wfConfig_preservedW .ioFree w_default w_default e1 { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cfg₁1 v₁1 ht₁_e1_w hwfcfg₁).2
  have hreg_ctx' : regimeConsistentWithCtx ctx' := by
    -- ctx'.regime = res1.regime', need to derive from htagR1 and regime_monotone
    unfold regimeConsistentWithCtx at htagR1 ⊢
    constructor
    · -- tagEnvConsistentWithRegime ctx'.tagEnv ctx'.regime
      have h_tagEnv_eq : ctx'.tagEnv = (ctxAfter ctxᵢ res1).tagEnv := by simp [hctx', ctxAfter]
      have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
      rw [h_tagEnv_eq, h_regime_eq]
      exact htagR1.1
    · -- res1.regime'.bound ≤ ctx'.nextTag
      simp only [hctx']
      have hbound_eq : res1.regime'.bound = ctxᵢ.regime.bound := (regime_monotone ctxᵢ e1 fuel' res1 htc1').1
      have hctxAfter_nextTag : (ctxAfter ctxᵢ res1).nextTag = res1.nextTag' := by simp [ctxAfter]
      -- htagR1.2 : (ctxAfter ctxᵢ res1).regime.bound ≤ (ctxAfter ctxᵢ res1).nextTag
      -- Since (ctxAfter ctxᵢ res1).regime = res1.regime', and res1.regime'.bound = ctxᵢ.regime.bound
      have h_regime_eq : (ctxAfter ctxᵢ res1).regime = res1.regime' := by simp [ctxAfter]
      rw [hbound_eq]
      calc ctxᵢ.regime.bound = res1.regime'.bound := hbound_eq.symm
           _ = (ctxAfter ctxᵢ res1).regime.bound := by rw [h_regime_eq]
           _ ≤ (ctxAfter ctxᵢ res1).nextTag := htagR1.2
           _ = res1.nextTag' := hctxAfter_nextTag
  -- runtimeInstantiatesCtx for extended configs
  have hric₀1' : runtimeInstantiatesCtx ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
    unfold runtimeInstantiatesCtx at hric₀1 ⊢
    rcases hric₀1 with ⟨hmem₀1, hvars₀1⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₀1 l a hlookup
      simpa [hctx', ctxAfter, cfg₀2] using hmem
    · intro w qt hlookup
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxᵢ.varEnv.update w res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv w res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update w res1.qualType).lookup w := by symm; exact hlookup'
                 _ = some res1.qualType := by exact h
          exact Option.some.inj this
        have hlookup_var : cfg₀2.varEnv.lookup w = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        refine ⟨v₀1, hlookup_var, ?_⟩
        simpa [hqt] using hv₀1_typed
      · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₀1 hlookup_ctx
        have hvlookup' : cfg₀2.varEnv.lookup w = some v := by
          simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname w v₀1 hw] using hvlookup
        exact ⟨v, hvlookup', hvtyp⟩
  have hric₁1' : runtimeInstantiatesCtx ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    unfold runtimeInstantiatesCtx at hric₁1 ⊢
    rcases hric₁1 with ⟨hmem₁1, hvars₁1⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₁1 l a hlookup
      simpa [hctx', ctxAfter, cfg₁2] using hmem
    · intro w qt hlookup
      by_cases hw : w = vname
      · subst hw
        have hlookup' : (ctxᵢ.varEnv.update w res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv w res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update w res1.qualType).lookup w := by symm; exact hlookup'
                 _ = some res1.qualType := by exact h
          exact Option.some.inj this
        have hlookup_var : cfg₁2.varEnv.lookup w = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        refine ⟨v₁1, hlookup_var, ?_⟩
        simpa [hqt] using hv₁1_typed
      · have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup w = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup w = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname w res1.qualType hw] using hlookup'
        obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁1 hlookup_ctx
        have hvlookup' : cfg₁2.varEnv.lookup w = some v := by
          simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname w v₁1 hw] using hvlookup
        exact ⟨v, hvlookup', hvtyp⟩
  -- wfConfig for extended configs
  have hwfcfg₀2 : wfConfig cfg₀2 := by
    rcases hwfcf₀1 with ⟨hwfmem₀, hwfenv₀⟩
    refine ⟨?_, ?_⟩
    · simpa [cfg₀2] using hwfmem₀
    · have hwfenv₀' : wfVarEnv cfg₀1.nextAddr ((vname, v₀1) :: cfg₀1.varEnv) :=
        wfVarEnv.cons vname v₀1 cfg₀1.varEnv hv₀1_wf hwfenv₀
      simpa [cfg₀2, VarEnv.update] using hwfenv₀'
  have hwfcfg₁2 : wfConfig cfg₁2 := by
    rcases hwfcf₁1 with ⟨hwfmem₁, hwfenv₁⟩
    refine ⟨?_, ?_⟩
    · simpa [cfg₁2] using hwfmem₁
    · have hwfenv₁' : wfVarEnv cfg₁1.nextAddr ((vname, v₁1) :: cfg₁1.varEnv) :=
        wfVarEnv.cons vname v₁1 cfg₁1.varEnv hv₁1_wf hwfenv₁
      simpa [cfg₁2, VarEnv.update] using hwfenv₁'
  -- agreeOnClean for extended configs
  -- ctx'.regime = res1.regime' (not ctxᵢ.regime), need monotonicity transfer
  have hagree_clean1' :
      agreeOnClean predSat ctx'.regime ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    constructor
    · -- locs: unchanged memories, and ctx'.memEnv matches ctxAfter ctxᵢ res1
      intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
        simpa [hctx', ctxAfter] using hclean
      have hagree_loc := hagree_clean1.1 l qt hlookup' hclean'
      simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_loc
    · -- vars: old variables come from hagree_clean1; new binding uses result agreement
      intro x qt hlookup hclean
      by_cases hx : x = vname
      · subst x
        have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have : some qt = some res1.qualType := by
            calc
              some qt = (ctxᵢ.varEnv.update vname res1.qualType).lookup vname := by
                symm; exact hlookup'
              _ = some res1.qualType := by
                exact h
          exact Option.some.inj this
        subst hqt
        have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType := by
          simpa [hctx', ctxAfter] using hclean
        have hagree_val :=
          hres_agree1 hclean'
        have hlookup_v₀ : cfg₀2.varEnv.lookup vname = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        have hlookup_v₁ : cfg₁2.varEnv.lookup vname = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        refine agreeVarUnder.agree_values vname res1.qualType v₀1 v₁1 hlookup_v₀ hlookup_v₁ ?_
        simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_val
      · -- x ≠ vname: transport agreeVarUnder through varEnv.update
        have hlookup_update : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_ctx : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_update
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx
        have hclean' : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
          simpa [hctx', ctxAfter] using hclean
        have hagree_var := hagree_clean1.2 x qt hlookup_ctxAfter hclean'
        cases hagree_var with
        | agree_values x qt v₀ v₁ h₀ h₁ hagree_val =>
            have h₀' : cfg₀2.varEnv.lookup x = some v₀ := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using h₀
            have h₁' : cfg₁2.varEnv.lookup x = some v₁ := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using h₁
            exact
              agreeVarUnder.agree_values x qt v₀ v₁ h₀' h₁'
                (by simpa [cfg₀2, cfg₁2, hctx', ctxAfter] using hagree_val)
        | both_none x qt h₀ h₁ =>
            have h₀' : cfg₀2.varEnv.lookup x = none := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using h₀
            have h₁' : cfg₁2.varEnv.lookup x = none := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using h₁
            exact agreeVarUnder.both_none x qt h₀' h₁'
  -- Handle pureMode for IH2
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₀2_eq : cfg₀2 = { cfg₀1 with varEnv := cfg₀1.varEnv.update vname v₀1 } := rfl
  have hcfg₁2_eq : cfg₁2 = { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 } := rfl
  -- Convert ht₁_e2 to have matching pureMode
  have ht₁_e2' : terminatesTo .ioFree e2 { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } cfg₁3 o₁ := by
    have hcfg_eq : ({ cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1 } : Config) =
                   { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
      simp [hpm_eq]
    rw [← hcfg_eq]; exact ht₁_e2
  -- wfConfig for cfg₁2 with adjusted pureMode
  have hwfcfg₁2' : wfConfig { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
    have hcfg_eq : cfg₁2 = { cfg₁1 with varEnv := cfg₁1.varEnv.update vname v₁1, pureMode := cfg₀1.pureMode } := by
      simp [cfg₁2, hpm_eq]
    rw [← hcfg_eq]; exact hwfcfg₁2
  -- Apply IH for e2
  -- ctx'.regime = res1.regime' (from hctx'), use regime_monotone for properties
  have h_mono_vlet := regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hRbound_ctx' : regimeBounded ctx'.regime := by
    have h : ctx'.regime = res1.regime' := by simp [hctx']
    rw [h]
    exact regimeBounded_of_monotoneStep ctxᵢ.regime res1.regime' hRbound h_mono_vlet
  -- Transfer consistentWithRegime from IH1 result to ctx'
  -- IH1 gives consistentWithRegime predSat (ctxAfter ctxᵢ res1).regime (ctxAfter ctxᵢ res1) ...
  -- Since ctx' = ctxAfter ctxᵢ res1 (structurally), these match
  have hcwr₀1' : consistentWithRegime predSat ctx'.regime ctx' cfg₀2.memory cfg₀2.varEnv θ₀1 := by
    -- cfg₀2 extends cfg₀1 with updated varEnv
    -- ctx' has same memEnv as (ctxAfter ctxᵢ res1) but extended varEnv
    constructor
    · -- locs: memEnv and memory are the same
      intro l qt k hlookup hguard hregime_k
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hctx', ctxAfter] using hregime_k
      have hlocs := hcwr₀1.1 l qt k hlookup' hguard hregime_k'
      cases hlocs with
      | noPred_ok hpred =>
          exact locsRegime.noPred_ok (l, qt) hpred
      | guardOnly_ok k' hgo =>
          exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env a n b hclos hregime' hreal hmem' hconsist =>
          have hmem'' : cfg₀2.memory.lookup a = some n := by
            simpa [cfg₀2] using hmem'
          have hregime'' : ctx'.regime.lookup? k' = some b := by
            simpa [hctx', ctxAfter] using hregime'
          exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregime'' hreal hmem'' hconsist
    constructor
    · -- vars: old variables transfer, new variable from IH1 result
      intro x qt k hlookup hguard hregime_k
      by_cases hx : x = vname
      · -- Case: x = vname (new binding)
        subst hx
        have hlookup_res1 : (ctxᵢ.varEnv.update x res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hqt : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv x res1.qualType
          have : some qt = some res1.qualType := by
            calc
              some qt = (ctxᵢ.varEnv.update x res1.qualType).lookup x := by
                symm; exact hlookup_res1
              _ = some res1.qualType := by
                exact h
          exact Option.some.inj this
        subst hqt
        have hlookup_v : cfg₀2.varEnv.lookup x = some v₀1 := by
          simp [cfg₀2, VarEnv.update, VarEnv.lookup]
        have hval_consist :
            valueConsistentWithRegime predSat ctx'.regime res1.qualType cfg₀2.memory θ₀1 v₀1 := by
          simpa [hctx', ctxAfter, cfg₀2] using _hval_consist₀1
        cases hpred_case : res1.qualType.pred with
        | noPred =>
            have hguard' : qtypGuardTag res1.qualType = none := by
              simp [qtypGuardTag, hpred_case]
            rw [hguard'] at hguard
            cases hguard
        | guardOnly k' =>
            exact varsRegime.guardOnly_ok (x, res1.qualType) k' hpred_case
        | guardClosure k' arg_name pred_body var_env =>
            have htag_k' : qtypGuardTag res1.qualType = some k' := by
              simp [qtypGuardTag, hpred_case]
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                  _ = some k := hguard
              exact Option.some.inj this
            have hkR : ctx'.regime.lookup? k' ≠ none := by
              simpa [hk] using hregime_k
            cases hval_consist with
            | noTag hnone =>
                have : some k' = (none : Option Tag) := by
                  calc
                    some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                    _ = none := hnone
                cases this
            | guardOnly_ok k0 hgo =>
                have : Predicate.guardClosure k' arg_name pred_body var_env = Predicate.guardOnly k0 := by
                  calc
                    Predicate.guardClosure k' arg_name pred_body var_env = res1.qualType.pred := by
                      symm; exact hpred_case
                    _ = Predicate.guardOnly k0 := hgo
                cases this
            | notInRegime k0 htag0 hnone =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have : False := hkR (by simpa [hk0] using hnone)
                cases this
            | inRegimeTrue k0 htag0 hRtrue hholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRtrue' : ctx'.regime.lookup? k' = some true := by
                  simpa [hk0] using hRtrue
                refine
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₀1 true
                    hpred_case hRtrue' hlookup_v ?_
                constructor
                · intro _; exact hholds
                · intro hb; cases hb
            | inRegimeFalse k0 htag0 hRfalse hnholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRfalse' : ctx'.regime.lookup? k' = some false := by
                  simpa [hk0] using hRfalse
                refine
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₀1 false
                    hpred_case hRfalse' hlookup_v ?_
                constructor
                · intro hb; cases hb
                · intro _; exact hnholds
      · -- Case: x ≠ vname (old variable)
        have hlookup_old : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_old' : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_old
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simp [ctxAfter]; exact hlookup_old'
        have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hctx', ctxAfter] using hregime_k
        have hvars := hcwr₀1.2.1 x qt k hlookup_ctxAfter hguard hregime_k'
        cases hvars with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hregime' hlookup_v hconsist =>
            have hlookup_v' : cfg₀2.varEnv.lookup x = some v := by
              simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hlookup_v
            have hregime'' : ctx'.regime.lookup? k' = some b := by
              simpa [hctx', ctxAfter] using hregime'
            have hconsist' : (b = true → qtypPredHolds predSat (x, qt).snd cfg₀2.memory v) ∧
                           (b = false → ¬qtypPredHolds predSat (x, qt).snd cfg₀2.memory v) := by
              have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
              simpa [h_mem_eq] using hconsist
            exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregime'' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: the newly bound variable from e1
        rw [hx] at hlookup hlookup_v
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
            simpa [hctx'] using hlookup
          exact Option.some.inj (hlookup'.symm.trans h)
        have hv_eq : v = v₀1 := by
          have h : cfg₀2.varEnv.lookup vname = some v₀1 := by
            simp [cfg₀2, VarEnv.update, VarEnv.lookup]
          exact Option.some.inj (hlookup_v.symm.trans h)
        subst hqt_eq hv_eq
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
        exact valueConsistentWithRegime_closureCapturedVarsRegime
          (by simpa [h_regime_eq, h_mem_eq] using _hval_consist₀1)
      · -- x ≠ vname: old variable unchanged
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
            have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
              simpa [hctx'] using hlookup
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using this
          simpa [ctxAfter] using hlookup_old
        have hlookup_v_old : cfg₀1.varEnv.lookup x = some v := by
          simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hlookup_v
        have hcap := hcwr₀1.2.2 x qt v hlookup_ctxAfter hlookup_v_old
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₀2.memory = cfg₀1.memory := by simp [cfg₀2]
        rwa [h_regime_eq, h_mem_eq]
  have hcwr₁1' : consistentWithRegime predSat ctx'.regime ctx' cfg₁2.memory cfg₁2.varEnv θ₁1 := by
    -- cfg₁2 extends cfg₁1 with updated varEnv
    constructor
    · -- locs: memEnv and memory are the same
      intro l qt k hlookup hguard hregime_k
      have hlookup' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
        simpa [hctx', ctxAfter] using hlookup
      have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
        simpa [hctx', ctxAfter] using hregime_k
      have hlocs := hcwr₁1.1 l qt k hlookup' hguard hregime_k'
      cases hlocs with
      | noPred_ok hpred =>
          exact locsRegime.noPred_ok (l, qt) hpred
      | guardOnly_ok k' hgo =>
          exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env a n b hclos hregime' hreal hmem' hconsist =>
          have hmem'' : cfg₁2.memory.lookup a = some n := by
            simpa [cfg₁2] using hmem'
          have hregime'' : ctx'.regime.lookup? k' = some b := by
            simpa [hctx', ctxAfter] using hregime'
          have hconsist' : (b = true → qtypPredHolds predSat (l, qt).snd cfg₁2.memory (Value.num n)) ∧
                         (b = false → ¬qtypPredHolds predSat (l, qt).snd cfg₁2.memory (Value.num n)) := by
            have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
            simpa [h_mem_eq] using hconsist
          exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b hclos hregime'' hreal hmem'' hconsist'
    constructor
    · -- vars: old variables transfer, new variable from IH1 result
      intro x qt k hlookup hguard hregime_k
      by_cases hx : x = vname
      · -- Case: x = vname (new binding)
        subst hx
        -- After subst, vname is replaced by x everywhere
        have hlookup_res1 : (ctxᵢ.varEnv.update x res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv x res1.qualType
          have : some qt = some res1.qualType := by
            calc some qt = (ctxᵢ.varEnv.update x res1.qualType).lookup x := by symm; exact hlookup_res1
                 _ = some res1.qualType := h
          exact Option.some.inj this
        subst hqt_eq
        have hlookup_v : cfg₁2.varEnv.lookup x = some v₁1 := by
          simp [cfg₁2, VarEnv.update, VarEnv.lookup]
        cases hpred_case : res1.qualType.pred with
        | noPred =>
            have hguard' : qtypGuardTag res1.qualType = none := by simp [qtypGuardTag, hpred_case]
            rw [hguard'] at hguard; cases hguard
        | guardOnly k' =>
            exact varsRegime.guardOnly_ok (x, res1.qualType) k' hpred_case
        | guardClosure k' arg_name pred_body var_env =>
            -- TODO(vlet/valueConsistentWithRegime): symmetric to the cfg₀2 case above.
            -- We need return-value regime-consistency for `v₁1` to discharge the new-binding
            -- `varsRegime` obligation when the guard tag is in the regime domain.
            have hval_consist :
                valueConsistentWithRegime predSat ctx'.regime res1.qualType cfg₁2.memory θ₁1 v₁1 := by
              simpa [hctx', ctxAfter, cfg₁2] using _hval_consist₁1
            have htag_k' : qtypGuardTag res1.qualType = some k' := by
              simp [qtypGuardTag, hpred_case]
            have hk : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                  _ = some k := hguard
              exact Option.some.inj this
            have hkR : ctx'.regime.lookup? k' ≠ none := by
              simpa [hk] using hregime_k
            cases hval_consist with
            | noTag hnone =>
                have : some k' = (none : Option Tag) := by
                  calc
                    some k' = qtypGuardTag res1.qualType := by symm; exact htag_k'
                    _ = none := hnone
                cases this
            | guardOnly_ok k0 hgo =>
                have : Predicate.guardClosure k' arg_name pred_body var_env = Predicate.guardOnly k0 := by
                  calc
                    Predicate.guardClosure k' arg_name pred_body var_env = res1.qualType.pred := by
                      symm; exact hpred_case
                    _ = Predicate.guardOnly k0 := by
                      exact hgo
                cases this
            | notInRegime k0 htag0 hnone =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have : False := hkR (by simpa [hk0] using hnone)
                cases this
            | inRegimeTrue k0 htag0 hRtrue hholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRtrue' : ctx'.regime.lookup? k' = some true := by
                  simpa [hk0] using hRtrue
                exact
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₁1 true
                    hpred_case hRtrue' hlookup_v
                    ⟨(by intro _; exact hholds), (by intro hb; cases hb)⟩
            | inRegimeFalse k0 htag0 hRfalse hnholds =>
                have hk0 : k0 = k' := by
                  have : some k0 = some k' := by
                    calc
                      some k0 = qtypGuardTag res1.qualType := by symm; exact htag0
                      _ = some k' := htag_k'
                  exact Option.some.inj this
                have hRfalse' : ctx'.regime.lookup? k' = some false := by
                  simpa [hk0] using hRfalse
                exact
                  varsRegime.withPred_ok (x, res1.qualType) k' arg_name pred_body var_env v₁1 false
                    hpred_case hRfalse' hlookup_v
                    ⟨(by intro hb; cases hb), (by intro _; exact hnholds)⟩
      · -- Case: x ≠ vname (old variable)
        have hlookup_old : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
          simpa [hctx'] using hlookup
        have hlookup_old' : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_old
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          simp [ctxAfter]; exact hlookup_old'
        have hregime_k' : (ctxAfter ctxᵢ res1).regime.lookup? k ≠ none := by
          simpa [hctx', ctxAfter] using hregime_k
        have hvars := hcwr₁1.2.1 x qt k hlookup_ctxAfter hguard hregime_k'
        cases hvars with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hregime' hlookup_v hconsist =>
            have hlookup_v' : cfg₁2.varEnv.lookup x = some v := by
              simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hlookup_v
            have hregime'' : ctx'.regime.lookup? k' = some b := by
              simpa [hctx', ctxAfter] using hregime'
            have hconsist' : (b = true → qtypPredHolds predSat (x, qt).snd cfg₁2.memory v) ∧
                           (b = false → ¬qtypPredHolds predSat (x, qt).snd cfg₁2.memory v) := by
              have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
              simpa [h_mem_eq] using hconsist
            exact varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hregime'' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: the newly bound variable from e1
        rw [hx] at hlookup hlookup_v
        have hqt_eq : qt = res1.qualType := by
          have h := VarTypeEnv_lookup_update_eq ctxᵢ.varEnv vname res1.qualType
          have hlookup' : (ctxᵢ.varEnv.update vname res1.qualType).lookup vname = some qt := by
            simpa [hctx'] using hlookup
          exact Option.some.inj (hlookup'.symm.trans h)
        have hv_eq : v = v₁1 := by
          have h : cfg₁2.varEnv.lookup vname = some v₁1 := by
            simp [cfg₁2, VarEnv.update, VarEnv.lookup]
          exact Option.some.inj (hlookup_v.symm.trans h)
        subst hqt_eq hv_eq
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
        exact valueConsistentWithRegime_closureCapturedVarsRegime
          (by simpa [h_regime_eq, h_mem_eq] using _hval_consist₁1)
      · -- x ≠ vname: old variable unchanged
        have hlookup_ctxAfter : (ctxAfter ctxᵢ res1).varEnv.lookup x = some qt := by
          have hlookup_old : ctxᵢ.varEnv.lookup x = some qt := by
            have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
              simpa [hctx'] using hlookup
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using this
          simpa [ctxAfter] using hlookup_old
        have hlookup_v_old : cfg₁1.varEnv.lookup x = some v := by
          simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hlookup_v
        have hcap := hcwr₁1.2.2 x qt v hlookup_ctxAfter hlookup_v_old
        have h_regime_eq : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by
          simp [hctx', ctxAfter]
        have h_mem_eq : cfg₁2.memory = cfg₁1.memory := by simp [cfg₁2]
        rwa [h_regime_eq, h_mem_eq]
  have hstep_e2 :=
    hIH2 hpredlaws hwfTm' cfg₀2.memory cfg₁2.memory cfg₀2.varEnv cfg₁2.varEnv θ₀1 θ₁1
      cfg₀3 cfg₁3 o₀ o₁
      hθ₀1wf hθ₁1wf hwf1' hric₀1' hric₁1' hreg_ctx' hRbound_ctx' hcwr₀1' hcwr₁1' hagree_clean1'
      cfg₀2.nextAddr cfg₁2.nextAddr cfg₀2.pureMode hwfcfg₀2 hwfcfg₁2'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, hwfcf₀3, hwfcf₁3, hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree_clean2, _hval_consist₀2, _hval_consist₁2, hres_agree2⟩
  -- Combine map extensions
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  -- VarEnv preservation through e2
  have ht₀_e2_w : terminatesToW .ioFree w_default w_default e2 cfg₀2 cfg₀3 o₀ := by
    rcases ht₀_e2 with ⟨fuel₀, verbose₀, hpure₀⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₀
    exact ⟨fuel₀, verbose₀, by simpa [pure] using h_eq⟩
  have ht₁_e2_w : terminatesToW .ioFree w_default w_default e2 cfg₁2 cfg₁3 o₁ := by
    rcases ht₁_e2 with ⟨fuel₁, verbose₁, hpure₁⟩
    have h_eq := LeanProofs.evalAtWorld_eq w_default hpure₁
    exact ⟨fuel₁, verbose₁, by simpa [pure] using h_eq⟩
  have hvar_pres₀ : cfg₀3.varEnv = cfg₀2.varEnv := by
    symm
    rcases ht₀_e2_w with ⟨fuel₀', verbose₀', heval₀⟩
    exact beval_preserves_varEnv .ioFree e2 fuel₀' verbose₀' cfg₀2 cfg₀3 o₀ ⟨w_default, w_default, heval₀⟩
  have hvar_pres₁ : cfg₁3.varEnv = cfg₁2.varEnv := by
    symm
    rcases ht₁_e2_w with ⟨fuel₁', verbose₁', heval₁⟩
    exact beval_preserves_varEnv .ioFree e2 fuel₁' verbose₁' cfg₁2 cfg₁3 o₁ ⟨w_default, w_default, heval₁⟩
  -- Final runtimeInstantiatesCtx
  have hric₀'' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    unfold runtimeInstantiatesCtx
    rcases hric₀2 with ⟨hmem₂, _hvars₂⟩
    rcases hric₀1 with ⟨_hmem₁, hvars₁⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₂ l a hlookup
      simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcf₀_eq] using hmem
    · intro u qt hlookup
      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
      have hvlookup' : cf₀.varEnv.lookup u = some v := by
        simpa [hcf₀_eq] using hvlookup
      have hvtyp' : valueHasETyp θ₀2 v qt.etyp := valueHasETyp_extends hθext₀2.1 hvtyp
      exact ⟨v, hvlookup', hvtyp'⟩
  have hric₁'' : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    unfold runtimeInstantiatesCtx
    rcases hric₁2 with ⟨hmem₂, _hvars₂⟩
    rcases hric₁1 with ⟨_hmem₁, hvars₁⟩
    constructor
    · intro l a hlookup
      have hmem := hmem₂ l a hlookup
      simpa [ctxAfter, h_mem, h_tag, h_loc, h_ntag, hcf₁_eq] using hmem
    · intro u qt hlookup
      have hlookup' : (ctxAfter ctxᵢ res1).varEnv.lookup u = some qt := by
        simpa [ctxAfter] using hlookup
      obtain ⟨v, hvlookup, hvtyp⟩ := hvars₁ hlookup'
      have hvlookup' : cf₁.varEnv.lookup u = some v := by
        simpa [hcf₁_eq] using hvlookup
      have hvtyp' : valueHasETyp θ₁2 v qt.etyp := valueHasETyp_extends hθext₁2.1 hvtyp
      exact ⟨v, hvlookup', hvtyp'⟩
  -- ctx'.regime = res1.regime' (not ctxᵢ.regime)
  -- With new StepFR using output regime, we need (ctxAfter ctxᵢ res).regime
  have hreg'' : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    -- IH2 gives regimeConsistentWithCtx (ctxAfter ctx' res2) (ctxAfter ctx' res2).regime
    -- The relevant fields match by structure lemma
    have h_tagEnv_eq : (ctxAfter ctxᵢ res).tagEnv = (ctxAfter ctx' res2).tagEnv := by simp [ctxAfter, h_tag]
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by simp [ctxAfter, h_ret_regime]
    have h_nextTag_eq : (ctxAfter ctxᵢ res).nextTag = (ctxAfter ctx' res2).nextTag := by simp [ctxAfter, h_ntag]
    unfold regimeConsistentWithCtx at htagR2 ⊢
    constructor
    · rw [h_tagEnv_eq, h_regime_eq]; exact htagR2.1
    · rw [h_regime_eq, h_nextTag_eq]; exact htagR2.2
  -- Final agreeOnClean (using output regime)
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    -- IH2 gives agreeOnClean for extended context, but TypeResult doesn't include varEnv'
    -- So (ctxAfter ctxᵢ res).varEnv = ctxᵢ.varEnv (original, NOT extended)
    -- And (ctxAfter ctx' res2).varEnv = ctx'.varEnv (extended with vname)
    -- Runtime: cf₀.varEnv = cfg₀1.varEnv (restored), not the extended cfg₀2.varEnv
    have h_mem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
    have h_mem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
    have h_var₀_eq : cf₀.varEnv = cfg₀1.varEnv := by simp [hcf₀_eq]
    have h_var₁_eq : cf₁.varEnv = cfg₁1.varEnv := by simp [hcf₁_eq]
    have h_mem_eq : (ctxAfter ctxᵢ res).memEnv = (ctxAfter ctx' res2).memEnv := by simp [ctxAfter, h_mem]
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by simp [ctxAfter, h_ret_regime]
    constructor
    · -- locs: memEnv matches by structure lemma
      intro l qt hlookup hclean
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by simpa [h_mem_eq] using hlookup
      have hclean' : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by simpa [h_regime_eq] using hclean
      have hagree_loc := hagree_clean2.1 l qt hlookup' hclean'
      have hagree_loc' : agreeLocUnder predSat (ctxAfter ctxᵢ res).regime cfg₀3.memory cfg₁3.memory θ₀2 θ₁2 (l, qt) := by
        simpa [h_regime_eq] using hagree_loc
      simpa [h_mem₀_eq, h_mem₁_eq] using hagree_loc'
    · -- vars: Complex - varEnv is restored, needs careful reasoning about variable shadowing
      intro x qt hlookup hclean
      -- Helper: clean-under is preserved backwards along a regime monotone step (entries can only be dropped).
      have cleanUnder_of_monotone {R R' : Regime} {qt : QTyp} :
          Regime.monotoneStep R R' → qtypCleanUnder R' qt → qtypCleanUnder R qt := by
        intro h_mono h_clean
        cases h_clean with
        | clean hpoison =>
            exact qtypCleanUnder.clean hpoison
        | guard k htag hkR' hnotfun =>
            -- Since R'.lookup? k = some true, monotonicity implies R.lookup? k = some true as well.
            have hRdef : R.lookup? k ≠ none := h_mono.2.2 k (by simp [hkR'])
            cases hkR : R.lookup? k with
            | none => exact (hRdef hkR).elim
            | some b =>
                have h_cases := h_mono.2.1 k b hkR
                cases h_cases with
                | inl hkR'_preserved =>
                    have hb : b = true := by
                      have : some b = some true := hkR'_preserved.symm.trans hkR'
                      exact Option.some.inj this
                    subst hb
                    exact qtypCleanUnder.guard k htag hkR hnotfun
                | inr hkR'_none =>
                    -- Contradiction: hkR' says R'.lookup? k = some true.
                    simp [hkR'_none] at hkR'
      -- Helper: transfer agreeValueUnder across a monotone regime step, assuming the type is clean under the target.
      -- We prove this by induction on agreement; the recursor provides the needed IH for captured environments.
      have agreeValueUnder_clean_monotoneRegime
          {R R' : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
          Regime.monotoneStep R R' →
            qtypCleanUnder R' qt →
              agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
                agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
        intro h_mono hclean hagree
        -- Strengthen the induction hypothesis so the captured-env case is available in arrow/parrow branches.
        have hrec :
            (qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁) :=
          agreeValueUnder.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
            (motive_1 := fun qt v₀ v₁ _ =>
              qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁)
            (motive_2 := fun σcap ρcap₀ ρcap₁ _ =>
              agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁)
            (clean_eq_nonref_nonarrow := by
              intro qt v₀ v₁ hpoison hnotfun hnotref heq _hclean
              exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq)
            (clean_internal_arrow := by
              intro st1 st2 p tcls qt tcl x body σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
                hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap _hclean
              exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch ihcap
                (memberVarsRegimeEvidence_monotone h_mono hmemberVars₀)
                (memberCvcrEvidence_monotone h_mono hmemberCvcr₀)
                (memberVarsRegimeEvidence_monotone h_mono hmemberVars₁)
                (memberCvcrEvidence_monotone h_mono hmemberCvcr₁)
                hv₀ hv₁)
            (dirty_internal_arrow := by
              intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hclean
              exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
            (clean_internal_parrow := by
              intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
                hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap _hclean
              exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch ihcap
                (memberVarsRegimeEvidence_monotone h_mono hmemberVars₀)
                (memberCvcrEvidence_monotone h_mono hmemberCvcr₀)
                (memberVarsRegimeEvidence_monotone h_mono hmemberVars₁)
                (memberCvcrEvidence_monotone h_mono hmemberCvcr₁)
                hv₀ hv₁)
            (dirty_internal_parrow := by
              intro qt v₀ v₁ hdirty_internal hisParrow htyp1 htyp2 _hclean
              exact agreeValueUnder.dirty_internal_parrow hdirty_internal hisParrow htyp1 htyp2)
            (clean_ref := by
              intro ls l a₀ a₁ qt v₀ v₁ hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁ _hclean
              exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁)
            (withPred_true_eq := by
              intro k qt v₀ v₁ htag _hreg hnotfun hnotref heq hclean
              cases hclean with
              | clean hpoison =>
                  exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq
              | guard k' htag' hk'R' _hnotfun' =>
                  have hk : k' = k := by
                    have : some k' = some k := by
                      calc
                        some k' = qtypGuardTag qt := by symm; exact htag'
                        _ = some k := htag
                    exact Option.some.inj this
                  have hreg : R'.lookup? k = some true := by
                    simpa [hk] using hk'R'
                  exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref heq)
            (withPred_true_ref := by
              intro k ls l a₀ a₁ qt v₀ v₁ htag _hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁ hclean
              cases hclean with
              | clean hpoison =>
                  exact agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁
              | guard k' htag' hk'R' _hnotfun' =>
                  have hk : k' = k := by
                    have : some k' = some k := by
                      calc
                        some k' = qtypGuardTag qt := by symm; exact htag'
                        _ = some k := htag
                    exact Option.some.inj this
                  have hreg : R'.lookup? k = some true := by
                    simpa [hk] using hk'R'
                  exact agreeValueUnder.withPred_true_ref k htag hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁)
            (nil := by
              intro ρcap₀ ρcap₁
              exact agreeCapturedEnv.nil)
            (cons_clean := by
              intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ _hcleanR hlookup1 hlookup2 htyp1 htyp2 hagree htail ihagree ihtail
              by_cases hcleanR' : qtypCleanUnder R' qt
              · exact agreeCapturedEnv.cons_clean hcleanR' hlookup1 hlookup2 htyp1 htyp2 (ihagree hcleanR') ihtail
              · exact agreeCapturedEnv.cons_dirty hcleanR' hlookup1 hlookup2 htyp1 htyp2 ihtail)
            (cons_dirty := by
              intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ hdirty hlookup1 hlookup2 htyp1 htyp2 htail ihtail
              have hdirty' : ¬ qtypCleanUnder R' qt := by
                intro hcleanR'
                exact hdirty (cleanUnder_of_monotone (R := R) (R' := R') h_mono hcleanR')
              exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
            hagree
        exact hrec hclean
      -- Establish the regime monotone step from after-e1 to after-e2 (typechecking can only drop regime entries).
      have h_mono_e2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
        have h := regime_monotone ctx' e2 fuel' res2 htc2'
        have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
        simpa [hR1] using h
      -- Split on shadowing: the only variable affected by the let-binding is `vname`.
      by_cases hx : x = vname
      · subst x
        -- Use IH1 agreement for the original variable binding (since the runtime varEnv is restored).
        have hlookup1 : (ctxAfter ctxᵢ res1).varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have hclean_final : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          -- Final regime is the e2 output regime.
          simpa [h_regime_eq] using hclean
        have hclean1 : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt :=
          cleanUnder_of_monotone h_mono_e2 hclean_final
        have hagree_var1 := hagree_clean1.2 vname qt hlookup1 hclean1
        cases hagree_var1 with
        | both_none _ _ hnone₀ hnone₁ =>
            refine agreeVarUnder.both_none vname qt ?_ ?_
            · simpa [h_var₀_eq] using hnone₀
            · simpa [h_var₁_eq] using hnone₁
        | agree_values _ _ v₀ v₁ hv₀ hv₁ hagree_val =>
            -- Transfer value agreement to the final regime, extended realisation maps, and final memories.
            have hagree_val' : agreeValueUnder predSat (ctxAfter ctx' res2).regime cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
              agreeValueUnder_clean_monotoneRegime h_mono_e2 hclean_final hagree_val
            have hqtypPredHolds_mem_vlet₀ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' cfg₀1.memory v' ↔
                    qtypPredHolds predSat qt' cf₀.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₀1) (μ := cfg₀1.memory) (μ' := cf₀.memory)
            have hqtypPredHolds_mem_vlet₁ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' cfg₁1.memory v' ↔
                    qtypPredHolds predSat qt' cf₁.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₁1) (μ := cfg₁1.memory) (μ' := cf₁.memory)
            have hagree_val'' :
                agreeValueUnder predSat (ctxAfter ctx' res2).regime cf₀.memory cf₁.memory θ₀2 θ₁2 qt v₀ v₁ :=
              agreeValueUnder_clean_extends_transport_mem
                hqtypPredHolds_mem_vlet₀ hqtypPredHolds_mem_vlet₁
                hclean_final hθext₀2.1 hθext₁2.1 hagree_val'
            refine agreeVarUnder.agree_values vname qt v₀ v₁ ?_ ?_ ?_
            · simpa [h_var₀_eq] using hv₀
            · simpa [h_var₁_eq] using hv₁
            · simpa [h_mem₀_eq, h_mem₁_eq, h_regime_eq] using hagree_val''
      · -- x ≠ vname: use IH2 agreement in the extended context, then transport lookups back to the restored varEnvs.
        have hlookup_ctx' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          -- ctx'.varEnv is ctxᵢ.varEnv updated at vname; lookup at x is unchanged.
          have hlookup_ctx : ctxᵢ.varEnv.lookup x = some qt := by
            simpa [ctxAfter] using hlookup
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctx
          simpa [ctxAfter, hctx'] using this
        have hclean_ctx' : qtypCleanUnder (ctxAfter ctx' res2).regime qt := by
          simpa [h_regime_eq] using hclean
        have hagree_var := hagree_clean2.2 x qt hlookup_ctx' hclean_ctx'
        cases hagree_var with
        | both_none _ _ hnone₀ hnone₁ =>
            refine agreeVarUnder.both_none x qt ?_ ?_
            · -- Transport the `none` lookup across the let-bound update and varEnv restoration.
              have : cfg₀3.varEnv.lookup x = none := hnone₀
              have : cfg₀1.varEnv.lookup x = none := by
                -- cfg₀3.varEnv = cfg₀2.varEnv = cfg₀1.varEnv.update vname v₀1
                have hx' : cfg₀2.varEnv.lookup x = none := by
                  simpa [hvar_pres₀] using this
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hx'
              simpa [h_var₀_eq] using this
            · have : cfg₁3.varEnv.lookup x = none := hnone₁
              have : cfg₁1.varEnv.lookup x = none := by
                have hx' : cfg₁2.varEnv.lookup x = none := by
                  simpa [hvar_pres₁] using this
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hx'
              simpa [h_var₁_eq] using this
        | agree_values _ _ v₀ v₁ hv₀ hv₁ hagree_val =>
            refine agreeVarUnder.agree_values x qt v₀ v₁ ?_ ?_ ?_
            · -- lookup in restored env equals lookup in extended env for x ≠ vname
              have : cfg₀3.varEnv.lookup x = some v₀ := hv₀
              have : cfg₀1.varEnv.lookup x = some v₀ := by
                have hx' : cfg₀2.varEnv.lookup x = some v₀ := by
                  simpa [hvar_pres₀] using this
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using hx'
              simpa [h_var₀_eq] using this
            · have : cfg₁3.varEnv.lookup x = some v₁ := hv₁
              have : cfg₁1.varEnv.lookup x = some v₁ := by
                have hx' : cfg₁2.varEnv.lookup x = some v₁ := by
                  simpa [hvar_pres₁] using this
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using hx'
              simpa [h_var₁_eq] using this
            · -- agreeValueUnder is insensitive to varEnvs; just rewrite memories/regime to match the goal.
              simpa [h_mem₀_eq, h_mem₁_eq, h_regime_eq] using hagree_val
  -- Final wfConfig
  have hwfcf₀_final : wfConfig cf₀ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ :=
    (wfConfig_preserved .ioFree (Expr.vlet vname e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
  -- Need consistentWithRegime for both runs
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    have h_mem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
    have h_var₀_eq : cf₀.varEnv = cfg₀1.varEnv := by simp [hcf₀_eq]
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    constructor
    · intro l qt k hlookup hguard hkR
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        simpa [ctxAfter, h_mem] using hlookup
      have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
        simpa [hR_eq] using hkR
      have hloc := hcwr₀2.1 l qt k hlookup' hguard hkR'
      simpa [hR_eq, h_mem₀_eq] using hloc
    constructor
    · intro x qt k hlookup hguard hkR
      by_cases hx : x = vname
      · subst x
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        cases hpred : qt.pred with
        | noPred =>
            exact varsRegime.noPred_ok (vname, qt) (by simp [qtypGuardTag, hpred])
        | guardOnly k0 =>
            exact varsRegime.guardOnly_ok (vname, qt) k0 hpred
        | guardClosure k0 arg_name pred_body var_env =>
            -- Ruled out by the vlet shadowing restriction in the typechecker.
            exfalso
            have hk0 : k0 = k := by
              have : qtypGuardTag qt = some k0 := by simp [qtypGuardTag, hpred]
              exact Option.some.inj (this.symm.trans hguard)
            have hkR_e2 : (ctxAfter ctx' res2).regime.lookup? k0 ≠ none := by
              simpa [hk0, hR_eq] using hkR
            have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
              simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
            have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
              have h := regime_monotone ctx' e2 fuel' res2 htc2'
              have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
              simpa [hR1, ctxAfter] using h
            have hkR_after1 : (ctxAfter ctxᵢ res1).regime.lookup? k0 ≠ none :=
              h_mono2.2.2 k0 hkR_e2
            have hkR_ctxᵢ : ctxᵢ.regime.lookup? k0 ≠ none :=
              h_mono1.2.2 k0 hkR_after1
            have hk_isSome : (ctxᵢ.regime.lookup? k0).isSome = true := by
              cases hk : ctxᵢ.regime.lookup? k0 with
              | none => exact (hkR_ctxᵢ hk).elim
              | some b => simp
            have htc_bad := htc'
            simp [typecheckVlet, hlookup_ctxᵢ, hpred, hk_isSome] at htc_bad
            cases htc_bad
      · have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
          simpa [hR_eq] using hkR
        have hvars2 := hcwr₀2.2.1 x qt k hlookup_ctxAfter' hguard hkR'
        cases hvars2 with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hlookup_v hconsist =>
            have hlookup_v' : cf₀.varEnv.lookup x = some v := by
              have : cfg₀3.varEnv.lookup x = some v := hlookup_v
              have : cfg₀2.varEnv.lookup x = some v := by
                simpa [hvar_pres₀] using this
              have : cfg₀1.varEnv.lookup x = some v := by
                simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using this
              simpa [h_var₀_eq] using this
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hR_eq] using hreg
            have hconsist' :
                (b = true → qtypPredHolds predSat qt cf₀.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₀.memory v) := by
              simpa [h_mem₀_eq] using hconsist
            exact
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: use initial hcwr₀; transport regime via monotonicity, memory via predSat independence
        rw [hx] at hlookup hlookup_v
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have h_varEnv_pres₀ : ρ₀ = cfg₀1.varEnv := by
          rcases ht₀_e1_w with ⟨fuel_w, verbose_w, h_beval_w⟩
          exact beval_preserves_varEnv .ioFree e1 fuel_w verbose_w _ _ _ ⟨w_default, w_default, h_beval_w⟩
        have hlookup_v_ρ₀ : ρ₀.lookup vname = some v := by
          rw [h_varEnv_pres₀]; simpa [h_var₀_eq] using hlookup_v
        have hcap₀ := hcwr₀.2.2 vname qt v hlookup_ctxᵢ hlookup_v_ρ₀
        have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
          simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
        have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
          have h := regime_monotone ctx' e2 fuel' res2 htc2'
          have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
          simpa [hR1, ctxAfter] using h
        have hcap₂ := closureCapturedVarsRegime_monotone h_mono2
          (closureCapturedVarsRegime_monotone h_mono1 hcap₀)
        rw [← hR_eq] at hcap₂
        have hPredSat_mem₀ : ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
          predSat_mem_noPred_compat hpredlaws θ₀
        exact closureCapturedVarsRegime_transport_μ_θ (fun qt' v' =>
          ⟨fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').1 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').1 hs),
           fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').2 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₀ _ μ₀ cf₀.memory v').2 hs)⟩)
          hθext₀.1 hcap₂
      · -- x ≠ vname: use hcwr₀2 from IH2 and transport regimes/memory
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hlookup_v_cfg₀3 : cfg₀3.varEnv.lookup x = some v := by
          have hcf₀_v : cf₀.varEnv.lookup x = some v := hlookup_v
          have : cfg₀1.varEnv.lookup x = some v := by simpa [h_var₀_eq] using hcf₀_v
          have h2 : cfg₀2.varEnv.lookup x = some v := by
            simpa [cfg₀2, VarEnv_lookup_update_ne cfg₀1.varEnv vname x v₀1 hx] using this
          rw [hvar_pres₀]; exact h2
        have hcap := hcwr₀2.2.2 x qt v hlookup_ctxAfter' hlookup_v_cfg₀3
        rw [← hR_eq] at hcap
        rw [← h_mem₀_eq] at hcap
        exact hcap
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    have h_mem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
    have h_var₁_eq : cf₁.varEnv = cfg₁1.varEnv := by simp [hcf₁_eq]
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    constructor
    · intro l qt k hlookup hguard hkR
      have hlookup' : (ctxAfter ctx' res2).memEnv.lookup l = some qt := by
        simpa [ctxAfter, h_mem] using hlookup
      have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
        simpa [hR_eq] using hkR
      have hloc := hcwr₁2.1 l qt k hlookup' hguard hkR'
      simpa [hR_eq, h_mem₁_eq] using hloc
    constructor
    · intro x qt k hlookup hguard hkR
      by_cases hx : x = vname
      · subst x
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        cases hpred : qt.pred with
        | noPred =>
            exact varsRegime.noPred_ok (vname, qt) (by simp [qtypGuardTag, hpred])
        | guardOnly k0 =>
            exact varsRegime.guardOnly_ok (vname, qt) k0 hpred
        | guardClosure k0 arg_name pred_body var_env =>
            exfalso
            have hk0 : k0 = k := by
              have : qtypGuardTag qt = some k0 := by simp [qtypGuardTag, hpred]
              exact Option.some.inj (this.symm.trans hguard)
            have hkR_e2 : (ctxAfter ctx' res2).regime.lookup? k0 ≠ none := by
              simpa [hk0, hR_eq] using hkR
            have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
              simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
            have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
              have h := regime_monotone ctx' e2 fuel' res2 htc2'
              have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
              simpa [hR1, ctxAfter] using h
            have hkR_after1 : (ctxAfter ctxᵢ res1).regime.lookup? k0 ≠ none :=
              h_mono2.2.2 k0 hkR_e2
            have hkR_ctxᵢ : ctxᵢ.regime.lookup? k0 ≠ none :=
              h_mono1.2.2 k0 hkR_after1
            have hk_isSome : (ctxᵢ.regime.lookup? k0).isSome = true := by
              cases hk : ctxᵢ.regime.lookup? k0 with
              | none => exact (hkR_ctxᵢ hk).elim
              | some b => simp
            have htc_bad := htc'
            simp [typecheckVlet, hlookup_ctxᵢ, hpred, hk_isSome] at htc_bad
            cases htc_bad
      · have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hkR' : (ctxAfter ctx' res2).regime.lookup? k ≠ none := by
          simpa [hR_eq] using hkR
        have hvars2 := hcwr₁2.2.1 x qt k hlookup_ctxAfter' hguard hkR'
        cases hvars2 with
        | noPred_ok hpred =>
            exact varsRegime.noPred_ok (x, qt) hpred
        | guardOnly_ok k' hgo =>
            exact varsRegime.guardOnly_ok (x, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env v b hclos hreg hlookup_v hconsist =>
            have hlookup_v' : cf₁.varEnv.lookup x = some v := by
              have : cfg₁3.varEnv.lookup x = some v := hlookup_v
              have : cfg₁2.varEnv.lookup x = some v := by
                simpa [hvar_pres₁] using this
              have : cfg₁1.varEnv.lookup x = some v := by
                simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using this
              simpa [h_var₁_eq] using this
            have hreg' : (ctxAfter ctxᵢ res).regime.lookup? k' = some b := by
              simpa [hR_eq] using hreg
            have hconsist' :
                (b = true → qtypPredHolds predSat qt cf₁.memory v) ∧
                (b = false → ¬ qtypPredHolds predSat qt cf₁.memory v) := by
              simpa [h_mem₁_eq] using hconsist
            exact
              varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b hclos hreg' hlookup_v' hconsist'
    · intro x qt v hlookup hlookup_v
      by_cases hx : x = vname
      · -- x = vname: use initial hcwr₁; transport regime via monotonicity, memory via predSat independence
        rw [hx] at hlookup hlookup_v
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup vname = some qt := by
          simpa [ctxAfter] using hlookup
        have h_varEnv_pres₁ : ρ₁ = cfg₁1.varEnv := by
          rcases ht₁_e1_w with ⟨fuel_w, verbose_w, h_beval_w⟩
          exact beval_preserves_varEnv .ioFree e1 fuel_w verbose_w _ _ _ ⟨w_default, w_default, h_beval_w⟩
        have hlookup_v_ρ₁ : ρ₁.lookup vname = some v := by
          rw [h_varEnv_pres₁]; simpa [h_var₁_eq] using hlookup_v
        have hcap₀ := hcwr₁.2.2 vname qt v hlookup_ctxᵢ hlookup_v_ρ₁
        have h_mono1 : Regime.monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime := by
          simpa [ctxAfter] using (regime_monotone ctxᵢ e1 fuel' res1 htc1')
        have h_mono2 : Regime.monotoneStep (ctxAfter ctxᵢ res1).regime (ctxAfter ctx' res2).regime := by
          have h := regime_monotone ctx' e2 fuel' res2 htc2'
          have hR1 : ctx'.regime = (ctxAfter ctxᵢ res1).regime := by simp [hctx', ctxAfter]
          simpa [hR1, ctxAfter] using h
        have hcap₂ := closureCapturedVarsRegime_monotone h_mono2
          (closureCapturedVarsRegime_monotone h_mono1 hcap₀)
        rw [← hR_eq] at hcap₂
        have hPredSat_mem₁ : ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
          predSat_mem_noPred_compat hpredlaws θ₁
        exact closureCapturedVarsRegime_transport_μ_θ (fun qt' v' =>
          ⟨fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').1 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').1 hs),
           fun h => by cases h with
            | noPred_ok hp => exact qtypPredHolds.noPred_ok hp
            | guardClosure_ok hp hs =>
                exact qtypPredHolds.guardClosure_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').2 hs)
            | guardOnly_ok hp hs =>
                exact qtypPredHolds.guardOnly_ok hp ((hPredSat_mem₁ _ μ₁ cf₁.memory v').2 hs)⟩)
          hθext₁.1 hcap₂
      · -- x ≠ vname: use hcwr₁2 from IH2 and transport regimes/memory
        have hlookup_ctxᵢ : ctxᵢ.varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup
        have hlookup_ctx' : ctx'.varEnv.lookup x = some qt := by
          have : (ctxᵢ.varEnv.update vname res1.qualType).lookup x = some qt := by
            simpa [VarTypeEnv_lookup_update_ne ctxᵢ.varEnv vname x res1.qualType hx] using hlookup_ctxᵢ
          simpa [hctx'] using this
        have hlookup_ctxAfter' : (ctxAfter ctx' res2).varEnv.lookup x = some qt := by
          simpa [ctxAfter] using hlookup_ctx'
        have hlookup_v_cfg₁3 : cfg₁3.varEnv.lookup x = some v := by
          have hcf₁_v : cf₁.varEnv.lookup x = some v := hlookup_v
          have : cfg₁1.varEnv.lookup x = some v := by simpa [h_var₁_eq] using hcf₁_v
          have h2 : cfg₁2.varEnv.lookup x = some v := by
            simpa [cfg₁2, VarEnv_lookup_update_ne cfg₁1.varEnv vname x v₁1 hx] using this
          rw [hvar_pres₁]; exact h2
        have hcap := hcwr₁2.2.2 x qt v hlookup_ctxAfter' hlookup_v_cfg₁3
        rw [← hR_eq] at hcap
        rw [← h_mem₁_eq] at hcap
        exact hcap
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hetyp : res.qualType.etyp = res2.qualType.etyp := by
      simp [h_ret_etyp]
    have hpredEq : res.qualType.pred = res2.qualType.pred := by
      simp [h_ret_pred]
    exact fun {qt'} {k} {d} hinq hqd =>
      (QTypRespectsTagMeaning_transport_etyp_pred
        (tm := tm) (qt := res2.qualType) (qt' := res.qualType) hresTm2 hetyp hpredEq) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀'', hric₁'', hreg'', hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · rw [h_ret_etyp]
    exact _hvtyp₀2
  · rw [h_ret_etyp]
    exact _hvtyp₁2
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res): remove the temporary vlet binding.
    unfold wfTagMeaningCtx at _hTm2 ⊢
    simp only [ctxAfter, h_mem, h_tag, h_loc, h_ntag]
    have _hTm2' : EnvRespectsTagMeaning tm (ctxᵢ.varEnv.update vname res1.qualType) res2.memEnv' := by
      simpa [hctx'] using _hTm2
    refine EnvRespectsTagMeaning_of_update tm vname ctxᵢ.varEnv res1.qualType res2.memEnv' _hTm2' ?_
    intro qt hlookup
    exact wfTagMeaningCtx_var_lookup_qtyp tm ctxᵢ vname qt hwfTm hlookup
  · -- wfTypeContext
    intro l hcontains
    simp only [ctxAfter, h_mem, h_loc] at hcontains ⊢
    exact hwf2 l hcontains
  · -- valueConsistentWithRegime for cf₀
    -- Reuse IH2's value consistency for `res2.qualType`, then transport across
    -- the vlet result's predicate threading and varEnv restoration.
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    have hpred_eq : res2.qualType.pred = res.qualType.pred := by
      simpa using h_ret_pred.symm
    have hmem_eq : cf₀.memory = cfg₀3.memory := by
      simp [hcf₀_eq]
    have hv2 : valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res2.qualType cfg₀3.memory θ₀2 o₀ :=
      _hval_consist₀2
    have hv' :
        valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res.qualType cfg₀3.memory θ₀2 o₀ :=
      valueConsistentWithRegime_transport_pred (predSat := predSat) (R := (ctxAfter ctx' res2).regime)
        (qt := res2.qualType) (qt' := res.qualType) (μ := cfg₀3.memory) (v := o₀) hpred_eq (hetyp := h_ret_etyp.symm) hv2
    simpa [hR_eq, hmem_eq] using hv'
  · -- valueConsistentWithRegime for cf₁
    have hR_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp [ctxAfter, h_ret_regime]
    have hpred_eq : res2.qualType.pred = res.qualType.pred := by
      simpa using h_ret_pred.symm
    have hmem_eq : cf₁.memory = cfg₁3.memory := by
      simp [hcf₁_eq]
    have hv2 : valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res2.qualType cfg₁3.memory θ₁2 o₁ :=
      _hval_consist₁2
    have hv' :
        valueConsistentWithRegime predSat (ctxAfter ctx' res2).regime res.qualType cfg₁3.memory θ₁2 o₁ :=
      valueConsistentWithRegime_transport_pred (predSat := predSat) (R := (ctxAfter ctx' res2).regime)
        (qt := res2.qualType) (qt' := res.qualType) (μ := cfg₁3.memory) (v := o₁) hpred_eq (hetyp := h_ret_etyp.symm) hv2
    simpa [hR_eq, hmem_eq] using hv'
  -- resultAgreesIfClean
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
        calc joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by symm; exact h_ret_poison
             _ = false := by exact hpoison_res
      exact (joinPoison_eq_false hjoin).2
    -- hclean uses (ctxAfter ctxᵢ res).regime = res.regime' = res2.regime'
    -- We need hclean2' : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType for IH2
    -- Since (ctxAfter ctx' res2).regime = res2.regime' = res.regime' = (ctxAfter ctxᵢ res).regime
    -- First, prove regime equality from typechecker structure lemma
    have h_res_regime_eq : res.regime' = res2.regime' := h_ret_regime
    have h_regime_eq : (ctxAfter ctxᵢ res).regime = (ctxAfter ctx' res2).regime := by
      simp only [ctxAfter, h_res_regime_eq]
    have hclean2' : qtypCleanUnder (ctxAfter ctx' res2).regime res2.qualType := by
      cases hclean with
      | clean hpoison_res => exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k htag hreg hnotfun =>
          have htag' : qtypGuardTag res2.qualType = some k := by
            simpa [qtypGuardTag, h_ret_pred] using htag
          have hnotfun' : res2.qualType.etyp.isFunctionType = false := by
            simpa [h_ret_etyp] using hnotfun
          -- hreg : (ctxAfter ctxᵢ res).regime.lookup? k = some true
          -- Need: (ctxAfter ctx' res2).regime.lookup? k = some true
          exact qtypCleanUnder.guard k htag' (h_regime_eq ▸ hreg) hnotfun'
    have hagree2_ctx' := hres_agree2 hclean2'
    -- hagree2_ctx' : agreeValueUnder predSat (ctxAfter ctx' res2).regime cfg₀3.memory cfg₁3.memory ... res2.qualType o₀ o₁
    -- Need: agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory ... res2.qualType o₀ o₁
    -- Note: cf₀.memory = cfg₀3.memory (from hcf₀_eq) and cf₁.memory = cfg₁3.memory
    have hagree2 : agreeValueUnder predSat (ctxAfter ctxᵢ res).regime cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      have hmem₀_eq : cf₀.memory = cfg₀3.memory := by simp [hcf₀_eq]
      have hmem₁_eq : cf₁.memory = cfg₁3.memory := by simp [hcf₁_eq]
      rw [hmem₀_eq, hmem₁_eq, h_regime_eq]
      exact hagree2_ctx'
    exact agreeValueUnder_transport_clean hclean h_ret_etyp hpoison_imp hagree2

-- World-free version of stepFRW_fn
private lemma stepFR_fn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck .ioFree ctxᵢ (Expr.fn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.fn x paramType body returnType) res predSat tm := by
  -- Extract typecheck result
  have htcFn : typecheckFn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  let res_expected : TypeResult := {
    qualType :=
      ⟨ETyp.arrow paramType returnType ctxᵢ.pc
          [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
        ctxᵢ.pc, Predicate.noPred⟩
    memEnv' := ctxᵢ.memEnv
    tagEnv' := ctxᵢ.tagEnv
    nextLoc' := ctxᵢ.nextLoc
    nextTag' := ctxᵢ.nextTag
    regime' := ctxᵢ.regime
  }
  have hres : res = res_expected := by
    have htc' := htcFn
    simp [typecheckFn] at htc'
    cases htc'
    rfl
  have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
    simp [ctxAfter, hres, res_expected]
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Use world-free inversion lemma
  have ⟨hcf₀, ho₀⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  have ⟨hcf₁, ho₁⟩ := terminatesTo_fn_inv' mode x paramType body returnType
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  subst hcf₀ hcf₁
  have hcap' :
      agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
    agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
  -- Convert to use output regime (which equals input regime for fn)
  have h_regime_eq : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [hctxAfter]
  have hcap :
      agreeCapturedEnv predSat (ctxAfter ctxᵢ res).regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ := by
    rw [h_regime_eq]; exact hcap'
  have hresTm_expected : QTypRespectsTagMeaning tm res_expected.qualType := by
    intro qt' k d hinq hqd
    exact
      (QTypRespectsTagMeaning_fn_regular
        (tm := tm) (ctx := ctxᵢ) (x := x)
        (st₁ := paramType) (st₂ := returnType) (p := ctxᵢ.pc) (body := body) hwfTm)
        (by simpa [res_expected] using hinq)
        (by simpa [res_expected] using hqd)
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    intro qt' k d hinq hqd
    exact hresTm_expected (by simpa [hres] using hinq) (by simpa [hres] using hqd)
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
    refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
  · have hcover₀ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ₀.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric₀.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    subst ho₀
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp)
        (hcover := hcover₀) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric₀.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ₀.lookup y := by symm; exact hvlookup
          _ = some v := by exact hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  · have hcover₁ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
        ∃ v, ρ₁.lookup y = some v := by
      intro y qt hlookupT
      have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
      obtain ⟨v', hvlookup, _⟩ := hric₁.2 hlookup_ctx
      exact ⟨v', hvlookup⟩
    subst ho₁
    have hetyp_res :
        res.qualType.etyp =
          ETyp.arrow paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
      simp [hres, res_expected]
    rw [hetyp_res]
    refine valueHasETyp.closure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (htcl := by simp)
        (hcover := hcover₁) ?_
    intro y qt v hlookupT hlookupV
    have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
    obtain ⟨v', hvlookup, hvtyp⟩ := hric₁.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by
        calc
          some v' = ρ₁.lookup y := by symm; exact hvlookup
          _ = some v := by exact hlookupV
      exact Option.some.inj this
    subst hvEq
    exact hvtyp
  · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using hwfTm
  · -- wfTypeContext (ctxAfter ctxᵢ res)
    simpa [hctxAfter] using hwf
  · -- runtimeInstantiatesCtx for θ₀' (fn doesn't change context or config)
    simpa [hctxAfter] using hric₀
  · -- runtimeInstantiatesCtx for θ₁'
    simpa [hctxAfter] using hric₁
  · -- regimeConsistentWithCtx (fn doesn't change context)
    simpa [hctxAfter] using hreg
  · -- consistentWithRegime for run 0 (fn doesn't change context)
    simpa [hctxAfter] using hcwr₀
  · -- consistentWithRegime for run 1 (fn doesn't change context)
    simpa [hctxAfter] using hcwr₁
  · -- agreeOnClean for updated context (fn doesn't change context)
    simpa [hctxAfter] using hagree
  · -- valueConsistentWithRegime for cf₀
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
      (.intro (by
        rw [ho₀, h_regime_eq]
        apply deepValueQTypProperty.closure x body ρ₀
            (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr₀.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          cases hcwr₀.2.2 y qt_y v_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hlookup_ρ with
          | intro h => exact h))
  · -- valueConsistentWithRegime for cf₁
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
      (.intro (by
        rw [ho₁, h_regime_eq]
        apply deepValueQTypProperty.closure x body ρ₁
            (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
        · rfl
        · simp [hres, res_expected]
        · simp
        · constructor
          · intro y qt_y k_y hlookup_σ hguard hkR
            exact hcwr₁.2.1 y qt_y k_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hguard hkR
          · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
              fun y qt hlookup_σ =>
                let ⟨v, hv, _⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                ⟨v, hv⟩,
              fun y qt v hlookup_σ hlookup_ρ =>
                let ⟨v', hv', htyp⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
        · intro y qt_y v_y hlookup_σ hlookup_ρ
          cases hcwr₁.2.2 y qt_y v_y
              (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
              hlookup_ρ with
          | intro h => exact h))
  · -- resultAgreesIfClean
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp :
            res.qualType.etyp =
              ETyp.arrow paramType returnType ctxᵢ.pc
                [FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        -- res.qualType.poison = ctxᵢ.pc (from res_expected)
        -- hpoison says qt.poison = false, and qt = res.qualType
        -- Therefore ctxᵢ.pc = false, so internal poison is clean
        have hpc_clean : ctxᵢ.pc = false := by
          have hqt_poison : res.qualType.poison = ctxᵢ.pc := by
            simp [hres, res_expected]
          calc
            ctxᵢ.pc = res.qualType.poison := by symm; exact hqt_poison
            _ = false := by exact hpoison
        have hclean_internal : internalPoisonClean res.qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hmemberVars₀ :
            MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₀
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
          simpa [hctxAfter] using
            (memberVarsRegimeEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
        have hmemberVars₁ :
            MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₁
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
          simpa [hctxAfter] using
            (memberVarsRegimeEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
        have hmemberCvcr₀ :
            MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₀ θ₀
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
          simpa [hctxAfter] using
            (memberCvcrEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
        have hmemberCvcr₁ :
            MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₁ θ₁
              (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
          simpa [hctxAfter] using
            (memberCvcrEvidence_of_toCaptured
              (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
              (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
        exact
          agreeValueUnder.clean_internal_arrow
            (tcl := FnTClosure.regular x body (VarTypeEnv.toCaptured ctxᵢ.varEnv))
            (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
            hclean_internal hetyp (by simp) rfl hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
            (by simp [ho₀]) (by simp [ho₁])
    | guard k htag _hregime _ =>
        have : False := by
          have hpred : qtypGuardTag res.qualType = none := by
            simp [qtypGuardTag, hres, res_expected]
          simp [hpred] at htag
        exact False.elim this

-- World-free version of stepFRW_pfn
private lemma stepFR_pfn
  (mode : LeanPoison.EvalMode)
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
  (fuel : Nat) (res : TypeResult)
  (htc : typecheck .ioFree ctxᵢ (Expr.pfn x paramType body returnType) (Nat.succ fuel) = .ok res) :
  StepFR mode ctxᵢ (Expr.pfn x paramType body returnType) res predSat tm := by
  -- Extract typecheck result
  have htcPfn : typecheckPfn ctxᵢ x paramType body returnType = .ok res := by
    have h := htc
    simp [typecheck, typecheckExpr] at h
    exact h
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody] at htcPfn
  | ok pbody =>
      let res_expected : TypeResult := {
        qualType :=
          ⟨ETyp.parrow paramType returnType ctxᵢ.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)],
            ctxᵢ.pc, Predicate.noPred⟩
        memEnv' := ctxᵢ.memEnv
        tagEnv' := ctxᵢ.tagEnv
        nextLoc' := ctxᵢ.nextLoc
        nextTag' := ctxᵢ.nextTag
        regime' := ctxᵢ.regime
      }
      have hres : res = res_expected := by
        have htc' := htcPfn
        simp [typecheckPfn, hbody] at htc'
        cases htc'
        rfl
      have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
        simp [ctxAfter, hres, res_expected]
      intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ hreg hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
      -- Use world-free inversion lemma
      have ⟨hcf₀, ho₀⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
      have ⟨hcf₁, ho₁⟩ := terminatesTo_pfn_inv' mode x paramType body returnType
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
      subst hcf₀ hcf₁
      have hcap' :
          agreeCapturedEnv predSat ctxᵢ.regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ :=
        agreeCapturedEnv_of_agreeOnClean predSat ctxᵢ.regime ctxᵢ μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
      -- Convert to use output regime (which equals input regime for pfn)
      have h_regime_eq : (ctxAfter ctxᵢ res).regime = ctxᵢ.regime := by simp [hctxAfter]
      have hcap :
          agreeCapturedEnv predSat (ctxAfter ctxᵢ res).regime μ₀ μ₁ θ₀ θ₁ (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ ρ₁ := by
        rw [h_regime_eq]; exact hcap'
      have hto : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hresTm_expected : QTypRespectsTagMeaning tm res_expected.qualType := by
        intro qt' k d hinq hqd
        exact
          (QTypRespectsTagMeaning_pfn_regular
            (tm := tm) (ctx := ctxᵢ) (x := x)
            (st₁ := paramType) (st₂ := returnType) (p := ctxᵢ.pc) (body := pbody) hwfTm)
            (by simpa [res_expected] using hinq)
            (by simpa [res_expected] using hqd)
      have hresTm : QTypRespectsTagMeaning tm res.qualType := by
        intro qt' k d hinq hqd
        exact hresTm_expected (by simpa [hres] using hinq) (by simpa [hres] using hqd)
      refine ⟨hresTm, ?_⟩
      refine ⟨θ₀, θ₁, ?_, ?_, ?_, ?_, ?_, ?_, hwfcfg₀, hwfcfg₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- wfExtendsMap θ₀ θ₀ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · -- wfExtendsMap θ₁ θ₁ (maps unchanged)
        refine ⟨fun l a hlookup => hlookup, fun hwf' => hwf'⟩
      · have hcover₀ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ₀.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric₀.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        subst ho₀
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (hpure := hto) (htcl := by simp)
            (hcover := hcover₀) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric₀.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ₀.lookup y := by symm; exact hvlookup
              _ = some v := by exact hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      · have hcover₁ : ∀ y qt, (VarTypeEnv.toCaptured ctxᵢ.varEnv).lookup y = some qt →
            ∃ v, ρ₁.lookup y = some v := by
          intro y qt hlookupT
          have hlookup_ctx := VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
          obtain ⟨v', hvlookup, _⟩ := hric₁.2 hlookup_ctx
          exact ⟨v', hvlookup⟩
        subst ho₁
        have hetyp_res :
            res.qualType.etyp =
              ETyp.parrow paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
          simp [hres, res_expected]
        rw [hetyp_res]
        refine valueHasETyp.peClosure (tenv := VarTypeEnv.toCaptured ctxᵢ.varEnv) (hpure := hto) (htcl := by simp)
            (hcover := hcover₁) ?_
        intro y qt v hlookupT hlookupV
        have hlookup_ctx : ctxᵢ.varEnv.lookup y = some qt :=
          VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookupT
        obtain ⟨v', hvlookup, hvtyp⟩ := hric₁.2 hlookup_ctx
        have hvEq : v' = v := by
          have : some v' = some v := by
            calc
              some v' = ρ₁.lookup y := by symm; exact hvlookup
              _ = some v := by exact hlookupV
          exact Option.some.inj this
        subst hvEq
        exact hvtyp
      · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using hwfTm
      · -- wfTypeContext (ctxAfter ctxᵢ res)
        simpa [hctxAfter] using hwf
      · -- runtimeInstantiatesCtx for θ₀' (pfn doesn't change context or config)
        simpa [hctxAfter] using hric₀
      · -- runtimeInstantiatesCtx for θ₁'
        simpa [hctxAfter] using hric₁
      · -- regimeConsistentWithCtx (pfn doesn't change context)
        simpa [hctxAfter] using hreg
      · -- consistentWithRegime for run 0 (pfn doesn't change context)
        simpa [hctxAfter] using hcwr₀
      · -- consistentWithRegime for run 1 (pfn doesn't change context)
        simpa [hctxAfter] using hcwr₁
      · -- agreeOnClean for updated context (pfn doesn't change context)
        simpa [hctxAfter] using hagree
      · -- valueConsistentWithRegime for cf₀
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
          (.intro (by
            rw [ho₀, h_regime_eq]
            apply deepValueQTypProperty.peClosure x body pbody ρ₀
                (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
            · rfl
            · simp [hres, res_expected]
            · exact hto
            · simp
            · constructor
              · intro y qt_y k_y hlookup_σ hguard hkR
                exact hcwr₀.2.1 y qt_y k_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hguard hkR
              · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
                  fun y qt hlookup_σ =>
                    let ⟨v, hv, _⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    ⟨v, hv⟩,
                  fun y qt v hlookup_σ hlookup_ρ =>
                    let ⟨v', hv', htyp⟩ := hric₀.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
            · intro y qt_y v_y hlookup_σ hlookup_ρ
              cases hcwr₀.2.2 y qt_y v_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hlookup_ρ with
              | intro h => exact h))
      · -- valueConsistentWithRegime for cf₁
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hres, res_expected])
          (.intro (by
            rw [ho₁, h_regime_eq]
            apply deepValueQTypProperty.peClosure x body pbody ρ₁
                (VarTypeEnv.toCaptured ctxᵢ.varEnv) paramType returnType ctxᵢ.pc
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)]
            · rfl
            · simp [hres, res_expected]
            · exact hto
            · simp
            · constructor
              · intro y qt_y k_y hlookup_σ hguard hkR
                exact hcwr₁.2.1 y qt_y k_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hguard hkR
              · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctxᵢ.varEnv,
                  fun y qt hlookup_σ =>
                    let ⟨v, hv, _⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    ⟨v, hv⟩,
                  fun y qt v hlookup_σ hlookup_ρ =>
                    let ⟨v', hv', htyp⟩ := hric₁.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt hlookup_σ)
                    by rw [hlookup_ρ] at hv'; cases hv'; exact htyp⟩
            · intro y qt_y v_y hlookup_σ hlookup_ρ
              cases hcwr₁.2.2 y qt_y v_y
                  (VarTypeEnv_lookup_of_toCaptured_lookup ctxᵢ.varEnv y qt_y hlookup_σ)
                  hlookup_ρ with
              | intro h => exact h))
      · -- resultAgreesIfClean
        intro hclean
        cases hclean with
        | clean hpoison =>
            have hetyp :
                res.qualType.etyp =
                  ETyp.parrow paramType returnType ctxᵢ.pc
                    [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
              simp [hres, res_expected]
            have htcl : PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) ∈
                [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv)] := by
              simp
            have hmatch : Expr.toPExpr? body = some pbody ∧
                PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) =
                  PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv) := by
              exact ⟨hto, rfl⟩
            -- Same reasoning as stepFR_fn: outer poison = ctxᵢ.pc = false, so internal clean
            have hpc_clean : ctxᵢ.pc = false := by
              have hqt_poison : res.qualType.poison = ctxᵢ.pc := by
                simp [hres, res_expected]
              calc
                ctxᵢ.pc = res.qualType.poison := by symm; exact hqt_poison
                _ = false := by exact hpoison
            have hclean_internal : internalPoisonClean res.qualType := by
              simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
            have hmemberVars₀ :
                MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₀
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
              simpa [hctxAfter] using
                (memberVarsRegimeEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
            have hmemberVars₁ :
                MemberVarsRegimeEvidence predSat (ctxAfter ctxᵢ res).regime μ₁
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
              simpa [hctxAfter] using
                (memberVarsRegimeEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
            have hmemberCvcr₀ :
                MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₀ θ₀
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₀ := by
              simpa [hctxAfter] using
                (memberCvcrEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀)
            have hmemberCvcr₁ :
                MemberCvcrEvidence predSat (ctxAfter ctxᵢ res).regime μ₁ θ₁
                  (VarTypeEnv.toCaptured ctxᵢ.varEnv) ρ₁ := by
              simpa [hctxAfter] using
                (memberCvcrEvidence_of_toCaptured
                  (predSat := predSat) (R := ctxᵢ.regime) (ctx := ctxᵢ)
                  (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁)
            exact
              agreeValueUnder.clean_internal_parrow
                (pbody := pbody)
                (tcl := PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctxᵢ.varEnv))
                (σcap := VarTypeEnv.toCaptured ctxᵢ.varEnv) (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
                hclean_internal hetyp htcl hmatch hcap
                hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
                (by simp [ho₀]) (by simp [ho₁])
        | guard k htag _hregime _ =>
            have : False := by
              have hpred : qtypGuardTag res.qualType = none := by
                simp [qtypGuardTag, hres, res_expected]
              simp [hpred] at htag
            exact False.elim this

-- ================================================================
-- I/O-free fault-robustness proofs
-- ================================================================

section TypeSystemEnforcesFaultRobustness_IOFree_proof

/-- Shared check from `matchGuard`: function types cannot carry non-`noPred`. -/
private def matchGuard_checkNoPredOnArrow (qt : QTyp) : TypecheckM Unit := do
  match qt.etyp with
  | ETyp.arrow _ _ _ _ | ETyp.parrow _ _ _ _ =>
      match qt.pred with
      | Predicate.noPred => pure ()
      | _ => throw "Function types cannot carry predicates in matchGuard"
  | _ => pure ()

/-- Shared predicate matcher from `matchGuard`. -/
private def matchGuard_checkPredicate
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (arg : PExpr) (qt : QTyp)
    (fuel : Nat) :
    TypecheckM (Option (Tag × Deps)) := do
  matchGuard_checkNoPredOnArrow qt
  match qt.pred with
  | Predicate.noPred => return none
  | Predicate.guardOnly _tag => return none
  | Predicate.guardClosure tag arg_name pred_body var_env =>
      -- Use `... = true` conditionals to stay syntactically aligned with the unfolded
      -- `matchGuard` implementation (which often normalizes Bool-ifs this way).
      if PExpr.usesArg arg_name pred_body = true then
        if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, arg)) fuel = true then do
          let deps ← extractDepsFromPred qt.pred fuel
          return some (tag, deps)
        else
          return none
      else
        return none

/-- Var-side matches used by `matchGuard`, expressed via `toList` fold for proof convenience. -/
private def matchGuard_varMatches (conditionPExpr : PExpr) (ctx : TypeContext)
    (fuel : Nat) : List (Tag × Deps) :=
  let sCaptured := VarTypeEnv.toCaptured ctx.varEnv
  VarTypeEnv.foldl [] (fun acc name qt =>
    let arg := PExpr.var name
    match matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel with
    | .ok (some kd) => kd :: acc
    | .ok none => acc
    | .error _ => acc) ctx.varEnv

/-- Single ref-entry transition used by `matchGuard` ref-side matching. -/
private def matchGuard_refStep
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (ctx : TypeContext)
    (acc : List (Tag × Deps)) (entry : Name × QTyp) (fuel : Nat) :
    TypecheckM (List (Tag × Deps)) := do
  let name := entry.1
  let qt := entry.2
  match qt.etyp with
  | ETyp.ref ls =>
      if qt.poison = true then
        pure acc
      else
        if ExtTreeSet.isEmpty ls = true then throw "Reference locset is empty in matchGuard" else
        let arg := PExpr.deref (PExpr.var name)
        let merged? ←
          ls.foldM (init := (none : Option Predicate)) (fun accPred? l => do
            match ctx.memEnv.lookup l with
            | some memQt =>
                matchGuard_checkNoPredOnArrow memQt
                let nextPred :=
                  match accPred? with
                  | none => memQt.pred
                  | some p => joinPredicates p memQt.pred
                pure (some nextPred)
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
        let depsMerged ←
          ls.foldM (init := LocSet.empty) (fun dacc l => do
            match ctx.memEnv.lookup l with
            | some memQt =>
                matchGuard_checkNoPredOnArrow memQt
                let deps ← extractDepsFromPred memQt.pred fuel
                pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
        let merged := merged?.getD Predicate.noPred
        match merged with
        | Predicate.guardClosure tag arg_name pred_body var_env =>
            if PExpr.usesArg arg_name pred_body = true then
              if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                  (some (arg_name, arg)) fuel = true then
                pure ((tag, depsMerged) :: acc)
              else
                pure acc
            else
              pure acc
        | Predicate.guardOnly _ => pure acc
        | Predicate.noPred => pure acc
  | _ => pure acc

/-- Ref-side matches used by `matchGuard`, expressed via `toList` fold for proof convenience. -/
private def matchGuard_refMatches (conditionPExpr : PExpr) (ctx : TypeContext)
    (fuel : Nat) : TypecheckM (List (Tag × Deps)) := do
  let sCaptured := VarTypeEnv.toCaptured ctx.varEnv
  VarTypeEnv.foldlM (init := ([] : List (Tag × Deps)))
    (fun acc name qt => matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel)
    ctx.varEnv

private lemma matchGuard_checkPredicate_ok_some_guardClosure
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (arg : PExpr) (qt : QTyp)
    (fuel : Nat)
    (k : Tag) (deps : Deps)
    (h :
      matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel = .ok (some (k, deps))) :
    ∃ arg_name pred_body var_env,
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  cases hpred : qt.pred with
  | noPred =>
      unfold matchGuard_checkPredicate at h
      have : False := by
        cases hchk : matchGuard_checkNoPredOnArrow qt <;> simp [hchk, hpred] at h
      exact False.elim this
  | guardOnly _ =>
      unfold matchGuard_checkPredicate at h
      have : False := by
        cases hchk : matchGuard_checkNoPredOnArrow qt <;> simp [hchk, hpred] at h
      exact False.elim this
  | guardClosure k' arg_name pred_body var_env =>
      unfold matchGuard_checkPredicate at h
      cases hchk : matchGuard_checkNoPredOnArrow qt with
      | error err =>
          have : False := by
            simp [hchk, hpred] at h
            cases h
          exact False.elim this
      | ok _ =>
          simp [hchk, hpred] at h
          by_cases huses : PExpr.usesArg arg_name pred_body = true
          · simp [huses] at h
            by_cases heqv :
                PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                  (some (arg_name, arg)) fuel = true
            · simp [heqv] at h
              cases hdeps : extractDepsFromPred (Predicate.guardClosure k' arg_name pred_body var_env) fuel with
              | error err =>
                  have : False := by
                    simp [hdeps] at h
                    cases h
                  exact False.elim this
              | ok d =>
                  simp [hdeps] at h
                  cases h
                  exact ⟨arg_name, pred_body, var_env, rfl⟩
            · simp [heqv] at h
          · simp [huses] at h

/-- From `matchGuard = .ok`, recover singleton structure of combined var/ref matches. -/
private lemma matchGuard_ok_allMatches_singleton
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    (conditionPExpr : PExpr)
    (fuel : Nat)
    (hcond : cond.toPExpr = .ok conditionPExpr)
  (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
  ∃ refMatches,
    matchGuard_refMatches conditionPExpr ctx fuel = .ok refMatches ∧
    matchGuard_varMatches conditionPExpr ctx fuel ++ refMatches = [(k, deps)] := by
  let varMatchesRaw : List (Tag × Deps) :=
    VarTypeEnv.foldl []
      (fun acc name qt =>
        let arg := PExpr.var name
        match matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) arg qt fuel with
        | .ok (some (tag, deps)) => (tag, deps) :: acc
        | .ok none => acc
        | .error _ => acc)
      ctx.varEnv
  have hmatch2 :
      (do
        let refMatches ← matchGuard_refMatches conditionPExpr ctx fuel
        match varMatchesRaw ++ refMatches with
        | [(tag, deps)] => pure (tag, deps)
        | [] => throw "No matching guard found for condition"
        | _ =>
            throw s!"Multiple matching guards found for condition: {repr (varMatchesRaw ++ refMatches)}") =
      .ok (k, deps) := by
    simpa [varMatchesRaw, matchGuard, hcond, matchGuard_refMatches, matchGuard_refStep,
      matchGuard_checkPredicate, matchGuard_checkNoPredOnArrow,
      bind, Except.bind] using hmatch
  cases href0 : matchGuard_refMatches conditionPExpr ctx fuel with
  | error err =>
      have hbad : (Except.error err : TypecheckM (Tag × Deps)) = .ok (k, deps) := by
        have htmp := hmatch2
        simp [href0, bind, Except.bind] at htmp
      cases hbad
  | ok refMatches =>
      refine ⟨refMatches, by simp, ?_⟩
      have hsingle_raw : varMatchesRaw ++ refMatches = [(k, deps)] := by
        have hmain :
            (match varMatchesRaw ++ refMatches with
            | [(tag, deps)] => Except.ok (tag, deps)
            | [] => Except.error "No matching guard found for condition"
            | _ =>
                Except.error s!"Multiple matching guards found for condition: {
                  repr (varMatchesRaw ++ refMatches)}")
              = Except.ok (k, deps) := by
          simpa [href0, bind, Except.bind] using hmatch2
        set allMatches : List (Tag × Deps) := varMatchesRaw ++ refMatches
        have hmain' :
            (match allMatches with
            | [(tag, deps)] => Except.ok (tag, deps)
            | [] => Except.error "No matching guard found for condition"
            | _ => Except.error s!"Multiple matching guards found for condition: {repr allMatches}")
              = Except.ok (k, deps) := by
          simpa [allMatches] using hmain
        cases hall : allMatches with
        | nil =>
            have : False := by
              simp [hall] at hmain'
            exact False.elim this
        | cons a as =>
            cases as with
            | nil =>
                have ha : a = (k, deps) := by
                  simpa [hall] using hmain'
                subst ha
                simp
            | cons b bs =>
                have : False := by
                  simp [hall] at hmain'
                exact False.elim this
      have hvarRaw_eq : varMatchesRaw = matchGuard_varMatches conditionPExpr ctx fuel := by
        unfold varMatchesRaw
        unfold matchGuard_varMatches
        refine congrArg (fun f => VarTypeEnv.foldl [] f ctx.varEnv) ?_
        funext acc name qt
        dsimp
        cases hcp :
            matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv)
              (PExpr.var name) qt fuel with
        | error err =>
            simp
        | ok opt =>
            cases opt <;> simp
      simpa [hvarRaw_eq] using hsingle_raw

/-- Singleton append split. -/
private lemma singleton_allMatches_implies_var_or_ref
    (varMatches refMatches : List (Tag × Deps)) (k : Tag) (deps : Deps)
    (hall : varMatches ++ refMatches = [(k, deps)]) :
    (k, deps) ∈ varMatches ∨ (k, deps) ∈ refMatches := by
  have hmem : (k, deps) ∈ varMatches ++ refMatches := by simp [hall]
  exact List.mem_append.mp hmem

private lemma var_match_from_varMatches_aux
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (fuel : Nat) :
    ∀ (entries : List (Name × QTyp)),
      (∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt) →
      ∀ (acc : List (Tag × Deps)),
      (∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) →
      ∀ kd, kd ∈ List.foldl
        (fun acc entry =>
          let name := entry.1
          let qt := entry.2
          let arg := PExpr.var name
          match matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel with
          | .ok (some kd) => kd :: acc
          | .ok none => acc
          | .error _ => acc) acc entries →
        ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env := by
  intro entries
  induction entries with
  | nil =>
      intro _hentries acc hacc kd hmem
      simpa using hacc kd hmem
  | cons entry entries ih =>
      intro hentries acc hacc kd hmem
      rcases entry with ⟨name, qt⟩
      have hlookup_name : ctx.varEnv.lookup name = some qt := by
        exact hentries name qt (by simp)
      set acc1 :=
        (match matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel with
        | .ok (some kd) => kd :: acc
        | .ok none => acc
        | .error _ => acc)
      have hacc1 :
          ∀ kd, kd ∈ acc1 →
            ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
              ctx.varEnv.lookup x = some qt ∧
              qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env := by
        intro kd' hmem'
        dsimp [acc1] at hmem'
        cases hcp : matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel with
        | error err =>
            simp [hcp] at hmem'
            exact hacc kd' hmem'
        | ok opt =>
            cases opt with
            | none =>
                simp [hcp] at hmem'
                exact hacc kd' hmem'
            | some kd0 =>
                simp [hcp] at hmem'
                rcases hmem' with hhead | htail
                · subst hhead
                  have hcp' :
                      matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel = .ok (some kd') := by
                    simp [hcp]
                  rcases matchGuard_checkPredicate_ok_some_guardClosure
                    conditionPExpr sCaptured (PExpr.var name) qt fuel kd'.1 kd'.2 hcp'
                    with ⟨arg_name, pred_body, var_env, hpred⟩
                  exact ⟨name, qt, arg_name, pred_body, var_env, hlookup_name, hpred⟩
                · exact hacc kd' htail
      have hentries_tail :
          ∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt := by
        intro name' qt' hmem'
        exact hentries name' qt' (List.mem_cons_of_mem _ hmem')
      exact ih hentries_tail acc1 hacc1 kd hmem

/-- Var-side extraction from varMatches membership. -/
private lemma var_match_from_varMatches
    (ctx : TypeContext) (conditionPExpr : PExpr) (k : Tag) (deps : Deps)
    (fuel : Nat)
    (hmem : (k, deps) ∈ matchGuard_varMatches conditionPExpr ctx fuel) :
    ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ctx.varEnv.lookup x = some qt ∧
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold matchGuard_varMatches at hmem
  rw [VarTypeEnv.foldl, Std.ExtTreeMap.foldl_eq_foldl_toList] at hmem
  have hentries_toList :
      ∀ name qt, (name, qt) ∈ ctx.varEnv.toList → ctx.varEnv.lookup name = some qt := by
    intro name qt hmemToList
    have hlookup : ctx.varEnv[name]? = some qt :=
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := ctx.varEnv)).1 hmemToList
    simpa [VarTypeEnv.lookup] using hlookup
  have h :=
    var_match_from_varMatches_aux ctx conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) fuel
      ctx.varEnv.toList hentries_toList [] (by intro kd h; cases h) (k, deps) hmem
  simpa using h

private def matchGuard_refPredFoldF (ctx : TypeContext)
    (accPred? : Option Predicate) (l : Loc) : TypecheckM (Option Predicate) := do
  match ctx.memEnv.lookup l with
  | some memQt =>
      matchGuard_checkNoPredOnArrow memQt
      let nextPred :=
        match accPred? with
        | none => memQt.pred
        | some p => joinPredicates p memQt.pred
      pure (some nextPred)
  | none => throw s!"Location {l} not found in memory environment during matchGuard"

private lemma list_foldlM_matchGuard_refPred_eq_guardClosure_from_some
    (ctx : TypeContext) :
    ∀ (xs : List Loc) (p0 : Predicate) (pred? : Option Predicate)
      (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      List.foldlM (matchGuard_refPredFoldF ctx) (some p0) xs = .ok pred? →
      pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
      p0 = Predicate.guardClosure k arg_name pred_body var_env ∧
      (∀ l ∈ xs, ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  induction xs with
  | nil =>
      intro p0 pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      subst hfold
      refine ⟨?_, ?_⟩
      · simpa using hpred
      · intro l hl
        cases hl
  | cons x xs ih =>
      intro p0 pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : matchGuard_refPredFoldF ctx (some p0) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : ctx.memEnv.lookup x with
          | none =>
              have hlookup' : ctx.memEnv.lookup x = none := hlookup
              have : False := by
                simp [matchGuard_refPredFoldF, hlookup'] at hfx
              exact False.elim this
          | some memQt =>
              have hlookup' : ctx.memEnv.lookup x = some memQt := hlookup
              cases hchk : matchGuard_checkNoPredOnArrow memQt with
              | error err =>
                  have : False := by
                    simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  exact False.elim this
              | ok _ =>
                  simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  cases hfx
                  have htail_fold :
                      List.foldlM (matchGuard_refPredFoldF ctx)
                        (some (joinPredicates p0 memQt.pred)) xs = .ok pred? := by
                    simpa using hfold
                  have hih :=
                    ih (joinPredicates p0 memQt.pred) pred? k arg_name pred_body var_env htail_fold hpred
                  have hjoin :=
                    joinPredicates_eq_guardClosure
                      (p := p0) (q := memQt.pred)
                      (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      hih.1
                  refine ⟨hjoin.1, ?_⟩
                  intro l hl
                  rcases (List.mem_cons.mp hl) with rfl | hltail
                  · refine ⟨memQt, ?_, hjoin.2⟩
                    simpa [MemoryTypeEnv.lookup] using hlookup
                  · exact hih.2 l hltail

private lemma list_foldlM_matchGuard_refPred_eq_guardClosure
    (ctx : TypeContext) :
    ∀ (xs : List Loc) (pred? : Option Predicate)
      (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      List.foldlM (matchGuard_refPredFoldF ctx) (none : Option Predicate) xs = .ok pred? →
      pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
      (∀ l ∈ xs, ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  cases xs with
  | nil =>
      intro pred? k arg_name pred_body var_env _hfold _hpred l hl
      cases hl
  | cons x xs =>
      intro pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : matchGuard_refPredFoldF ctx none x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : ctx.memEnv.lookup x with
          | none =>
              have hlookup' : ctx.memEnv.lookup x = none := hlookup
              have : False := by
                simp [matchGuard_refPredFoldF, hlookup'] at hfx
              exact False.elim this
          | some memQt =>
              have hlookup' : ctx.memEnv.lookup x = some memQt := hlookup
              cases hchk : matchGuard_checkNoPredOnArrow memQt with
              | error err =>
                  have : False := by
                    simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  exact False.elim this
              | ok _ =>
                  simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  cases hfx
                  have htail_fold :
                      List.foldlM (matchGuard_refPredFoldF ctx) (some memQt.pred) xs = .ok pred? := by
                    simpa using hfold
                  have htail :=
                    list_foldlM_matchGuard_refPred_eq_guardClosure_from_some
                      ctx xs memQt.pred pred? k arg_name pred_body var_env htail_fold hpred
                  intro l hl
                  rcases (List.mem_cons.mp hl) with rfl | hltail
                  · refine ⟨memQt, ?_, htail.1⟩
                    simpa [MemoryTypeEnv.lookup] using hlookup
                  · exact htail.2 l hltail

private lemma matchGuard_refPred_foldM_guardClosure
    (ctx : TypeContext) (ls : LocSet) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (hfold : LocSet.foldM ls (init := (none : Option Predicate)) (matchGuard_refPredFoldF ctx) = .ok pred?)
    (hpred : pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env) :
    ∀ l, l ∈ ls →
      ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hlist :=
    list_foldlM_matchGuard_refPred_eq_guardClosure
      ctx ls.toList pred? k arg_name pred_body var_env hfold hpred
  intro l hl
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact hlist l hl'

private lemma matchGuard_refStep_preserves_invariant
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (name : Name) (qt : QTyp) (acc acc1 : List (Tag × Deps))
    (fuel : Nat)
    (hlookup_name : ctx.varEnv.lookup name = some qt)
    (hacc :
      ∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env))
    (hstep : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .ok acc1) :
    ∀ kd, kd ∈ acc1 →
      ∃ (x : Name) (qt : QTyp) (ls : LocSet)
        (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
        ctx.varEnv.lookup x = some qt ∧
        qt.etyp = ETyp.ref ls ∧
        (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
            memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
  intro kd hmem
  have hstep0 : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .ok acc1 := hstep
  unfold matchGuard_refStep at hstep
  cases hEt : qt.etyp with
  | ref ls =>
      by_cases hpoisonT : qt.poison = true
      · simp [hEt, hpoisonT] at hstep
        cases hstep
        exact hacc kd hmem
      · have hpoisonF : qt.poison = false := by
          cases hq : qt.poison with
          | false =>
              rfl
          | true =>
              simp [hq] at hpoisonT
        by_cases hlsEmptyT : ls.isEmpty = true
        · simp [hEt, hpoisonF, hlsEmptyT] at hstep
        · cases hmerged :
            LocSet.foldM ls (init := (none : Option Predicate))
              (fun accPred? l => do
                match ctx.memEnv.lookup l with
                | some memQt =>
                    matchGuard_checkNoPredOnArrow memQt
                    let nextPred :=
                      match accPred? with
                      | none => memQt.pred
                      | some p => joinPredicates p memQt.pred
                    pure (some nextPred)
                | none => throw s!"Location {l} not found in memory environment during matchGuard") with
          | error err =>
              have hlsEmptyF : ls.isEmpty = false := by
                cases hls : ls.isEmpty with
                | false =>
                    rfl
                | true =>
                    simp [hls] at hlsEmptyT
              have hstepErr :
                  matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .error err := by
                unfold matchGuard_refStep
                try simp [hEt, hpoisonF, hlsEmptyF]
                erw [hmerged]
                simp [bind, Except.bind]
              have : False := by
                rw [hstepErr] at hstep0
                simp at hstep0
              exact False.elim this
          | ok merged? =>
              have hlsEmptyF : ls.isEmpty = false := by
                cases hls : ls.isEmpty with
                | false =>
                    rfl
                | true =>
                    simp [hls] at hlsEmptyT
              cases hdeps :
                  LocSet.foldM ls (init := LocSet.empty) (fun dacc l => do
                    match ctx.memEnv.lookup l with
                    | some memQt =>
                        matchGuard_checkNoPredOnArrow memQt
                        let deps ← extractDepsFromPred memQt.pred fuel
                        pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
                    | none => throw s!"Location {l} not found in memory environment during matchGuard") with
                | error err =>
                  have hstepErr :
                      matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .error err := by
                    unfold matchGuard_refStep
                    -- Simplify outer control-flow first, then rewrite the computed folds.
                    simp [hEt, hpoisonF, hlsEmptyF]
                    erw [hmerged]
                    erw [hdeps]
                    simp [bind, Except.bind]
                  have : False := by
                    rw [hstepErr] at hstep0
                    simp at hstep0
                  exact False.elim this
                | ok depsMerged =>
                  cases hmg : merged?.getD Predicate.noPred with
                  | noPred =>
                      have hacc1eq : acc1 = acc := by
                        have hstep' := hstep0
                        unfold matchGuard_refStep at hstep'
                        simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                        erw [hmerged] at hstep'
                        erw [hdeps] at hstep'
                        simp [bind, Except.bind] at hstep'
                        erw [hmg] at hstep'
                        simp at hstep'
                        cases hstep'
                        rfl
                      subst hacc1eq
                      exact hacc kd hmem
                  | guardOnly gk =>
                      have hacc1eq : acc1 = acc := by
                        have hstep' := hstep0
                        unfold matchGuard_refStep at hstep'
                        simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                        erw [hmerged] at hstep'
                        erw [hdeps] at hstep'
                        simp [bind, Except.bind] at hstep'
                        erw [hmg] at hstep'
                        simp at hstep'
                        cases hstep'
                        rfl
                      subst hacc1eq
                      exact hacc kd hmem
                  | guardClosure tag arg_name pred_body var_env =>
                      by_cases husesT : PExpr.usesArg arg_name pred_body = true
                      · by_cases heqvT :
                          PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                            (some (arg_name, PExpr.deref (PExpr.var name))) fuel = true
                        · have hacc1eq : acc1 = (tag, depsMerged) :: acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            simp [husesT, heqvT] at hstep'
                            cases hstep'
                            rfl
                          subst hacc1eq
                          rcases (List.mem_cons.mp hmem) with hhead | htail
                          · subst hhead
                            refine ⟨name, qt, ls, arg_name, pred_body, var_env, hlookup_name, hEt, ?_⟩
                            have hmerged' :
                                LocSet.foldM ls (init := (none : Option Predicate))
                                  (matchGuard_refPredFoldF ctx) = .ok merged? := by
                              simpa [matchGuard_refPredFoldF] using hmerged
                            have hls :
                                ∀ l, l ∈ ls →
                                  ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                                    memQt.pred =
                                      Predicate.guardClosure tag arg_name pred_body var_env :=
                              matchGuard_refPred_foldM_guardClosure
                                ctx ls merged? tag arg_name pred_body var_env hmerged'
                                (by simp [hmg])
                            exact hls
                          · exact hacc kd htail
                        · have heqvF :
                              PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                (some (arg_name, PExpr.deref (PExpr.var name))) fuel = false := by
                            cases heqv :
                                PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                  (some (arg_name, PExpr.deref (PExpr.var name))) fuel with
                            | false =>
                                rfl
                            | true =>
                                simp [heqv] at heqvT
                          have hacc1eq : acc1 = acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            simp [husesT, heqvF] at hstep'
                            cases hstep'
                            rfl
                          subst hacc1eq
                          exact hacc kd hmem
                      · have husesF : PExpr.usesArg arg_name pred_body = false := by
                          cases huses : PExpr.usesArg arg_name pred_body with
                          | false =>
                              rfl
                          | true =>
                              simp [huses] at husesT
                        have hacc1eq : acc1 = acc := by
                          have hstep' := hstep0
                          unfold matchGuard_refStep at hstep'
                          -- Avoid fragile `rw/erw` matching on folded expressions; `simp` with the
                          -- computed fold equalities is stable under definitional unfolding.
                          simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                          erw [hmerged] at hstep'
                          erw [hdeps] at hstep'
                          simp [bind, Except.bind] at hstep'
                          erw [hmg] at hstep'
                          simp [husesF] at hstep'
                          cases hstep'
                          rfl
                        subst hacc1eq
                        exact hacc kd hmem
    | int =>
        simp [hEt] at hstep
        cases hstep
        exact hacc kd hmem
  | bool =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | unit =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | arrow t1 t2 p1 p2 =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | parrow t1 t2 p1 p2 =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | string =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem

private lemma ref_match_from_refMatches_aux
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (fuel : Nat) :
    ∀ (entries : List (Name × QTyp)),
      (∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt) →
      ∀ (acc : List (Tag × Deps)),
      (∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env)) →
      ∀ acc',
        List.foldlM (fun acc entry => matchGuard_refStep conditionPExpr sCaptured ctx acc entry fuel) acc entries =
          .ok acc' →
      ∀ kd, kd ∈ acc' →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
  intro entries
  induction entries with
  | nil =>
      intro _hentries acc hacc acc' hfold kd hmem
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      simpa using hacc kd hmem
  | cons entry entries ih =>
      intro hentries acc hacc acc' hfold kd hmem
      rcases entry with ⟨name, qt⟩
      have hlookup_name : ctx.varEnv.lookup name = some qt := by
        exact hentries name qt (by simp)
      cases hstep : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel with
      | error err =>
          simp [List.foldlM_cons, hstep, bind, Except.bind] at hfold
      | ok acc1 =>
          simp [List.foldlM_cons, hstep, bind, Except.bind] at hfold
          have hacc1 :
              ∀ kd, kd ∈ acc1 →
                ∃ (x : Name) (qt : QTyp) (ls : LocSet)
                  (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
                  ctx.varEnv.lookup x = some qt ∧
                  qt.etyp = ETyp.ref ls ∧
                  (∀ l, l ∈ ls →
                    ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                      memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
            exact
              matchGuard_refStep_preserves_invariant
                ctx conditionPExpr sCaptured name qt acc acc1 fuel hlookup_name hacc hstep
          have hentries_tail :
              ∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt := by
            intro name' qt' hmem'
            exact hentries name' qt' (List.mem_cons_of_mem _ hmem')
          exact ih hentries_tail acc1 hacc1 acc' hfold kd hmem

/-- Ref-side extraction from refMatches membership. -/
private lemma ref_match_from_refMatches
    (ctx : TypeContext) (conditionPExpr : PExpr) (k : Tag) (deps : Deps)
    (refMatches : List (Tag × Deps))
    (fuel : Nat)
    (href : matchGuard_refMatches conditionPExpr ctx fuel = .ok refMatches)
    (hmem : (k, deps) ∈ refMatches) :
    ∃ (x : Name) (qt : QTyp) (ls : LocSet)
      (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ctx.varEnv.lookup x = some qt ∧
      qt.etyp = ETyp.ref ls ∧
      (∀ l, l ∈ ls →
        ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  unfold matchGuard_refMatches at href
  rw [VarTypeEnv.foldlM, Std.ExtTreeMap.foldlM_eq_foldlM_toList] at href
  cases hfold :
      List.foldlM
        (fun acc entry =>
          matchGuard_refStep conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) ctx acc entry fuel)
        [] ctx.varEnv.toList with
  | error err =>
      simp [hfold] at href
  | ok rms =>
      simp [hfold] at href
      subst href
      exact
        ref_match_from_refMatches_aux ctx conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) fuel
          ctx.varEnv.toList
          (by
            intro name qt hmemToList
            have hlookup : ctx.varEnv[name]? = some qt :=
              (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := ctx.varEnv)).1 hmemToList
            simpa [VarTypeEnv.lookup] using hlookup)
          [] (by intro kd h; cases h) rms hfold (k, deps) hmem

/-- Successful `matchGuard` implies the condition has a pure-expression view. -/
private lemma matchGuard_ok_toPExpr?_some
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ conditionPExpr, Expr.toPExpr? cond = some conditionPExpr := by
  cases hcond : cond.toPExpr with
  | error _err =>
      unfold matchGuard at hmatch
      simp [hcond] at hmatch
      cases hmatch
  | ok conditionPExpr =>
      exact ⟨conditionPExpr, Expr_toPExpr?_eq_some_of_toPExpr_ok cond conditionPExpr hcond⟩

private lemma qtypCleanUnder_transport_pure_regime_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr .ioFree { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ qt, qtypCleanUnder ctx.regime qt → qtypCleanUnder res.regime' qt := by
  intro qt hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hreg' : res.regime'.lookup? k = some true :=
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctx) (e := e) (pe := pe) (fuel := fuel) (res := res)
          hpe htc k true hreg
      exact qtypCleanUnder.guard k htag hreg' hnotfun

private lemma runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
    (ctx : TypeContext) (res : TypeResult) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (k : Tag) (deps : Deps)
    (hsub : ∀ l, res.memEnv'.contains l → ctx.memEnv.contains l)
    (hric :
      runtimeInstantiatesCtx
        (ctxAfter { ctx with pureCtx := true } res)
        μ ρ θ) :
    runtimeInstantiatesCtx
      { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      μ ρ θ := by
  rcases hric with ⟨hmem, hvar⟩
  unfold runtimeInstantiatesCtx
  constructor
  · intro l a hlookup
    rcases hmem l a hlookup with ⟨hcontainsRes, hcontainsMem⟩
    exact ⟨hsub l hcontainsRes, hcontainsMem⟩
  · intro x qt hlookup
    have hlookup' :
        (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    exact hvar hlookup'

private lemma consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
    (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (kTrue : Tag) (depsTrue : Deps)
    (hreg_bridge :
      ∀ k b, ctx.regime.lookup? k = some b → res.regime'.lookup? k = some b)
    (hmem_bridge :
      ∀ l qt k,
        ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k →
        ctx.regime.lookup? k ≠ none →
        res.memEnv'.lookup l = some qt)
    (hcwr :
      consistentWithRegime predSat
        (ctxAfter { ctx with pureCtx := true } res).regime
        (ctxAfter { ctx with pureCtx := true } res) μ ρ θ) :
    consistentWithRegime predSat
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }) μ ρ θ := by
  unfold consistentWithRegime at hcwr ⊢
  constructor
  · intro l qt k hlookup hguard hRdef
    have hlookupRes : res.memEnv'.lookup l = some qt := hmem_bridge l qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hloc :=
          hcwr.1 l qt k
            (by
              unfold ctxAfter
              exact hlookupRes)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        cases hloc with
        | noPred_ok hpred =>
            exact locsRegime.noPred_ok (l, qt) hpred
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b' hclos hregime hreal hmem hconsist =>
            have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
              simpa using hclos
            have htag_qt : qtypGuardTag qt = some k' := by
              simp [qtypGuardTag, hclos']
            have hkEq : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag_qt
                  _ = some k := hguard
              exact Option.some.inj this
            have hbEq : b' = b := by
              have : some b' = some b := by
                calc
                  some b' = res.regime'.lookup? k' := hregime.symm
                  _ = res.regime'.lookup? k := by simp [hkEq]
                  _ = some b := hbres
              exact Option.some.inj this
            have hbctx' : ctx.regime.lookup? k' = some b' := by
              calc
                ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                _ = some b := hbctx
                _ = some b' := by simp [hbEq]
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b'
                hclos hbctx' hreal hmem hconsist
  · constructor
    · intro x qt k hlookup hguard hRdef
      cases hbctx : ctx.regime.lookup? k with
      | none =>
          exact False.elim (hRdef hbctx)
      | some b =>
          have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
          have hvar :=
            hcwr.2.1 x qt k
              (by
                unfold ctxAfter
                exact hlookup)
              hguard
              (by
                unfold ctxAfter
                intro hnone
                rw [hbres] at hnone
                contradiction)
          cases hvar with
          | noPred_ok hpred =>
              exact varsRegime.noPred_ok (x, qt) hpred
          | guardOnly_ok k' hgo =>
              exact varsRegime.guardOnly_ok (x, qt) k' hgo
          | withPred_ok k' arg_name pred_body var_env v b' hclos hregime hvarLookup hconsist =>
              have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                simpa using hclos
              have htag_qt : qtypGuardTag qt = some k' := by
                simp [qtypGuardTag, hclos']
              have hkEq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by symm; exact htag_qt
                    _ = some k := hguard
                exact Option.some.inj this
              have hbEq : b' = b := by
                have : some b' = some b := by
                  calc
                    some b' = res.regime'.lookup? k' := hregime.symm
                    _ = res.regime'.lookup? k := by simp [hkEq]
                    _ = some b := hbres
                exact Option.some.inj this
              have hbctx' : ctx.regime.lookup? k' = some b' := by
                calc
                  ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                  _ = some b := hbctx
                  _ = some b' := by simp [hbEq]
              exact
                varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b'
                  hclos hbctx' hvarLookup hconsist
    · intro x qt v hlookup hlookup_v
      have hlookupRes :
          (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
        unfold ctxAfter
        exact hlookup
      have hcapRes :
          closureCapturedVarsRegime predSat
            (ctxAfter { ctx with pureCtx := true } res).regime
            qt μ θ v :=
        hcwr.2.2 x qt v hlookupRes hlookup_v
      exact
        closureCapturedVarsRegime_transport_lookup_back
          (predSat := predSat)
          (R := (ctxAfter { ctx with pureCtx := true } res).regime)
          (R' := ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime)
          (μ := μ)
          (hlookup_back := by
            intro k b hk
            simpa [ctxAfter] using hreg_bridge k b hk)
          hcapRes

/-- Extract a context-level guard owner from successful `matchGuard`. -/
private lemma matchGuard_ok_extract_owner_in_ctx
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      ∨
      (∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ) ) := by
  have hcond_ok : ∃ conditionPExpr, cond.toPExpr = .ok conditionPExpr := by
    rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
    have hcond_ok' : cond.toPExpr = .ok conditionPExpr := by
      unfold Expr.toPExpr
      rw [hcond_some]
      simp [pure, Except.pure]
    exact ⟨conditionPExpr, hcond_ok'⟩
  rcases hcond_ok with ⟨conditionPExpr, hcond⟩
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  have hvar_or_href :=
    singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall
  rcases hvar_or_href with hvar | hrefMem
  · left
    exact var_match_from_varMatches ctx conditionPExpr k deps fuel hvar
  · right
    exact ref_match_from_refMatches ctx conditionPExpr k deps refMatches fuel href hrefMem

/-- Lift a context-level owner witness to the runtime owner witness shape used by `match_iff`. -/
private lemma owner_in_ctx_to_runtime_owner_witness
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (k : Tag)
    (hctx :
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
        ∨
        (∃ (x : Name) (qt : QTyp) (ls : LocSet)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            (∀ l, l ∈ ls →
              ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ) ))
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    ∃ v,
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          ρ.lookup x = some v)
        ∨
        (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          ctx.memEnv.lookup l0 = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) := by
  rcases hric with ⟨hmemInst, hvarInst⟩
  rcases hctx with hvar | href
  · rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred⟩
    rcases hvarInst hlookup with ⟨v, hρ, _⟩
    exact ⟨v, Or.inl ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred, hρ⟩⟩
  · rcases href with ⟨x, qt, ls, arg_name, pred_body, var_env, hlookup, hetyp, hall⟩
    rcases hvarInst hlookup with ⟨v0, _hρ, hvtyp⟩
    have hvtyp_ref : valueHasETyp θ v0 (ETyp.ref ls) := by
      simpa [hetyp] using hvtyp
    cases hvtyp_ref with
    | loc hθ hin =>
        rename_i a l0
        have hμcontains : μ.contains a = true := (hmemInst l0 a hθ).2
        rcases Memory_lookup_some_of_contains hμcontains with ⟨n, hμ⟩
        rcases hall l0 hin with ⟨memQt, hlookupMem, hpredMem⟩
        exact ⟨Value.num n, Or.inr
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hin, hlookupMem, hpredMem, hθ, hμ, rfl⟩⟩

/-- If `matchGuard` succeeds at `(k,deps)`, there is a runtime owner witness for tag `k`
    under any runtime that instantiates `ctx`. -/
private lemma matchGuard_ok_runtime_owner
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    ∃ v,
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          ρ.lookup x = some v)
        ∨
        (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          ctx.memEnv.lookup l0 = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) := by
  have hctx := matchGuard_ok_extract_owner_in_ctx ctx cond k deps hmatch
  exact owner_in_ctx_to_runtime_owner_witness ctx μ ρ θ k hctx hric

/-- Optional local helper for the `ite` FR modes.
    Shows the guard evaluation boolean is aligned with the regime value once
    `matchGuard` succeeds and an owner witness is available.

    NOTE: `howner` is the runtime owner-witness needed by `PredSatLaws.match_iff`
    (premise (iii)). At intended call sites, derive it via bridge lemmas:
    `matchGuard_ok_owner_in_ctx` then `owner_in_ctx_to_runtime`.
    Sketch:
    `matchGuard_ok_owner_in_ctx`:
      `matchGuard cond ctx.memEnv ctx.varEnv = .ok (k,deps) →`
      `∃ owner, ownerHasGuardTagInCtx ctx cond k owner`
    `owner_in_ctx_to_runtime`:
      `runtimeInstantiatesCtx ctx μ ρ θ → ownerHasGuardTagInCtx ctx cond k owner →`
      `∃ v, ownerWitnessAtRuntime owner μ ρ θ v`
    This helper itself does not need `runtimeInstantiatesCtx`; that premise
    is expected while constructing `howner` via the bridge lemmas. -/
private lemma guard_branch_alignment
    (predSat : PredSat) (tm : TagMeaning) (mode : LeanPoison.EvalMode)
    (ctx : TypeContext) (μ₀ : Memory) (ρ₀ : VarEnv) (θ₀ : RealizationMap)
    (l₀ : Address) (pm₀ : Bool)
    (hwfTm : wfTagMeaningCtx tm ctx) (hpred : PredSatLaws predSat tm)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config)
    {fuel : Nat}
    (howner :
      ∃ v,
        ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            ρ₀.lookup x = some v)
          ∨
          (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
              (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            l0 ∈ ls ∧
            ctx.memEnv.lookup l0 = some memQt ∧
            memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            θ₀.lookup l0 = some a ∧
            μ₀.lookup a = some n ∧
            v = Value.num n) ) ) :
    matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    terminatesTo mode cond
      { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
      cfg' (Value.bool b') →
    b' = b := by
  intro hmatch hregime hterm
  rcases howner with ⟨v, hv_owner⟩
  have hmatch_iff_v : (b' = true ↔ predSat k μ₀ v) := by
    apply hpred.match_iff mode cond ctx.memEnv ctx.varEnv fuel k deps
      μ₀ ρ₀ θ₀ l₀ pm₀ cfg' v b'
    · exact hwfTm
    · exact hmatch
    · exact hterm
    · cases hv_owner with
      | inl hvar =>
          rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
          left
          refine ⟨x, qt, hlookup, ?_, hvar⟩
          simp [qtypGuardTag, hpred_qt]
      | inr href =>
          rcases href with
            ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
              hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
          right
          refine ⟨x, qt, memQt, ls, l0, a, n, hlookup, hetyp, hIn, hlookupMem, ?_, hθ, hμ, hv⟩
          simp [qtypGuardTag, hpred_memQt]
  have hRdef : ctx.regime.lookup? k ≠ none := by
    simp [hregime]
  have hpred_implies_lookup_true : predSat k μ₀ v → ctx.regime.lookup? k = some true := by
    intro hsat
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ ρ₀ (x, qt) :=
          hcwr.2.1 x qt k hlookup htag_qt hRdef
        cases hvr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_qt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_qt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 v1 b1 hclos hregime1 hvar1 hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = qt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_qt
              cases hEq
              rfl
            have hv1 : v1 = v := by
              have : some v1 = some v := by simpa [hvar1] using hvar
              exact Option.some.inj this
            by_cases hb1t : b1 = true
            ·
              have hlookup_k_b1 : ctx.regime.lookup? k = some b1 := by
                simpa [hk] using hregime1
              simpa [hb1t] using hlookup_k_b1
            · have hb1f : b1 = false := by
                cases b1 <;> simp at hb1t ⊢
              have hnot : ¬ qtypPredHolds predSat qt μ₀ v1 := hconsist.2 hb1f
              have hsat1 : predSat k1 μ₀ v1 := by
                simpa [hk, hv1] using hsat
              have hholds : qtypPredHolds predSat qt μ₀ v1 :=
                qtypPredHolds.guardClosure_ok hclos hsat1
              exact False.elim (hnot hholds)
    | inr href =>
        rcases href with
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
        have htag_memQt : qtypGuardTag memQt = some k := by
          simp [qtypGuardTag, hpred_memQt]
        have hlr : locsRegime predSat ctx.regime μ₀ θ₀ (l0, memQt) :=
          hcwr.1 l0 memQt k hlookupMem htag_memQt hRdef
        cases hlr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_memQt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_memQt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 a1 n1 b1 hclos hregime1 hreal hmem hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = memQt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_memQt
              cases hEq
              rfl
            have ha : a1 = a := by
              have : some a1 = some a := by simpa [hreal] using hθ
              exact Option.some.inj this
            have hmemA : μ₀.lookup a = some n1 := by
              simpa [ha] using hmem
            have hn : n1 = n := by
              have : some n1 = some n := by simpa [hmemA] using hμ
              exact Option.some.inj this
            have hv_num : v = Value.num n1 := by
              calc
                v = Value.num n := hv
                _ = Value.num n1 := by simp [hn]
            by_cases hb1t : b1 = true
            ·
              have hlookup_k_b1 : ctx.regime.lookup? k = some b1 := by
                simpa [hk] using hregime1
              simpa [hb1t] using hlookup_k_b1
            · have hb1f : b1 = false := by
                cases b1 <;> simp at hb1t ⊢
              have hnot : ¬ qtypPredHolds predSat memQt μ₀ (Value.num n1) := hconsist.2 hb1f
              have hsat_num : predSat k1 μ₀ (Value.num n1) := by
                simpa [hk, hv_num] using hsat
              have hholds : qtypPredHolds predSat memQt μ₀ (Value.num n1) :=
                qtypPredHolds.guardClosure_ok hclos hsat_num
              exact False.elim (hnot hholds)
  have hlookup_true_implies_pred : ctx.regime.lookup? k = some true → predSat k μ₀ v := by
    intro hktrue
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ ρ₀ (x, qt) :=
          hcwr.2.1 x qt k hlookup htag_qt hRdef
        cases hvr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_qt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_qt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 v1 b1 hclos hregime1 hvar1 hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = qt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_qt
              cases hEq
              rfl
            have hv1 : v1 = v := by
              have : some v1 = some v := by simpa [hvar1] using hvar
              exact Option.some.inj this
            have hb1t : b1 = true := by
              have hlookup_k1_true : ctx.regime.lookup? k1 = some true := by
                simpa [hk] using hktrue
              have : some b1 = some true := by simpa [hregime1] using hlookup_k1_true
              exact Option.some.inj this
            have hholds : qtypPredHolds predSat qt μ₀ v1 := hconsist.1 hb1t
            cases hholds with
            | noPred_ok hnp =>
                exfalso
                simp [hpred_qt] at hnp
            | guardOnly_ok hgo _ =>
                exfalso
                simp [hpred_qt] at hgo
            | guardClosure_ok hclos' hsat' =>
                rename_i k2 arg2 body2 env2
                have hk2 : k2 = k1 := by
                  have hEq :
                      Predicate.guardClosure k2 arg2 body2 env2 =
                      Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := by
                    calc
                      Predicate.guardClosure k2 arg2 body2 env2 = qt.pred := by
                        symm; exact hclos'
                      _ = Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := hclos
                  cases hEq
                  rfl
                subst hk2
                simpa [hk, hv1] using hsat'
    | inr href =>
        rcases href with
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
        have htag_memQt : qtypGuardTag memQt = some k := by
          simp [qtypGuardTag, hpred_memQt]
        have hlr : locsRegime predSat ctx.regime μ₀ θ₀ (l0, memQt) :=
          hcwr.1 l0 memQt k hlookupMem htag_memQt hRdef
        cases hlr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_memQt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_memQt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 a1 n1 b1 hclos hregime1 hreal hmem hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = memQt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_memQt
              cases hEq
              rfl
            have ha : a1 = a := by
              have : some a1 = some a := by simpa [hreal] using hθ
              exact Option.some.inj this
            have hmemA : μ₀.lookup a = some n1 := by
              simpa [ha] using hmem
            have hn : n1 = n := by
              have : some n1 = some n := by simpa [hmemA] using hμ
              exact Option.some.inj this
            have hv_num : v = Value.num n1 := by
              calc
                v = Value.num n := hv
                _ = Value.num n1 := by simp [hn]
            have hb1t : b1 = true := by
              have hlookup_k1_true : ctx.regime.lookup? k1 = some true := by
                simpa [hk] using hktrue
              have : some b1 = some true := by simpa [hregime1] using hlookup_k1_true
              exact Option.some.inj this
            have hholds : qtypPredHolds predSat memQt μ₀ (Value.num n1) := hconsist.1 hb1t
            have hsat_num : predSat k1 μ₀ (Value.num n1) := by
              cases hholds with
              | noPred_ok hnp =>
                  exfalso
                  simp [hpred_memQt] at hnp
              | guardOnly_ok hgo _ =>
                  exfalso
                  simp [hpred_memQt] at hgo
              | guardClosure_ok hclos' hsat' =>
                  rename_i k2 arg2 body2 env2
                  have hk2 : k2 = k1 := by
                    have hEq :
                        Predicate.guardClosure k2 arg2 body2 env2 =
                        Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := by
                      calc
                        Predicate.guardClosure k2 arg2 body2 env2 = memQt.pred := by
                          symm; exact hclos'
                        _ = Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := hclos
                    cases hEq
                    rfl
                  subst hk2
                  exact hsat'
            simpa [hk, hv_num] using hsat_num
  have hb'_iff : (b' = true ↔ b = true) := by
    constructor
    · intro hb'true
      have hsat : predSat k μ₀ v := hmatch_iff_v.mp hb'true
      have hktrue : ctx.regime.lookup? k = some true := hpred_implies_lookup_true hsat
      have : some b = some true := by simpa [hregime] using hktrue
      exact Option.some.inj this
    · intro hbtrue
      have hktrue : ctx.regime.lookup? k = some true := by
        simp [hregime, hbtrue]
      have hsat : predSat k μ₀ v := hlookup_true_implies_pred hktrue
      exact hmatch_iff_v.mpr hsat
  cases b <;> cases b' <;> simp at hb'_iff ⊢

private lemma stepFR_ite_mode1
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_true : ctxᵢ.regime.lookup? k = some true)
  (res1 res2 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          typecheckExpr .ioFree ctxTrue e2 fuel' = .ok res2)
  (hmemEnv : res.memEnv' = res2.memEnv')
  (htagEnv : res.tagEnv' = res2.tagEnv')
  (hnextLoc : res.nextLoc' = res2.nextLoc')
  (hnextTag : res.nextTag' = res2.nextTag')
  (hregime' : res.regime' = res2.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res2.qualType.poison)
  (hetyp : res.qualType.etyp = res2.qualType.etyp) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwfTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  have hb₀_true : b₀ = true := by
    have howner₀ := matchGuard_ok_runtime_owner ctxᵢ μ₀ ρ₀ θ₀ e1 k deps hmatch hric₀
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps true b₀ cfg₀1
        howner₀
        hmatch hregime_true ht₀_e1
  have hb₁_true : b₁ = true := by
    have howner₁ := matchGuard_ok_runtime_owner ctxᵢ μ₁ ρ₁ θ₁ e1 k deps hmatch hric₁
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps true b₁ cfg₁1
        howner₁
        hmatch hregime_true ht₁_e1
  have ht₀_e2 : terminatesTo .ioFree e2 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₀_true]
        contradiction
  have ht₁_e2 : terminatesTo .ioFree e2 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₁_true]
        contradiction
  let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
  have htc2' : typecheck .ioFree ctxTrue e2 fuel' = .ok res2 := by
    simpa [typecheck, Nat.succ_sub_one] using htc2
  have hwfTm_true : wfTagMeaningCtx tm ctxTrue := by
    simpa [wfTagMeaningCtx, ctxTrue] using hwfTm
  have hIH_e2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctxTrue hwfTm_true res2 htc2'
  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred := by
    have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
      native_decide
    unfold typecheckIf at htcIf
    erw [hmatch] at htcIf
    simp [hregime_true, heq, bind, Except.bind] at htcIf
    rw [htc1] at htcIf
    simp at htcIf
    cases hq1 : res1.qualType with
    | mk etyp1 p1 pred1 =>
        simp [hq1] at htcIf
        have hbool1 : etyp1 = ETyp.bool := by
          simpa [hq1] using hbool
        rw [hbool1] at htcIf
        simp [htc2, pure, Except.pure] at htcIf
        cases hq2 : res2.qualType with
        | mk etyp2 p2 pred2 =>
            simp [hq2] at htcIf
            cases htcIf
            rfl
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_true : wfTypeContext ctxTrue := by
    simpa [wfTypeContext, ctxTrue] using hwf
  have hric₀1' : runtimeInstantiatesCtx ctxTrue cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hsub₀ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    exact
      runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
        (ctx := ctxᵢ) (res := res1) (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
        (k := k) (deps := deps)
        hsub₀ hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctxTrue cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hsub₁ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    exact
      runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
        (ctx := ctxᵢ) (res := res1) (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
        (k := k) (deps := deps)
        hsub₁ hric₁1
  have htagR_true : regimeConsistentWithCtx ctxTrue := by
    unfold regimeConsistentWithCtx at htagR ⊢
    constructor
    · exact tagEnvConsistentWithRegime_insert_true
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR.1 hregime_true
    · simpa [ctxTrue] using htagR.2
  have hRbound_true : regimeBounded ctxTrue.regime := by
    simpa [ctxTrue] using hRbound
  have hcwr₀1' : consistentWithRegime predSat ctxTrue.regime ctxTrue cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    refine
      consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
        (predSat := predSat) (ctx := ctxᵢ) (res := res1)
        (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
        (kTrue := k) (depsTrue := deps)
        ?hreg_bridge ?hmem_bridge hcwr₀1
    · intro k' b hk
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b hk
    · intro l qt k' hlookup hguard hRdef
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt k' hlookup hguard hRdef
  have hcwr₁1' : consistentWithRegime predSat ctxTrue.regime ctxTrue cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    refine
      consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
        (predSat := predSat) (ctx := ctxᵢ) (res := res1)
        (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
        (kTrue := k) (depsTrue := deps)
        ?hreg_bridge1 ?hmem_bridge1 hcwr₁1
    · intro k' b hk
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b hk
    · intro l qt k' hlookup hguard hRdef
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt k' hlookup hguard hRdef
  have hagree1' :
      agreeOnClean predSat ctxTrue.regime ctxTrue
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    have hcleanBack :
        ∀ qt, qtypCleanUnder ctxTrue.regime qt → qtypCleanUnder res1.regime' qt := by
      intro qt hclean
      exact
        qtypCleanUnder_transport_pure_regime_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 qt (by simpa [ctxTrue] using hclean)
    have hlookupBackAll :
        ∀ k' b, ctxTrue.regime.lookup? k' = some b → res1.regime'.lookup? k' = some b := by
      intro k' b hk
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxTrue] using hk)
    have hmemberVars₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₀1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberCvcr₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberCvcrEvidence predSat ctxTrue.regime cfg₀1.memory θ₀1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberVars₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₁1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    have hmemberCvcr₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberCvcrEvidence predSat ctxTrue.regime cfg₁1.memory θ₁1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    constructor
    · intro l qt hlookup hclean
      have hlookupRes :
          res1.memEnv'.lookup l = some qt :=
        typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt (by simpa [ctxTrue] using hlookup)
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeLocUnder predSat res1.regime'
            cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt) :=
        hagree1.1 l qt (by simpa [ctxAfter] using hlookupRes) hcleanRes
      cases hagreeRes with
      | both_unrealized l qt hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxTrue.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxTrue.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV'
    · intro x qt hlookup hclean
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeVarUnder predSat res1.regime'
            cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
        hagree1.2 x qt (by simpa [ctxAfter, ctxTrue] using hlookup) hcleanRes
      cases hagreeRes with
      | both_none x qt hnone₀ hnone₁ =>
          exact agreeVarUnder.both_none x qt hnone₀ hnone₁
      | agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxTrue.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxTrue.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV'
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq :
      cfg₁1 =
        { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
          pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e2 :=
    hIH_e2 hpredlaws hwfTm_true
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_true hric₀1' hric₁1' htagR_true hRbound_true
      hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, hwfcf₀2, hwfcf₁2,
      hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₀2, _hvalc₁2, hres_agree2⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxTrue res2 := by
    simp [ctxAfter, ctxTrue, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree2
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm res2.qualType res.qualType hresTm2 hetyp hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · simpa [hetyp] using _hvtyp₀2
  · simpa [hetyp] using _hvtyp₁2
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₀.memory θ₀2 o₀ := by
        simpa [hctxAfter] using hcap₂
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₂'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₁.memory θ₁2 o₁ := by
        simpa [hctxAfter] using hcap₂
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₂'
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
        calc
          joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by
            symm
            exact hpoison
          _ = false := hpoison_res
      exact (joinPoison_eq_false hjoin).2
    have hclean2 : qtypCleanUnder (ctxAfter ctxᵢ res).regime res2.qualType := by
      cases hclean with
      | clean hpoison_res =>
          exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k' htag _hreg _hnotfun =>
          exfalso
          simp [qtypGuardTag, hpredNo] at htag
    have hres_agree2' :
        resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      simpa [hctxAfter] using hres_agree2
    have hagree2' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ :=
      hres_agree2' hclean2
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree2'

-- Mode 2: R(k) = some false (else-branch effective)
private lemma stepFR_ite_mode2
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_false : ctxᵢ.regime.lookup? k = some false)
  (res1 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc3 : let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩ }
          typecheckExpr .ioFree ctxFalse e3 fuel' = .ok res3)
  (hmemEnv : res.memEnv' = res3.memEnv')
  (htagEnv : res.tagEnv' = res3.tagEnv')
  (hnextLoc : res.nextLoc' = res3.nextLoc')
  (hnextTag : res.nextTag' = res3.nextTag')
  (hregime' : res.regime' = res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res3.qualType.poison)
  (hetyp : res.qualType.etyp = res3.qualType.etyp) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwfTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  have hb₀_false : b₀ = false := by
    have howner₀ := matchGuard_ok_runtime_owner ctxᵢ μ₀ ρ₀ θ₀ e1 k deps hmatch hric₀
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps false b₀ cfg₀1
        howner₀
        hmatch hregime_false ht₀_e1
  have hb₁_false : b₁ = false := by
    have howner₁ := matchGuard_ok_runtime_owner ctxᵢ μ₁ ρ₁ θ₁ e1 k deps hmatch hric₁
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps false b₁ cfg₁1
        howner₁
        hmatch hregime_false ht₁_e1
  have ht₀_e3 : terminatesTo .ioFree e3 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₀_false]
        contradiction
    | inr h => exact h.2
  have ht₁_e3 : terminatesTo .ioFree e3 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₁_false]
        contradiction
    | inr h => exact h.2
  let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩ }
  have htc3' : typecheck .ioFree ctxFalse e3 fuel' = .ok res3 := by
    simpa [typecheck, Nat.succ_sub_one] using htc3
  have hwfTm_false : wfTagMeaningCtx tm ctxFalse := by
    simpa [wfTagMeaningCtx, ctxFalse] using hwfTm
  have hIH_e3 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e3 ctxFalse hwfTm_false res3 htc3'
  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred := by
    have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
      native_decide
    unfold typecheckIf at htcIf
    erw [hmatch] at htcIf
    simp [hregime_false, heq, bind, Except.bind] at htcIf
    rw [htc1] at htcIf
    simp at htcIf
    cases hq1 : res1.qualType with
    | mk etyp1 p1 pred1 =>
        simp [hq1] at htcIf
        have hbool1 : etyp1 = ETyp.bool := by
          simpa [hq1] using hbool
        rw [hbool1] at htcIf
        simp [htc3, pure, Except.pure] at htcIf
        cases hq3 : res3.qualType with
        | mk etyp3 p3 pred3 =>
            simp [hq3] at htcIf
            cases htcIf
            rfl
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_false : wfTypeContext ctxFalse := by
    simpa [wfTypeContext, ctxFalse] using hwf
  have hric₀1' : runtimeInstantiatesCtx ctxFalse cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hsub₀ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    have hric₀1_true :
        runtimeInstantiatesCtx
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          cfg₀1.memory cfg₀1.varEnv θ₀1 := by
      exact
        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
          (ctx := ctxᵢ) (res := res1) (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
          (k := k) (deps := deps)
          hsub₀ hric₀1
    simpa [runtimeInstantiatesCtx, ctxFalse] using hric₀1_true
  have hric₁1' : runtimeInstantiatesCtx ctxFalse cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hsub₁ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    have hric₁1_true :
        runtimeInstantiatesCtx
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      exact
        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
          (ctx := ctxᵢ) (res := res1) (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
          (k := k) (deps := deps)
          hsub₁ hric₁1
    simpa [runtimeInstantiatesCtx, ctxFalse] using hric₁1_true
  have htagR_false : regimeConsistentWithCtx ctxFalse := by
    unfold regimeConsistentWithCtx at htagR ⊢
    constructor
    · exact tagEnvConsistentWithRegime_insert_false
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR.1
    · simpa [ctxFalse] using htagR.2
  have hRbound_false : regimeBounded ctxFalse.regime := by
    simpa [ctxFalse] using hRbound
  have hcwr₀1' : consistentWithRegime predSat ctxFalse.regime ctxFalse cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hcwr₀1_true :
        consistentWithRegime predSat
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
          cfg₀1.memory cfg₀1.varEnv θ₀1 := by
      refine
        consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
          (predSat := predSat) (ctx := ctxᵢ) (res := res1)
          (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
          (kTrue := k) (depsTrue := deps)
          ?hreg_bridge ?hmem_bridge hcwr₀1
      · intro k' b hk
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_regime_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 k' b hk
      · intro l qt k' hlookup hguard hRdef
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 l qt k' hlookup hguard hRdef
    simpa [consistentWithRegime, ctxFalse] using hcwr₀1_true
  have hcwr₁1' : consistentWithRegime predSat ctxFalse.regime ctxFalse cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hcwr₁1_true :
        consistentWithRegime predSat
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
          cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      refine
        consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
          (predSat := predSat) (ctx := ctxᵢ) (res := res1)
          (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
          (kTrue := k) (depsTrue := deps)
          ?hreg_bridge1 ?hmem_bridge1 hcwr₁1
      · intro k' b hk
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_regime_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 k' b hk
      · intro l qt k' hlookup hguard hRdef
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 l qt k' hlookup hguard hRdef
    simpa [consistentWithRegime, ctxFalse] using hcwr₁1_true
  have hagree1' :
      agreeOnClean predSat ctxFalse.regime ctxFalse
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    have hcleanBack :
        ∀ qt, qtypCleanUnder ctxFalse.regime qt → qtypCleanUnder res1.regime' qt := by
      intro qt hclean
      exact
        qtypCleanUnder_transport_pure_regime_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 qt (by simpa [ctxFalse] using hclean)
    have hlookupBackAll :
        ∀ k' b, ctxFalse.regime.lookup? k' = some b → res1.regime'.lookup? k' = some b := by
      intro k' b hk
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxFalse] using hk)
    have hmemberVars₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₀1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberCvcr₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberCvcrEvidence predSat ctxFalse.regime cfg₀1.memory θ₀1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberVars₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₁1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    have hmemberCvcr₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberCvcrEvidence predSat ctxFalse.regime cfg₁1.memory θ₁1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    constructor
    · intro l qt hlookup hclean
      have hlookupRes :
          res1.memEnv'.lookup l = some qt :=
        typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt (by simpa [ctxFalse] using hlookup)
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeLocUnder predSat res1.regime'
            cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt) :=
        hagree1.1 l qt (by simpa [ctxAfter] using hlookupRes) hcleanRes
      cases hagreeRes with
      | both_unrealized l qt hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxFalse.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxFalse.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV'
    · intro x qt hlookup hclean
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeVarUnder predSat res1.regime'
            cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
        hagree1.2 x qt (by simpa [ctxAfter, ctxFalse] using hlookup) hcleanRes
      cases hagreeRes with
      | both_none x qt hnone₀ hnone₁ =>
          exact agreeVarUnder.both_none x qt hnone₀ hnone₁
      | agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxFalse.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxFalse.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV'
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq :
      cfg₁1 =
        { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
          pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e3' : terminatesTo .ioFree e3
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e3
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e3 :=
    hIH_e3 hpredlaws hwfTm_false
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_false hric₀1' hric₁1' htagR_false hRbound_false
      hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e3 ht₁_e3'
  rcases hstep_e3 with ⟨hresTm3, hstep_e3⟩
  rcases hstep_e3 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀3, _hvtyp₁3, _hTm3, hwf3, hwfcf₀3, hwfcf₁3,
      hric₀3, hric₁3, htagR3, hcwr₀3, hcwr₁3, hagree3, _hvalc₀3, _hvalc₁3, hres_agree3⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxFalse res3 := by
    simp [ctxAfter, ctxFalse, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀3
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁3
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR3
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀3
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁3
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree3
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm res3.qualType res.qualType hresTm3 hetyp hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀3, hwfcf₁3,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · simpa [hetyp] using _hvtyp₀3
  · simpa [hetyp] using _hvtyp₁3
  · simpa [hctxAfter] using _hTm3
  · simpa [hctxAfter] using hwf3
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse res3).regime res3.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₀.memory θ₀2 o₀ := by
        simpa [hctxAfter] using hcap₃
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₃'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse res3).regime res3.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₁.memory θ₁2 o₁ := by
        simpa [hctxAfter] using hcap₃
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₃'
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res3.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res3.qualType.poison = false := by
        calc
          joinPoison ctxᵢ.pc res3.qualType.poison = res.qualType.poison := by
            symm
            exact hpoison
          _ = false := hpoison_res
      exact (joinPoison_eq_false hjoin).2
    have hclean3 : qtypCleanUnder (ctxAfter ctxᵢ res).regime res3.qualType := by
      cases hclean with
      | clean hpoison_res =>
          exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k' htag _hreg _hnotfun =>
          exfalso
          simp [qtypGuardTag, hpredNo] at htag
    have hres_agree3' :
        resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res3.qualType o₀ o₁ := by
      simpa [hctxAfter] using hres_agree3
    have hagree3' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res3.qualType o₀ o₁ :=
      hres_agree3' hclean3
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree3'

-- Mode 3: R(k) = none (conservative join)
private lemma stepFR_ite_mode3
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_none : ctxᵢ.regime.lookup? k = none)
  (res1 res2 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : let branchPc := joinPoison ctxᵢ.pc res1.qualType.poison
          let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
          typecheckExpr .ioFree ctxTrue e2 fuel' = .ok res2)
  (htc3 : let branchPc := joinPoison ctxᵢ.pc res1.qualType.poison
          let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
          let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
          typecheckExpr .ioFree ctxFalse' e3 fuel' = .ok res3)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv')
  (htagEnv : res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' res3.nextLoc')
  (hnextTag : res.nextTag' = max res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = joinRegimes res2.regime' res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison
                          (joinPoison res2.qualType.poison res3.qualType.poison))) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert ite evaluation (world-free)
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  -- Apply IH to e1
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢; exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwf1, hwfcf₀1, hwfcf₁1, _hric₀1, _hric₁1, _htagR1, _hcwr₀1, _hcwr₁1, _hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  -- In mode 3, we don't know which branch each run takes - need to handle all cases
  -- The key is that the joined result is conservative over both branches
  sorry -- Mode 3: complex proof with branch case analysis

-- Mode 4: matchGuard fails (standard join)
private lemma stepFR_ite_mode4
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (err : String) (hmatch_fail : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .error err)
  (res1 res2 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree ctxᵢ e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           typecheckExpr .ioFree ctx'' e2 fuel' = .ok res2))
  (htc3 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           typecheckExpr .ioFree ctxForE3 e3 fuel' = .ok res3))
  (hmemEnv : res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv')
  (htagEnv : res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' res3.nextLoc')
  (hnextTag : res.nextTag' = max res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = joinRegimes res2.regime' res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison
                          (joinPoison res2.qualType.poison res3.qualType.poison))) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert ite evaluation (world-free)
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  -- Apply IH to e1 (without pureCtx in this mode)
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, hvalc₀1, hvalc₁1, hres_agree1⟩
  -- Similar to mode 3, need to handle all branch combinations
  sorry -- Mode 4: complex proof with branch case analysis

-- Main lemma that dispatches to mode-specific lemmas
private lemma stepFR_ite
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  -- Parse typecheck result
  have htc' : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htc'
  -- Case split on typecheck structure (4 modes)
  cases hstruct with
  | inl h_mode1 =>
    -- Mode 1: R(k) = some true (then-branch effective)
    obtain ⟨k, deps, hmatch, hregime_true, res1, htc1, hbool, res2, htc2,
            hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp⟩ := h_mode1
    exact stepFR_ite_mode1 ctxᵢ predSat tm e1 e2 e3 fuel' res IH htc k deps hmatch hregime_true
      res1 res2 htc1 hbool htc2 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison hetyp
  | inr h_rest =>
    cases h_rest with
    | inl h_mode2 =>
      -- Mode 2: R(k) = some false (else-branch effective)
      obtain ⟨k, deps, hmatch, hregime_false, res1, htc1, hbool, res3, htc3,
              hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp⟩ := h_mode2
      exact stepFR_ite_mode2 ctxᵢ predSat tm e1 e2 e3 fuel' res IH htc k deps hmatch hregime_false
        res1 res3 htc1 hbool htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison hetyp
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_mode3 =>
        -- Mode 3: R(k) = none (conservative join)
        obtain ⟨k, deps, hmatch, hregime_none, res1, htc1, hbool, res2, htc2, res3, htc3,
                hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, _hetyp, _hpred⟩ := h_mode3
        exact stepFR_ite_mode3 ctxᵢ predSat tm e1 e2 e3 fuel' res IH k deps hmatch hregime_none
          res1 res2 res3 htc1 hbool htc2 htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison
      | inr h_mode4 =>
        -- Mode 4: matchGuard fails (standard join)
        obtain ⟨⟨err, hmatch_fail⟩, res1, htc1, hbool, res2, htc2, res3, htc3,
                hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, _hetyp, _hpred⟩ := h_mode4
        exact stepFR_ite_mode4 ctxᵢ predSat tm e1 e2 e3 fuel' res IH err hmatch_fail
          res1 res2 res3 htc1 hbool htc2 htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison


private lemma stepFR_deref
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.deref e) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.deref e) res predSat tm := by
  classical
  -- Parse typecheck result
  have htc' : typecheckDeref .ioFree ctxᵢ e (Nat.succ fuel') = .ok res := by
    simp [typecheck, typecheckExpr] at htc
    exact htc
  obtain ⟨res1, htc1, h_mem, h_tag, h_loc, h_ntag, h_regime⟩ :=
    typecheckDeref_structure ctxᵢ e (Nat.succ fuel') res htc'
  have htc1_expr : typecheckExpr .ioFree ctxᵢ e fuel' = .ok res1 := by
    simpa [Nat.succ_sub_one] using htc1
  have htc1' : typecheck .ioFree ctxᵢ e fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hIH := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e ctxᵢ hwfTm res1 htc1'
  -- Invert deref evaluation (world-free)
  have hstruct₀ := terminatesTo_deref_inv' e
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀', a₀', n₀, ht₀_e, hlookup₀, hv₀, hmem₀, hvar₀, hnext₀, hpm₀, hpm_e₀⟩
  have hstruct₁ := terminatesTo_deref_inv' e
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁', a₁', n₁, ht₁_e, hlookup₁, hv₁, hmem₁, hvar₁, hnext₁, hpm₁, hpm_e₁⟩
  -- Apply IH for sub-expression
  have hstep_e :=
    hIH hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀' cfg₁' (Value.loc a₀') (Value.loc a₁')
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e ht₁_e
  rcases hstep_e with ⟨hresTm_e, hstep_e⟩
  rcases hstep_e with ⟨θ₀', θ₁', hθext₀, hθext₁, _hvtyp₀, _hvtyp₁, _hTm', hwf', hwfcfg₀', hwfcfg₁', hric₀', hric₁', hreg', hcwr₀', hcwr₁', hagree_clean_e, _hval_consist₀, _hval_consist₁, hres_agree_e⟩
  -- Post-context is unchanged by deref (only result type changes)
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxᵢ res1 := by
    cases ctxᵢ
    simp [ctxAfter, h_mem, h_tag, h_loc, h_ntag, h_regime]
  -- IH gives agreeOnClean with (ctxAfter ctxᵢ res1).regime; transfer via hctxAfter
  have hagree_clean :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀' cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₀, hvar₀, hmem₁, hvar₁] using hagree_clean_e
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hric₀'
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hric₁'
  -- IH gives regimeConsistentWithCtx with output regime; transfer via hctxAfter
  have hreg_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using hreg'
  -- Derive wfConfig for final configs using wfConfig_preserved
  have hwfcf₀_final : wfConfig cf₀ := (wfConfig_preserved .ioFree (Expr.deref e) _ cf₀ o₀ ht₀ hwfcfg₀).1
  have hwfcf₁_final : wfConfig cf₁ := (wfConfig_preserved .ioFree (Expr.deref e) _ cf₁ o₁ ht₁ hwfcfg₁).1
  have hcwr₀_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀' := by
    simpa [hctxAfter, hmem₀, hvar₀] using hcwr₀'
  have hcwr₁_final : consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁' := by
    simpa [hctxAfter, hmem₁, hvar₁] using hcwr₁'
  have hresTm : QTypRespectsTagMeaning tm res.qualType :=
    typecheckDeref_qtypRespects tm ctxᵢ e fuel' res res1 _hTm' htc1_expr htc'
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀', θ₁', hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀_final, hwfcf₁_final, hric₀_final, hric₁_final, hreg_final, hcwr₀_final, hcwr₁_final, hagree_clean, ?_, ?_, ?_⟩
  · subst hv₀
    have hres_etyp_int : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    rw [hres_etyp_int]
    exact valueHasETyp.num n₀
  · subst hv₁
    have hres_etyp_int : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    rw [hres_etyp_int]
    exact valueHasETyp.num n₁
  · simpa [hctxAfter] using _hTm'
  · simpa [hctxAfter] using hwf'
  · -- valueConsistentWithRegime for cf₀
    subst hv₀
    have hlookup_cf₀ : cf₀.memory.lookup a₀' = some n₀ := by
      simpa [hmem₀] using hlookup₀
    have hderef_etyp_int : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    have _hnclos₀ : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime
        res.qualType cf₀.memory θ₀' (Value.num n₀) :=
      closureCapturedVarsRegime_nonClosure_of_nonFunctionType (θ := θ₀')
        (by rw [hderef_etyp_int]; exact valueHasETyp.num n₀)
        (by simp [hderef_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    cases hpred_res : res.qualType.pred with
    | noPred =>
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred_res]) _hnclos₀
    | guardOnly k =>
        exact valueConsistentWithRegime.guardOnly_ok k (by simp [hpred_res]) _hnclos₀
    | guardClosure k arg_name pred_body var_env =>
        have htag_res : qtypGuardTag res.qualType = some k := by
          simp [qtypGuardTag, hpred_res]
        cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
        | none =>
            exact valueConsistentWithRegime.notInRegime k htag_res hk _hnclos₀
        | some b =>
            -- `res1` must be an unpoisoned `ref int ls0` if `res` preserves a guardClosure predicate.
            have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
              have htc'' := htc'
              simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
              cases hq : res1.qualType with
              | mk etyp poison pred =>
                  cases etyp with
                  | ref ls => simp [hq] at htc''; exact ⟨ls, rfl⟩
                  | _ => simp [hq] at htc''
            rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
            have hres1_poison_false : res1.qualType.poison = false := by
              cases hq : res1.qualType with
              | mk etyp poison pred =>
                  cases hpoison : poison with
                  | false =>
                      simp
                  | true =>
                      have : False := by
                        have h_etyp : etyp = ETyp.ref ls0 := by
                          simpa [hq] using hres1_etyp0
                        have htc_bad := htc'
                        simp [typecheckDeref, htc1_expr, hq, h_etyp, hpoison, bind, Except.bind] at htc_bad
                        by_cases hls : ls0 = ∅
                        · simp [hls] at htc_bad
                        · simp [hls] at htc_bad
                          cases hfold :
                              ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                                match res1.memEnv'.lookup l with
                                | some qt =>
                                    pure
                                      (joinPoison x.1 qt.poison,
                                        match x.2 with
                                        | none => some qt.pred
                                        | some p => some (joinPredicates p qt.pred))
                                | none =>
                                    throw
                                      (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                          | error err =>
                              erw [hfold] at htc_bad
                              cases htc_bad
                          | ok v =>
                              erw [hfold] at htc_bad
                              simp [pure, Except.pure] at htc_bad
                              cases htc_bad
                              cases hpred_res
                      exact False.elim this
            have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
              qtypCleanUnder.clean hres1_poison_false
            have hagree_ref :
                agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁'
                  res1.qualType (Value.loc a₀') (Value.loc a₁') :=
              hres_agree_e hres1_clean
            have ⟨l, hθ₀l, hθ₁l, hlin⟩ :
                ∃ l, θ₀'.lookup l = some a₀' ∧ θ₁'.lookup l = some a₁' ∧ l ∈ ls0 := by
              cases hagree_ref with
              | @clean_ref ls l0 a1 a2 qt v1 v2 _hpoison0 hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                  have : ETyp.ref ls = ETyp.ref ls0 := by
                    calc
                      ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
                      _ = ETyp.ref ls0 := hres1_etyp0
                  injection this with hls
                  subst hls
                  cases hv1
                  cases hv2
                  exact ⟨l0, hlookup1, hlookup2, hin⟩
              | @withPred_true_ref k2 ls l0 a1 a2 qt v1 v2 _htag _hreg hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                  have : ETyp.ref ls = ETyp.ref ls0 := by
                    calc
                      ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
                      _ = ETyp.ref ls0 := hres1_etyp0
                  injection this with hls
                  subst hls
                  cases hv1
                  cases hv2
                  exact ⟨l0, hlookup1, hlookup2, hin⟩
              | clean_eq_nonref_nonarrow _ _ hnotref _ =>
                  exfalso
                  exact hnotref ⟨ls0, hres1_etyp0⟩
              | withPred_true_eq _ _ _ _ hnotref _ =>
                  exfalso
                  exact hnotref ⟨ls0, hres1_etyp0⟩
              | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
                  exfalso
                  have h := hetyp
                  rw [hres1_etyp0] at h
                  cases h
              | dirty_internal_arrow _ hisArrow _ _ =>
                  exfalso
                  have : res1.qualType.etyp.isArrow = false := by
                    simp [hres1_etyp0, ETyp.isArrow]
                  simp [this] at hisArrow
              | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
                  exfalso
                  have h := hetyp
                  rw [hres1_etyp0] at h
                  cases h
              | dirty_internal_parrow _ hisParrow _ _ =>
                  exfalso
                  have : res1.qualType.etyp.isParrow = false := by
                    simp [hres1_etyp0, ETyp.isParrow]
                  simp [this] at hisParrow

            -- Recover the fold result and the merged predicate from the typechecker.
            have htc'' := htc'
            cases hq : res1.qualType with
            | mk etyp poison pred =>
                have h_etyp : etyp = ETyp.ref ls0 := by
                  simpa [hq] using hres1_etyp0
                have h_poison : poison = false := by
                  simpa [hq] using hres1_poison_false
                simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
                by_cases hls : ls0 = ∅
                · simp [hls] at htc''
                · simp [hls] at htc''
                  cases hfold :
                      ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                        match res1.memEnv'.lookup l with
                        | some qt =>
                            pure (joinPoison x.1 qt.poison,
                              match x.2 with
                              | none => some qt.pred
                              | some p => some (joinPredicates p qt.pred))
                        | none =>
                            throw
                              (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                  | error err =>
                      erw [hfold] at htc''
                      cases htc''
                  | ok v =>
                      erw [hfold] at htc''
                      have hfold' :
                          LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                            Except.ok v := by
                        simpa [LocSet.foldM, derefFoldF] using hfold
                      cases hmerged : v.2.getD Predicate.noPred with
                      | noPred =>
                          simp [hmerged, pure, Except.pure] at htc''
                          cases htc''
                          cases hpred_res
                      | guardOnly k' =>
                          cases htagEnv' : res1.tagEnv'[k']? with
                          | some tv =>
                              cases tv with
                              | mk val deps =>
                                  cases val with
                                  | true =>
                                      simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                      cases htc''; cases hpred_res
                                  | false =>
                                      simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                      cases htc''; cases hpred_res
                          | none =>
                              simp [hmerged, htagEnv', pure, Except.pure] at htc''
                              cases htc''; cases hpred_res
                      | guardClosure k' arg_name' pred_body' var_env' =>
                          cases htagEnv : res1.tagEnv'[k']? with
                          | some tv =>
                              cases tv with
                              | mk val deps =>
                                  cases val with
                                  | true =>
                                      simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                      cases htc''
                                      cases hpred_res
                                  | false =>
                                      simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                      cases htc''
                                      cases hpred_res
                          | none =>
                              simp [hmerged, htagEnv, pure, Except.pure] at htc''
                              -- Extract the resulting TypeResult equality without eliminating `res`.
                              have hEq :
                                  { qualType :=
                                      { etyp := ETyp.int, poison := joinPoison ctxᵢ.pc v.1,
                                        pred := Predicate.guardClosure k' arg_name' pred_body' var_env' },
                                    memEnv' := res1.memEnv', tagEnv' := res1.tagEnv', nextLoc' := res1.nextLoc',
                                    nextTag' := res1.nextTag', regime' := res1.regime' } = res := by
                                simpa using htc''
                              have hpred_tc : res.qualType.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                                have h := congrArg (fun r => r.qualType.pred) hEq.symm
                                simp at h
                                exact h
                              -- Now `hpred_res` forces the merged predicate to match the output predicate.
                              have hpred_fold :
                                  v.2.getD Predicate.noPred =
                                    Predicate.guardClosure k arg_name pred_body var_env := by
                                calc
                                  v.2.getD Predicate.noPred =
                                      Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                                    simp [hmerged]
                                  _ = res.qualType.pred := by
                                    symm; exact hpred_tc
                                  _ = Predicate.guardClosure k arg_name pred_body var_env := by
                                    exact hpred_res
                              have ⟨qt_mem, hlookup_mem, hqt_pred⟩ :=
                                deref_foldM_pred_eq_guardClosure res1.memEnv' ls0 v.1 v.2 hfold' hpred_fold l hlin
                              have hlookup_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_mem := by
                                simpa [ctxAfter, h_mem] using hlookup_mem
                              have htag_mem : qtypGuardTag qt_mem = some k := by
                                simp [qtypGuardTag, hqt_pred]
                              have hk_ne : (ctxAfter ctxᵢ res).regime.lookup? k ≠ none := by
                                simp [hk]
                              have hlocs :=
                                hcwr₀_final.1 l qt_mem k hlookup_ctx htag_mem hk_ne
                              -- Invert locsRegime to get the predicate truth at runtime.
                              cases hlocs with
                              | noPred_ok hnone =>
                                  -- Impossible: we have a guardClosure predicate, hence a guard tag.
                                  simp [hnone] at htag_mem
                              | guardOnly_ok k' hgo =>
                                  -- Impossible: `qt_mem.pred` is a guardClosure.
                                  simp [hqt_pred] at hgo
                              | withPred_ok k0 arg_name0 pred_body0 var_env0 a n b0 hclos hregime hreal hmem hconsist =>
                                  have hreal' : θ₀'.lookup l = some a := by
                                    simpa using hreal
                                  have ha : a = a₀' := by
                                    have : some a = some a₀' := by
                                      calc
                                        some a = θ₀'.lookup l := by symm; exact hreal'
                                        _ = some a₀' := hθ₀l
                                    exact Option.some.inj this
                                  have hn : n = n₀ := by
                                    have : some n = some n₀ := by
                                      calc
                                        some n = cf₀.memory.lookup a := by symm; exact hmem
                                        _ = cf₀.memory.lookup a₀' := by simp [ha]
                                        _ = some n₀ := hlookup_cf₀
                                    exact Option.some.inj this
                                  have hk0 : k0 = k := by
                                    have htag0 : qtypGuardTag qt_mem = some k0 := by
                                      have hclos' :
                                          qt_mem.pred =
                                            Predicate.guardClosure k0 arg_name0 pred_body0 var_env0 := by
                                        simpa using hclos
                                      simp [qtypGuardTag, hclos']
                                    have : some k0 = some k := by
                                      calc
                                        some k0 = qtypGuardTag qt_mem := by symm; exact htag0
                                        _ = some k := htag_mem
                                    exact Option.some.inj this
                                  have hregime_k : (ctxAfter ctxᵢ res).regime.lookup? k = some b0 := by
                                    simpa [hk0] using hregime
                                  cases hb : b0 with
                                  | true =>
                                      have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                                        simpa [hb] using hregime_k
                                      have hholds_cell : qtypPredHolds predSat qt_mem cf₀.memory (Value.num n₀) := by
                                        simpa [hn] using hconsist.1 hb
                                      have hpredEq : qt_mem.pred = res.qualType.pred := by
                                        simp [hqt_pred, hpred_res]
                                      have hholds_res :
                                          qtypPredHolds predSat res.qualType cf₀.memory (Value.num n₀) :=
                                        qtypPredHolds_transport_pred (predSat := predSat)
                                          (qt := qt_mem) (qt' := res.qualType) (μ := cf₀.memory) (v := Value.num n₀)
                                          hpredEq hholds_cell
                                      exact valueConsistentWithRegime.inRegimeTrue k
                                        htag_res hktrue hholds_res _hnclos₀
                                  | false =>
                                      have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                                        simpa [hb] using hregime_k
                                      have hnot_cell : ¬ qtypPredHolds predSat qt_mem cf₀.memory (Value.num n₀) := by
                                        simpa [hn] using hconsist.2 hb
                                      have hpredEq : qt_mem.pred = res.qualType.pred := by
                                        simp [hqt_pred, hpred_res]
                                      have hnot_res :
                                          ¬ qtypPredHolds predSat res.qualType cf₀.memory (Value.num n₀) :=
                                        qtypPredHolds_transport_pred_not (predSat := predSat)
                                          (qt := qt_mem) (qt' := res.qualType) (μ := cf₀.memory) (v := Value.num n₀)
                                          hpredEq hnot_cell
                                      exact valueConsistentWithRegime.inRegimeFalse k
                                        htag_res hkfalse hnot_res _hnclos₀
  · -- valueConsistentWithRegime for cf₁
    subst hv₁
    have hlookup_cf₁ : cf₁.memory.lookup a₁' = some n₁ := by
      simpa [hmem₁] using hlookup₁
    have hderef_etyp_int₁ : res.qualType.etyp = ETyp.int :=
      typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
    have _hnclos₁ : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime
        res.qualType cf₁.memory θ₁' (Value.num n₁) :=
      closureCapturedVarsRegime_nonClosure_of_nonFunctionType (θ := θ₁')
        (by rw [hderef_etyp_int₁]; exact valueHasETyp.num n₁)
        (by simp [hderef_etyp_int₁, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    cases hpred_res : res.qualType.pred with
    | noPred =>
        exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred_res]) _hnclos₁
    | guardOnly k =>
        exact valueConsistentWithRegime.guardOnly_ok k (by simp [hpred_res]) _hnclos₁
    | guardClosure k arg_name pred_body var_env =>
        have htag_res : qtypGuardTag res.qualType = some k := by
          simp [qtypGuardTag, hpred_res]
        cases hk : (ctxAfter ctxᵢ res).regime.lookup? k with
        | none =>
            exact valueConsistentWithRegime.notInRegime k htag_res hk _hnclos₁
        | some b =>
            have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
              have htc'' := htc'
              simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
              cases hq : res1.qualType with
              | mk etyp poison pred =>
                  cases etyp with
                  | ref ls => simp [hq] at htc''; exact ⟨ls, rfl⟩
                  | _ => simp [hq] at htc''
            rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
            have hres1_poison_false : res1.qualType.poison = false := by
              cases hq : res1.qualType with
              | mk etyp poison pred =>
                  cases hpoison : poison with
                  | false =>
                      simp
                  | true =>
                      have : False := by
                        have h_etyp : etyp = ETyp.ref ls0 := by
                          simpa [hq] using hres1_etyp0
                        have htc_bad := htc'
                        simp [typecheckDeref, htc1_expr, hq, h_etyp, hpoison, bind, Except.bind] at htc_bad
                        by_cases hls : ls0 = ∅
                        · simp [hls] at htc_bad
                        · simp [hls] at htc_bad
                          cases hfold :
                              ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                                match res1.memEnv'.lookup l with
                                | some qt =>
                                    pure
                                      (joinPoison x.1 qt.poison,
                                        match x.2 with
                                        | none => some qt.pred
                                        | some p => some (joinPredicates p qt.pred))
                                | none =>
                                    throw
                                      (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                          | error err =>
                              erw [hfold] at htc_bad
                              cases htc_bad
                          | ok v =>
                              erw [hfold] at htc_bad
                              simp [pure, Except.pure] at htc_bad
                              cases htc_bad
                              cases hpred_res
                      exact False.elim this
            have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
              qtypCleanUnder.clean hres1_poison_false
            have hagree_ref :
                agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁'
                  res1.qualType (Value.loc a₀') (Value.loc a₁') :=
              hres_agree_e hres1_clean
            have ⟨l, hθ₀l, hθ₁l, hlin⟩ :
                ∃ l, θ₀'.lookup l = some a₀' ∧ θ₁'.lookup l = some a₁' ∧ l ∈ ls0 := by
              cases hagree_ref with
              | @clean_ref ls l0 a1 a2 qt v1 v2 _hpoison0 hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                  have : ETyp.ref ls = ETyp.ref ls0 := by
                    calc
                      ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
                      _ = ETyp.ref ls0 := hres1_etyp0
                  injection this with hls
                  subst hls
                  cases hv1
                  cases hv2
                  exact ⟨l0, hlookup1, hlookup2, hin⟩
              | @withPred_true_ref k2 ls l0 a1 a2 qt v1 v2 _htag _hreg hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                  have : ETyp.ref ls = ETyp.ref ls0 := by
                    calc
                      ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
                      _ = ETyp.ref ls0 := hres1_etyp0
                  injection this with hls
                  subst hls
                  cases hv1
                  cases hv2
                  exact ⟨l0, hlookup1, hlookup2, hin⟩
              | clean_eq_nonref_nonarrow _ _ hnotref _ =>
                  exfalso
                  exact hnotref ⟨ls0, hres1_etyp0⟩
              | withPred_true_eq _ _ _ _ hnotref _ =>
                  exfalso
                  exact hnotref ⟨ls0, hres1_etyp0⟩
              | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
                  exfalso
                  have h := hetyp
                  rw [hres1_etyp0] at h
                  cases h
              | dirty_internal_arrow _ hisArrow _ _ =>
                  exfalso
                  have : res1.qualType.etyp.isArrow = false := by
                    simp [hres1_etyp0, ETyp.isArrow]
                  simp [this] at hisArrow
              | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
                  exfalso
                  have h := hetyp
                  rw [hres1_etyp0] at h
                  cases h
              | dirty_internal_parrow _ hisParrow _ _ =>
                  exfalso
                  have : res1.qualType.etyp.isParrow = false := by
                    simp [hres1_etyp0, ETyp.isParrow]
                  simp [this] at hisParrow

            have htc'' := htc'
            cases hq : res1.qualType with
            | mk etyp poison pred =>
                have h_etyp : etyp = ETyp.ref ls0 := by
                  simpa [hq] using hres1_etyp0
                have h_poison : poison = false := by
                  simpa [hq] using hres1_poison_false
                simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
                by_cases hls : ls0 = ∅
                · simp [hls] at htc''
                · simp [hls] at htc''
                  cases hfold :
                      ls0.foldM (m := Except String) (false, (none : Option Predicate)) (fun x l =>
                        match res1.memEnv'.lookup l with
                        | some qt =>
                            pure (joinPoison x.1 qt.poison,
                              match x.2 with
                              | none => some qt.pred
                              | some p => some (joinPredicates p qt.pred))
                        | none =>
                            throw
                              (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
                  | error err =>
                      erw [hfold] at htc''
                      cases htc''
                  | ok v =>
                      erw [hfold] at htc''
                      have hfold' :
                          LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                            Except.ok v := by
                        simpa [LocSet.foldM, derefFoldF] using hfold
                      cases hmerged : v.2.getD Predicate.noPred with
                      | noPred =>
                          simp [hmerged, pure, Except.pure] at htc''
                          cases htc''
                          cases hpred_res
                      | guardOnly k' =>
                          cases htagEnv' : res1.tagEnv'[k']? with
                          | some tv =>
                              cases tv with
                              | mk val deps =>
                                  cases val with
                                  | true =>
                                      simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                      cases htc''; cases hpred_res
                                  | false =>
                                      simp [hmerged, htagEnv', pure, Except.pure] at htc''
                                      cases htc''; cases hpred_res
                          | none =>
                              simp [hmerged, htagEnv', pure, Except.pure] at htc''
                              cases htc''; cases hpred_res
                      | guardClosure k' arg_name' pred_body' var_env' =>
                          cases htagEnv : res1.tagEnv'[k']? with
                          | some tv =>
                              cases tv with
                              | mk val deps =>
                                  cases val with
                                  | true =>
                                      simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                      cases htc''
                                      cases hpred_res
                                  | false =>
                                      simp [hmerged, htagEnv, pure, Except.pure] at htc''
                                      cases htc''
                                      cases hpred_res
                          | none =>
                              simp [hmerged, htagEnv, pure, Except.pure] at htc''
                              have hEq :
                                  { qualType :=
                                      { etyp := ETyp.int, poison := joinPoison ctxᵢ.pc v.1,
                                        pred := Predicate.guardClosure k' arg_name' pred_body' var_env' },
                                    memEnv' := res1.memEnv', tagEnv' := res1.tagEnv', nextLoc' := res1.nextLoc',
                                    nextTag' := res1.nextTag', regime' := res1.regime' } = res := by
                                simpa using htc''
                              have hpred_tc : res.qualType.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                                have h := congrArg (fun r => r.qualType.pred) hEq.symm
                                simp at h
                                exact h
                              have hpred_fold :
                                  v.2.getD Predicate.noPred =
                                    Predicate.guardClosure k arg_name pred_body var_env := by
                                calc
                                  v.2.getD Predicate.noPred =
                                      Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                                    simp [hmerged]
                                  _ = res.qualType.pred := by
                                    symm; exact hpred_tc
                                  _ = Predicate.guardClosure k arg_name pred_body var_env := by
                                    exact hpred_res
                              have ⟨qt_mem, hlookup_mem, hqt_pred⟩ :=
                                deref_foldM_pred_eq_guardClosure res1.memEnv' ls0 v.1 v.2 hfold' hpred_fold l hlin
                              have hlookup_ctx : (ctxAfter ctxᵢ res).memEnv.lookup l = some qt_mem := by
                                simpa [ctxAfter, h_mem] using hlookup_mem
                              have htag_mem : qtypGuardTag qt_mem = some k := by
                                simp [qtypGuardTag, hqt_pred]
                              have hk_ne : (ctxAfter ctxᵢ res).regime.lookup? k ≠ none := by
                                simp [hk]
                              have hlocs :=
                                hcwr₁_final.1 l qt_mem k hlookup_ctx htag_mem hk_ne
                              cases hlocs with
                              | noPred_ok hnone =>
                                  simp [hnone] at htag_mem
                              | guardOnly_ok k' hgo =>
                                  simp [hqt_pred] at hgo
                              | withPred_ok k0 arg_name0 pred_body0 var_env0 a n b0 hclos hregime hreal hmem hconsist =>
                                  have hreal' : θ₁'.lookup l = some a := by
                                    simpa using hreal
                                  have ha : a = a₁' := by
                                    have : some a = some a₁' := by
                                      calc
                                        some a = θ₁'.lookup l := by symm; exact hreal'
                                        _ = some a₁' := hθ₁l
                                    exact Option.some.inj this
                                  have hn : n = n₁ := by
                                    have : some n = some n₁ := by
                                      calc
                                        some n = cf₁.memory.lookup a := by symm; exact hmem
                                        _ = cf₁.memory.lookup a₁' := by simp [ha]
                                        _ = some n₁ := hlookup_cf₁
                                    exact Option.some.inj this
                                  have hk0 : k0 = k := by
                                    have htag0 : qtypGuardTag qt_mem = some k0 := by
                                      have hclos' :
                                          qt_mem.pred =
                                            Predicate.guardClosure k0 arg_name0 pred_body0 var_env0 := by
                                        simpa using hclos
                                      simp [qtypGuardTag, hclos']
                                    have : some k0 = some k := by
                                      calc
                                        some k0 = qtypGuardTag qt_mem := by symm; exact htag0
                                        _ = some k := htag_mem
                                    exact Option.some.inj this
                                  have hregime_k : (ctxAfter ctxᵢ res).regime.lookup? k = some b0 := by
                                    simpa [hk0] using hregime
                                  cases hb : b0 with
                                  | true =>
                                      have hktrue : (ctxAfter ctxᵢ res).regime.lookup? k = some true := by
                                        simpa [hb] using hregime_k
                                      have hholds_cell : qtypPredHolds predSat qt_mem cf₁.memory (Value.num n₁) := by
                                        simpa [hn] using hconsist.1 hb
                                      have hpredEq : qt_mem.pred = res.qualType.pred := by
                                        simp [hqt_pred, hpred_res]
                                      have hholds_res :
                                          qtypPredHolds predSat res.qualType cf₁.memory (Value.num n₁) :=
                                        qtypPredHolds_transport_pred (predSat := predSat)
                                          (qt := qt_mem) (qt' := res.qualType) (μ := cf₁.memory) (v := Value.num n₁)
                                          hpredEq hholds_cell
                                      exact valueConsistentWithRegime.inRegimeTrue k
                                        htag_res hktrue hholds_res _hnclos₁
                                  | false =>
                                      have hkfalse : (ctxAfter ctxᵢ res).regime.lookup? k = some false := by
                                        simpa [hb] using hregime_k
                                      have hnot_cell : ¬ qtypPredHolds predSat qt_mem cf₁.memory (Value.num n₁) := by
                                        simpa [hn] using hconsist.2 hb
                                      have hpredEq : qt_mem.pred = res.qualType.pred := by
                                        simp [hqt_pred, hpred_res]
                                      have hnot_res :
                                          ¬ qtypPredHolds predSat res.qualType cf₁.memory (Value.num n₁) :=
                                        qtypPredHolds_transport_pred_not (predSat := predSat)
                                          (qt := qt_mem) (qt' := res.qualType) (μ := cf₁.memory) (v := Value.num n₁)
                                          hpredEq hnot_cell
                                      exact valueConsistentWithRegime.inRegimeFalse k
                                        htag_res hkfalse hnot_res _hnclos₁
  -- Result agreement when clean: deref reads from a clean location
  intro hclean
  -- We need to show o₀ = o₁ (both are ints from the same logical location)
  -- First, show the argument type is ref int
  have hres1_etyp : ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
    have htc'' := htc'
    simp [typecheckDeref, htc1_expr, bind, Except.bind] at htc''
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        cases etyp <;> simp [hq] at htc''
        rename_i ls
        exact ⟨ls, rfl⟩
  -- The reference itself must be unpoisoned if the deref result is clean
  have hres1_poison_false : res1.qualType.poison = false := by
    by_contra hbad
    rcases hres1_etyp with ⟨ls, hres1_etyp⟩
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        -- simplify typecheckDeref under poisonRef = true
        have h_etyp : etyp = ETyp.ref ls := by
          simpa [hq] using hres1_etyp
        have hpoison : poison = true := by
          cases poison
          · simp [hq] at hbad
          · rfl
        have htc'' := htc'
        simp [typecheckDeref, htc1_expr, hq, h_etyp, hpoison, bind, Except.bind, pure, Except.pure] at htc''
        by_cases hls : ls = ∅
        · -- Empty locset: typecheck would error, contradict success
          simp [hls] at htc''
        · -- ls ≠ ∅, so the deref branch returns poisoned result with noPred
          simp [hls] at htc''
          -- Case split on the foldM over locations via the outer match in htc''
          split at htc''
          · -- foldM error case
            cases htc''
          · -- foldM ok case
            rename_i v
            cases htc''
            cases hclean with
            | clean hpoison =>
                -- contradiction: clean requires poison = false
                simp at hpoison
            | guard k htag _ _ =>
                -- contradiction: guard tag absent when pred = noPred
                simp [qtypGuardTag] at htag
  -- Use output regime for IH result
  have hres1_clean : qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
    qtypCleanUnder.clean hres1_poison_false
  have hagree_ref :
      agreeValueUnder predSat (ctxAfter ctxᵢ res1).regime cfg₀'.memory cfg₁'.memory θ₀' θ₁' res1.qualType (Value.loc a₀') (Value.loc a₁') :=
    hres_agree_e hres1_clean
  -- Extract the logical location l from reference agreement
  rcases hres1_etyp with ⟨ls0, hres1_etyp0⟩
  have ⟨l, hθ₀l, hθ₁l, hlin⟩ :
      ∃ l, θ₀'.lookup l = some a₀' ∧ θ₁'.lookup l = some a₁' ∧ l ∈ ls0 := by
    cases hagree_ref with
    | @clean_ref ls l a1 a2 qt v1 v2 _hetyp_poison hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have hls_eq : ETyp.ref ls = ETyp.ref ls0 := by
          calc
            ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ls0 := hres1_etyp0
        injection hls_eq with hls; subst hls
        -- Align addresses using hv1/hv2
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | @withPred_true_ref k ls l a1 a2 qt v1 v2 _htag _hreg hetyp hlookup1 hin hv1 hlookup2 hv2 =>
        have hls_eq : ETyp.ref ls = ETyp.ref ls0 := by
          calc
            ETyp.ref ls = res1.qualType.etyp := by symm; exact hetyp
            _ = ETyp.ref ls0 := hres1_etyp0
        injection hls_eq with hls; subst hls
        cases hv1
        cases hv2
        exact ⟨l, by simpa using hlookup1, by simpa using hlookup2, hin⟩
    | clean_eq_nonref_nonarrow _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ls0, hres1_etyp0⟩
    | withPred_true_eq _ _ _ _ hnotref _ =>
        exfalso
        exact hnotref ⟨ls0, hres1_etyp0⟩
    | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | dirty_internal_arrow _ hisArrow _ _ =>
        exfalso
        -- res1.etyp is ref, so cannot be arrow
        have : res1.qualType.etyp.isArrow = false := by
          simp [hres1_etyp0, ETyp.isArrow]
        rw [hisArrow] at this
        cases this
    | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
        exfalso
        have h := hres1_etyp0
        simp [hetyp] at h
    | dirty_internal_parrow _ hisParrow _ _ =>
        exfalso
        have : res1.qualType.etyp.isParrow = false := by
          simp [hres1_etyp0, ETyp.isParrow]
        rw [hisParrow] at this
        cases this
  -- Obtain the memory type for l from the context
  have hlookup_ctx : ∃ qt, (ctxAfter ctxᵢ res1).memEnv.lookup l = some qt := by
    -- Use runtime instantiation to show l is present, then pick its lookup
    have hcontains : (ctxAfter ctxᵢ res1).memEnv.contains l = true := by
      -- from runtimeInstantiatesCtx and θ₀' lookup
      have hctx : (ctxAfter ctxᵢ res1).memEnv.contains l ∧ cfg₀'.memory.contains a₀' :=
        (hric₀'.1 l a₀' hθ₀l)
      exact hctx.1
    have hmem : l ∈ (ctxAfter ctxᵢ res1).memEnv :=
      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
    have hlookup_isSome : ((ctxAfter ctxᵢ res1).memEnv[l]?).isSome = true :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
    cases hlookup_l : (ctxAfter ctxᵢ res1).memEnv[l]? with
    | none =>
        simp [hlookup_l] at hlookup_isSome
    | some e =>
        -- get? returns MemEntry; lookup returns QTyp (etyp = int)
        have hlookup_l' : (ctxAfter ctxᵢ res1).memEnv.lookup l = some ⟨ETyp.int, e.poison, e.pred⟩ := by
          simp only [ctxAfter] at hlookup_l
          simp only [ctxAfter, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hlookup_l, Option.map] 
        exact ⟨⟨ETyp.int, e.poison, e.pred⟩, hlookup_l'⟩
  obtain ⟨qt, hlookup_ctx⟩ := hlookup_ctx
  -- Get agreement on the location from agreeOnClean (need cleanliness under the *post-e* regime).
  have hclean_loc : qtypCleanUnder (ctxAfter ctxᵢ res1).regime qt := by
    -- Analyze typecheckDeref to obtain the fold result, then use hclean.
    cases hq : res1.qualType with
    | mk etyp poison pred =>
        have h_etyp : etyp = ETyp.ref ls0 := by
          simpa [hq] using hres1_etyp0
        have h_poison : poison = false := by
          simpa [hq] using hres1_poison_false
        have htc'' := htc'
        simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, bind, Except.bind] at htc''
        by_cases hls : ls0 = ∅
        · simp [hls] at htc''
        · simp [hls] at htc''
          cases hfold :
              ls0.foldM (m := Except String) (false, none) (fun x l =>
                match res1.memEnv'.lookup l with
                | some qt =>
                    pure
                      (joinPoison x.1 qt.poison,
                        match x.2 with
                        | none => some qt.pred
                        | some p => some (joinPredicates p qt.pred))
                | none =>
                    throw
                      (toString "Location " ++ toString l ++ toString " not found in memory environment")) with
          | error err =>
              have htc_bad : typecheckDeref .ioFree ctxᵢ e (Nat.succ fuel') = Except.error err := by
                simp [typecheckDeref, htc1_expr, hq, h_etyp, h_poison, hls,
                  bind, Except.bind, pure, Except.pure]
                erw [hfold]
              have htc_bad_false : False := by
                simp [htc_bad] at htc'
              cases htc_bad_false
          | ok v_3 =>
              have hfold_plain :
                  ls0.foldM (m := Except String) (false, none) (fun x l =>
                    match res1.memEnv'.lookup l with
                    | some qt =>
                        pure
                          (joinPoison x.1 qt.poison,
                            match x.2 with
                            | none => some qt.pred
                            | some p => some (joinPredicates p qt.pred))
                    | none =>
                        throw
                          (toString "Location " ++ toString l ++ toString " not found in memory environment")) =
                    Except.ok v_3 := by
                simpa using hfold
              erw [hfold_plain] at htc''
              have hfold' :
                  LocSet.foldM ls0 (false, (none : Option Predicate)) (derefFoldF res1.memEnv') =
                    Except.ok v_3 := by
                simpa [LocSet.foldM, derefFoldF] using hfold
              have hlookup_ctx' : res1.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_ctx
              cases hclean with
            | clean hpoison =>
                cases hpred : v_3.2.getD Predicate.noPred with
                | noPred =>
                    simp [pure, Except.pure, hpred] at htc''
                    cases htc''
                    have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                      simpa [hpoison]
                    have hjoined_false : v_3.1 = false :=
                      (joinPoison_eq_false hjoin').2
                    obtain ⟨qt', hlookup', hpoison'⟩ :=
                      deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                    have hqt' : qt' = qt := by
                      have : some qt' = some qt := by
                        calc
                          some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                          _ = some qt := hlookup_ctx'
                      exact Option.some.inj this
                    have hpoison'' : qt.poison = false := by
                      simpa [hqt'] using hpoison'
                    exact qtypCleanUnder.clean hpoison''
                | guardOnly k =>
                    cases htagEnv : res1.tagEnv'[k]? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                          simpa [hpoison]
                        have hjoined_false : v_3.1 = false :=
                          (joinPoison_eq_false hjoin').2
                        obtain ⟨qt', hlookup', hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hpoison'' : qt.poison = false := by
                          simpa [hqt'] using hpoison'
                        exact qtypCleanUnder.clean hpoison''
                    | some tagInfo =>
                        cases tagInfo with
                        | mk val deps =>
                            cases val with
                            | true =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                have hpc : ctxᵢ.pc = false := by
                                  simpa [hpoison]
                                -- regime consistency yields regime lookup = some true
                                have htagEnv' :
                                    (ctxAfter ctxᵢ res1).tagEnv.get? k = some ⟨true, deps⟩ := by
                                  simpa [ctxAfter] using htagEnv
                                -- hreg' uses output regime (ctxAfter ctxᵢ res1).regime
                                have hreg_k' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true :=
                                  (hreg'.1 k deps htagEnv')
                                have hreg_k : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := hreg_k'
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred]
                                  simp [predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using htagqt
                                obtain ⟨qt'', hlookup''⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                exact qtypCleanUnder.guard k htagqt' hreg_k hnotfun'
                            | false =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                cases hpoison
                | guardClosure k a b env =>
                    -- same reasoning as guardOnly
                    cases htagEnv : res1.tagEnv'[k]? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hjoin' : joinPoison ctxᵢ.pc v_3.1 = false := by
                          simpa [hpoison]
                        have hjoined_false : v_3.1 = false :=
                          (joinPoison_eq_false hjoin').2
                        obtain ⟨qt', hlookup', hpoison'⟩ :=
                          deref_foldM_poison_false res1.memEnv' ls0 v_3.1 v_3.2 hfold' hjoined_false l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have hpoison'' : qt.poison = false := by
                          simpa [hqt'] using hpoison'
                        exact qtypCleanUnder.clean hpoison''
                    | some tagInfo =>
                        cases tagInfo with
                        | mk val deps =>
                            cases val with
                            | true =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                have hpc : ctxᵢ.pc = false := by
                                  simpa [hpoison]
                                have htagEnv' :
                                    (ctxAfter ctxᵢ res1).tagEnv.get? k = some ⟨true, deps⟩ := by
                                  simpa [ctxAfter] using htagEnv
                                -- hreg' uses output regime (ctxAfter ctxᵢ res1).regime
                                have hreg_k' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true :=
                                  (hreg'.1 k deps htagEnv')
                                have hreg_k : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := hreg_k'
                                have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k := by
                                  simp [hpred, predGuardTag]
                                obtain ⟨qt', hlookup', htagqt⟩ :=
                                  deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k hfold' hguard l hlin
                                have hqt' : qt' = qt := by
                                  have : some qt' = some qt := by
                                    calc
                                      some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have htagqt' : qtypGuardTag qt = some k := by
                                  simpa [hqt'] using htagqt
                                obtain ⟨qt'', hlookup''⟩ :=
                                  deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                                have hqt'' : qt'' = qt := by
                                  have : some qt'' = some qt := by
                                    calc
                                      some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                                      _ = some qt := hlookup_ctx'
                                  exact Option.some.inj this
                                have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                                have hnotfun' : qt.etyp.isFunctionType = false := by
                                  rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                exact qtypCleanUnder.guard k htagqt' hreg_k hnotfun'
                            | false =>
                                simp [hpred, htagEnv] at htc''
                                cases htc''
                                cases hpoison
            | guard k htag hreg hnotfun =>
                -- merged predicate must carry tag k
                cases hpred : v_3.2.getD Predicate.noPred with
                | noPred =>
                    simp [hpred, pure, Except.pure] at htc''
                    rw [← htc''] at htag
                    -- res.pred is noPred, so qtypGuardTag is none: contradiction
                    simp [qtypGuardTag] at htag
                | guardOnly k' =>
                    -- tagEnv must be none, otherwise res.pred noPred
                    cases htagEnv : res1.tagEnv'[k']? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k' := by
                          simp [hpred, predGuardTag]
                        obtain ⟨qt', hlookup', htagqt⟩ :=
                          deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k' hfold' hguard l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have htagqt' : qtypGuardTag qt = some k := by
                          -- align k' with k using htag
                          simp [qtypGuardTag] at htag
                          rw [hqt', htag] at htagqt
                          simp [predGuardTag] at htagqt
                          simp [qtypGuardTag]
                          cases hqtpred : qt.pred
                            <;> simp [hqtpred] at htagqt
                            <;> simpa using htagqt
                        -- show not function
                        obtain ⟨qt'', hlookup''⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                        have hreg' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := by
                          simpa [ctxAfter, h_regime] using hreg
                        exact qtypCleanUnder.guard k htagqt' hreg' hnotfun'
                    | some val =>
                        simp [hpred, htagEnv, pure, Except.pure] at htc''
                        rcases hval : val with ⟨b, deps⟩; rcases hb : b
                          <;> simp [hval, hb] at htc''
                          <;> rw [← htc''] at htag
                          <;> simp [qtypGuardTag] at htag
                | guardClosure k' a b env =>
                    -- same as guardOnly
                    cases htagEnv : res1.tagEnv'[k']? with
                    | none =>
                        simp [hpred, htagEnv] at htc''
                        cases htc''
                        have hguard : predGuardTag (v_3.2.getD Predicate.noPred) = some k' := by
                          simp [hpred, predGuardTag]
                        obtain ⟨qt', hlookup', htagqt⟩ :=
                          deref_foldM_guardTag res1.memEnv' ls0 v_3.1 v_3.2 k' hfold' hguard l hlin
                        have hqt' : qt' = qt := by
                          have : some qt' = some qt := by
                            calc
                              some qt' = res1.memEnv'.lookup l := by symm; exact hlookup'
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have htagqt' : qtypGuardTag qt = some k := by
                          have hk : k' = k := by
                            simpa [qtypGuardTag, hpred] using htag
                          simpa [hk, hqt'] using htagqt
                        obtain ⟨qt'', hlookup''⟩ :=
                          deref_foldM_etyp_int res1.memEnv' ls0 v_3.1 v_3.2 hfold' l hlin
                        have hqt'' : qt'' = qt := by
                          have : some qt'' = some qt := by
                            calc
                              some qt'' = res1.memEnv'.lookup l := by symm; exact hlookup''
                              _ = some qt := hlookup_ctx'
                          exact Option.some.inj this
                        have het : qt''.etyp = ETyp.int := memEnv_lookup_etyp_int res1.memEnv' l qt'' hlookup''
                        have hnotfun' : qt.etyp.isFunctionType = false := by
                          rw [← hqt'', het]; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                        have hreg'' : (ctxAfter ctxᵢ res1).regime.lookup? k = some true := by
                          simpa [ctxAfter, h_regime] using hreg
                        exact qtypCleanUnder.guard k htagqt' hreg'' hnotfun'
                    | some val =>
                        simp [hpred, htagEnv, pure, Except.pure] at htc''
                        rcases hval : val with ⟨b, deps⟩; rcases hb : b
                          <;> simp [hval, hb] at htc''
                          <;> rw [← htc''] at htag
                          <;> simp [qtypGuardTag] at htag
  have hagree_loc := (hagree_clean_e.1 l qt hlookup_ctx hclean_loc)
  have hEq : o₀ = o₁ := by
    -- Use the agreement on the location to show equality of stored ints.
    cases hagree_loc with
    | both_unrealized _ _ hnone0 hnone1 =>
        -- impossible: deref requires a realized location
        -- contradict θ₀'.lookup l = some a₀'
        rw [hθ₀l] at hnone0
        cases hnone0
    | agree_values _ _ a0 a1 m0 m1 hreal0 hreal1 hm0 hm1 hagree_val =>
        -- The addresses must match those from deref
        have ha0 : a0 = a₀' := by
          have : some a0 = some a₀' := by
            calc
              some a0 = θ₀'.lookup l := by symm; exact hreal0
              _ = some a₀' := by exact hθ₀l
          exact Option.some.inj this
        have ha1 : a1 = a₁' := by
          have : some a1 = some a₁' := by
            calc
              some a1 = θ₁'.lookup l := by symm; exact hreal1
              _ = some a₁' := by exact hθ₁l
          exact Option.some.inj this
        subst ha0; subst ha1
        have hvalEq : m0 = m1 := by
          -- Use the structure of agreeValueUnder on integer values
          cases hagree_val with
          | clean_eq_nonref_nonarrow _ _ _ hEq =>
              cases hEq
              rfl
          | withPred_true_eq _ _ _ _ _ hEq =>
              cases hEq
              rfl
          | clean_ref _ _ _ _ hv1 _ _ =>
              cases hv1
          | @withPred_true_ref k ls l0 a1 a2 qt' v1 v2 _htag _hreg _hetyp _hlookup1 _hin hv1 _hlookup2 _hv2 =>
              cases hv1
          | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow _ hisArrow htyp1 _ =>
              -- Value.num can only have type int, so isArrow must be false.
              have hqte_int : qt.etyp = ETyp.int :=
                valueHasETyp_num_etyp htyp1
              have : qt.etyp.isArrow = false := by
                simp [hqte_int, ETyp.isArrow]
              rw [hisArrow] at this
              cases this
          | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_parrow _ hisParrow htyp1 _ =>
              -- Value.num can only have type int, so isParrow must be false.
              have hqte_int : qt.etyp = ETyp.int :=
                valueHasETyp_num_etyp htyp1
              have : qt.etyp.isParrow = false := by
                simp [hqte_int, ETyp.isParrow]
              rw [hisParrow] at this
              cases this
        -- Use memory lookup equalities
        have : n₀ = n₁ := by
          have : some n₀ = some n₁ := by
            calc
              some n₀ = cfg₀'.memory.lookup a0 := by symm; exact hlookup₀
              _ = some m0 := by simpa [hmem₀] using hm0
              _ = some m1 := by simp [hvalEq]
              _ = cfg₁'.memory.lookup a1 := by symm; simpa [hmem₁] using hm1
              _ = some n₁ := hlookup₁
          exact Option.some.inj this
        -- o₀ and o₁ are Value.num of these ints
        simp [hv₀, hv₁, this]
  -- Build agreement on the return value (int)
  have hres_etyp_int : res.qualType.etyp = ETyp.int :=
    typecheckDeref_etyp_int ctxᵢ e (Nat.succ fuel') res htc'
  have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
    intro hcontra
    rcases hcontra with ⟨ls, h_etyp⟩
    -- deref always returns int
    have : res.qualType.etyp = ETyp.ref ls := h_etyp
    rw [hres_etyp_int] at this
    cases this
  have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
    -- deref returns int
    simp [hres_etyp_int, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  cases hclean with
  | clean hpoison =>
      exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun_res hnotref_res hEq
  | guard k htag hreg hnotfun =>
      exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref_res hEq

-- Stub lemma for while loop (not yet proven)
private lemma stepFR_kwhile
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.kwhile e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.kwhile e1 e2) res predSat tm := by
  sorry


-- I/O-free step theorem: proves StepFR directly (no world-threading)
-- Restructured to avoid variable capture: induction is generalized over all expressions
theorem TypeSystemEnforcesFaultRobustness_step_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat tm := by
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel res htc
  -- Use strong induction on fuel, generalized over all e and ctxᵢ
  -- The key insight: we need IH to work for any I/O-free expression, not just our specific e
  revert e ctxᵢ res htc
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctxᵢ res htc
    cases n with
    | zero =>
        simp [typecheck, typecheckExpr] at htc
    | succ fuel =>
        cases e with
        | unit =>
            simp [typecheck, typecheckExpr, typecheckUnit] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.unit, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? Expr.unit = some Value.unit := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm Expr.unit res Value.unit hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.unit) hpoison hnotfun hnotref hpredNo hctxAfter
        | num n =>
            simp [typecheck, typecheckExpr, typecheckInt] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.int, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.num n) = some (Value.num n) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.num n) res (Value.num n) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.num n) hpoison hnotfun hnotref hpredNo hctxAfter
        | bool b =>
            simp [typecheck, typecheckExpr, typecheckBool] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.bool, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.bool b) = some (Value.bool b) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.bool b) res (Value.bool b) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.bool b) hpoison hnotfun hnotref hpredNo hctxAfter
        | str s =>
            simp [typecheck, typecheckExpr, typecheckString] at htc
            let res_expected : TypeResult := {
              qualType := ⟨ETyp.string, false, Predicate.noPred⟩
              memEnv' := ctxᵢ.memEnv
              tagEnv' := ctxᵢ.tagEnv
              nextLoc' := ctxᵢ.nextLoc
              nextTag' := ctxᵢ.nextTag
              regime' := ctxᵢ.regime
            }
            have hres : res = res_expected := by
              cases htc
              rfl
            have hval : Expr.toValue? (Expr.str s) = some (Value.str s) := by
              simp [Expr.toValue?]
            have hpoison : res.qualType.poison = false := by
              simp [hres, res_expected]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hres, res_expected]
            have hpredNo : res.qualType.pred = Predicate.noPred := by
              simp [hres, res_expected]
            have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
              simp [ctxAfter, hres, res_expected]
            exact stepFR_literal .ioFree ctxᵢ predSat tm (Expr.str s) res (Value.str s) hval (fun _ => by simp [hres, res_expected]; exact valueHasETyp.str s) hpoison hnotfun hnotref hpredNo hctxAfter
        | var name =>
            exact stepFR_var .ioFree ctxᵢ predSat tm name res fuel htc
        | op e1 op e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
            | succ fuel' =>
                exact stepFR_op ctxᵢ predSat e1 e2 op fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | unaryop uop e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
            | succ fuel' =>
                exact stepFR_unaryop ctxᵢ predSat e uop fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | ite e1 e2 e3 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckIf] at htc
            | succ fuel' =>
                exact stepFR_ite ctxᵢ predSat tm e1 e2 e3 fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | newRef e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckNewRef] at htc
            | succ fuel' =>
                exact stepFR_newRef ctxᵢ predSat e fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | assign e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckAssign] at htc
            | succ fuel' =>
                exact stepFR_assign ctxᵢ predSat tm e1 e2 fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | deref e =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckDeref] at htc
            | succ fuel' =>
                exact stepFR_deref ctxᵢ predSat tm e fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | seq e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
            | succ fuel' =>
                exact stepFR_seq ctxᵢ predSat e1 e2 fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | kwhile e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckWhile] at htc
            | succ fuel' =>
                exact stepFR_kwhile ctxᵢ predSat tm e1 e2 fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | vlet z e1 e2 =>
            let vname := z
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
            | succ fuel' =>
                exact stepFR_vlet ctxᵢ predSat vname e1 e2 fuel' res tm (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | fn name ty e1 ty2 =>
            exact stepFR_fn .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | pfn name ty e1 ty2 =>
            exact stepFR_pfn .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
        | app e1 e2 =>
            cases fuel with
            | zero =>
                simp [typecheck, typecheckExpr, typecheckApp] at htc
            | succ fuel' =>
                exact stepFR_app ctxᵢ predSat tm e1 e2 fuel' res (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH) htc
        | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            -- In `.ioFree` mode, I/O constructs cannot terminate, so StepFR is vacuous.
            intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
            have : False := by
              obtain ⟨fuelT, verboseT, heq⟩ := ht₀
              -- In `.ioFree` mode, evaluation yields `ioForbidden`, never `.success`.
              have h_world := congrArg (fun f => f LeanProofs.defaultWorld) heq
              cases fuelT with
              | zero =>
                  -- fuel = 0 yields outOfFuel, not success
                  simp [LeanPoison.beval, pure] at h_world
                  cases h_world
              | succ fuelT' =>
                  -- fuel > 0: these constructs yield ioForbidden, not success
                  simp [LeanPoison.beval, pure] at h_world
                  cases h_world
            exact False.elim this

end TypeSystemEnforcesFaultRobustness_IOFree_proof

-- Bridges from step theorem to full specification
-- FaultRobustnessSpec specialized to ioFree mode (implied by FaultRobustnessSpec)
def FaultRobustnessSpec_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) (_tm : TagMeaning) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (θ₁ θ₂ : RealizationMap) (a₁ a₂ : Address) (pm : Bool),
    ∀ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    ctx.regime.bound = ctx.nextTag →  -- regime bounded by initial tag supply
    wfRegime ctx.regime s →
    regimeBounded ctx.regime →
    wfRealizationMap θ₁ →  wfRealizationMap θ₂ →
    wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } →
    wfConfig { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } →
    inputsConformSpec s μ₁ ρ₁ θ₁ →  inputsConformSpec s μ₂ ρ₂ θ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ θ₂ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₁ ρ₁ θ₁ →
    trustedVarsClosureRegimeInit predSat ctx.regime s ctx μ₂ ρ₂ θ₂ →
    consistentRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ →  consistentRegimeSpec predSat ctx.regime s μ₂ ρ₂ θ₂ →
    agreeOnCriticalInputsUnderRegimeSpec predSat ctx.regime s μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    agreeOnTrustedInputs predSat ctx.regime s ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ →
    terminatesTo .ioFree e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ →
    terminatesTo .ioFree e { memory := μ₂, varEnv := ρ₂, nextAddr := a₂, pureMode := pm } cf₂ o₂ →
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂

-- FaultRobustnessSpec implies FaultRobustnessSpec_ioFree (by instantiating mode = .ioFree)
lemma FaultRobustnessSpec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
    FaultRobustnessSpec e s obs ctx predSat tm → FaultRobustnessSpec_ioFree e s obs ctx predSat tm := by
  intro h
  unfold FaultRobustnessSpec_ioFree
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm cf₁ cf₂ o₁ o₂
  exact h .ioFree μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm cf₁ cf₂ o₁ o₂

def TypeSystemEnforcesFaultRobustness_spec_ioFree
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      wfTypeContext ctx →
      ctx.pc = false →
      ctx.tagEnv = {} →
      ∀ (predSat : PredSat) (tm : TagMeaning),
        wfTagMeaningCtx tm ctx →
        PredSatLaws predSat tm →
        ((∃ (fuel : Nat) (res : TypeResult),
          typecheck .ioFree ctx e fuel = .ok res ∧
          ObsConstraints obs res) →
          FaultRobustnessSpec_ioFree e s obs ctx predSat tm)

-- TypeSystemEnforcesFaultRobustness_spec implies TypeSystemEnforcesFaultRobustness_spec_ioFree
lemma TypeSystemEnforcesFaultRobustness_spec_implies_ioFree (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
    TypeSystemEnforcesFaultRobustness_spec e s obs → TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs := by
  intro h his hos ctx hctx hwf hpc hte predSat tm hwfTm hps htc
  exact FaultRobustnessSpec_implies_ioFree e s obs ctx predSat tm
    (h his hos ctx hctx hwf hpc hte predSat tm hwfTm hps htc)

theorem TypeSystemEnforcesFaultRobustness_impl_IOFree :
  (∀ e ctxᵢ predSat tm, TypeSystemEnforcesFaultRobustness_step_spec .ioFree e ctxᵢ predSat tm) →
  (∀ e s obs, TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs) := by
  intro hstep e s obs
  rintro his _hos ctx hctx hwf _hpc hte predSat tm hwfTm hps ⟨fuel, res, htc, hobs⟩
  rcases hobs with ⟨hobs_ret, hobs_mem⟩
  intro μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ a₁ a₂ pm
  have hstep' := hstep e ctx predSat tm
  have hstep' := hstep' fuel res htc
  intro cf₁ cf₂ o₁ o₂ hR hRbound hregBounded hθ₁ hθ₂ hwfcfg₁ hwfcfg₂ hics₁ hics₂ hric₁ hric₂ htrustedInit₁ htrustedInit₂ hcrs₁ hcrs₂ hagree htrusted ht₁ ht₂
  set R := ctx.regime with hRdef
  have hagree_clean :
      agreeOnClean predSat R ctx μ₁ ρ₁ θ₁ μ₂ ρ₂ θ₂ :=
    agreeOnCriticalAndTrusted_implies_agreeOnClean
      predSat R s ctx μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ hctx hagree htrusted
  have htagR : tagEnvConsistentWithRegime ctx.tagEnv R := by
    intro k deps hlookup
    -- Empty tag environment at the top level.
    have hempty : ctx.tagEnv.get? k = none := by simp [hte]
    rw [hempty] at hlookup
    cases hlookup
  -- regimeConsistentWithCtx is now a conjunction: tagEnvConsistentWithRegime ∧ R.bound ≤ nextTag
  have hreg : regimeConsistentWithCtx ctx := by
    constructor
    · exact htagR
    · exact Nat.le_of_eq hR
  -- Need consistentWithRegime for both runs (derived from bridge lemma)
  have hcwr₁ : consistentWithRegime predSat R ctx μ₁ ρ₁ θ₁ := by
    have hcrs₁' : consistentRegimeSpec predSat R s μ₁ ρ₁ θ₁ := by
      simpa [hRdef] using hcrs₁
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₁ ρ₁ θ₁ hcrs₁' hric₁ (by simpa [hRdef] using htrustedInit₁) his hctx hRbound' hregBounded'
  have hcwr₂ : consistentWithRegime predSat R ctx μ₂ ρ₂ θ₂ := by
    have hcrs₂' : consistentRegimeSpec predSat R s μ₂ ρ₂ θ₂ := by
      simpa [hRdef] using hcrs₂
    have hRbound' : wfRegime R s := by
      simpa [hRdef] using hRbound
    have hregBounded' : regimeBounded R := by
      simpa [hRdef] using hregBounded
    exact
      consistentRegimeSpec_implies_consistentWithRegime
        predSat R s ctx μ₂ ρ₂ θ₂ hcrs₂' hric₂ (by simpa [hRdef] using htrustedInit₂) his hctx hRbound' hregBounded'
  have hstep_fr :=
    hstep' hps hwfTm μ₁ μ₂ ρ₁ ρ₂ θ₁ θ₂ cf₁ cf₂ o₁ o₂
      hθ₁ hθ₂ hwf hric₁ hric₂ hreg hregBounded hcwr₁ hcwr₂ hagree_clean
      a₁ a₂ pm hwfcfg₁ hwfcfg₂ ht₁ ht₂
  -- StepFR result structure: ∃ θ₁' θ₂', wfExtendsMap ∧ wfExtendsMap ∧ valueHasETyp ∧ valueHasETyp ∧
  --   wfTagMeaningCtx ∧ wfTypeContext ∧ wfConfig ∧ wfConfig ∧ ... ∧ agreeOnClean ∧ resultAgreesIfClean
  rcases hstep_fr with ⟨_hresTm, hstep_fr⟩
  rcases hstep_fr with ⟨θ₁', θ₂', hwfext₁, hwfext₂, _hvtyp₁, _hvtyp₂, _hTm', _hwfctx', _hwfcfg₁', _hwfcfg₂', _hric₁', _hric₂', _hreg', _hcwr₁', _hcwr₂', hagree_clean', _hval_consist₁, _hval_consist₂, hret_agree⟩
  refine ⟨θ₁', θ₂', hwfext₁, hwfext₂, ?_⟩
  -- Bridge from post-state agreement to observables.
  simp [observablesEqual]
  constructor
  · -- Observable memory locations agree
    intro l et hobs_lookup
    obtain ⟨qt, hlookup_mem, _het_eq, hpoison⟩ := hobs_mem l et hobs_lookup
    have hctx_lookup : (ctxAfter ctx res).memEnv.lookup l = some qt := by
      simpa [ctxAfter] using hlookup_mem
    -- Use output regime since hagree_clean' now uses (ctxAfter ctx res).regime
    have hclean : qtypCleanUnder (ctxAfter ctx res).regime qt := by
      exact qtypCleanUnder.clean hpoison
    have hlocEntry : agreeLocUnder predSat (ctxAfter ctx res).regime cf₁.memory cf₂.memory θ₁' θ₂' (l, qt) :=
      (hagree_clean'.1 l qt hctx_lookup hclean)
    cases hlocEntry with
    | agree_values _l _qt a₁' a₂' n₁ n₂ hreal₁ hreal₂ hlookup₁ hlookup₂ hagree =>
        -- Reduce to equality of stored ints via agreement on the stored values.
        have hvalEq : n₁ = n₂ := by
          cases hagree with
          | clean_eq_nonref_nonarrow _ _ _ hval =>
              cases hval
              rfl
          | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_arrow hdirty hisArrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isArrow = true implies function type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisArrow) (by decide)
          | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv1 _ =>
              cases hv1
          | dirty_internal_parrow hdirty hisParrow htyp1 htyp2 =>
              -- A Value.num can only have type ETyp.int, but isParrow = true implies parrow type
              have het : qt.etyp = ETyp.int := by
                generalize hqte : qt.etyp = qte at htyp1; cases htyp1; rfl
              exact absurd (het ▸ hisParrow) (by decide)
          | clean_ref _ _ _ _ hv1 _ _ =>
              cases hv1
          | withPred_true_eq _ _ _ _ _ hval =>
              cases hval
              rfl
          | withPred_true_ref _ _ _ _ _ _ hv1 _ _ =>
              cases hv1
        refine Or.inl ?_
        refine ⟨a₁', ?_⟩
        refine And.intro hreal₁ ?_
        refine ⟨a₂', ?_⟩
        refine And.intro hreal₂ ?_
        calc
          cf₁.memory.lookup a₁' = some n₁ := hlookup₁
          _ = some n₂ := by simp [hvalEq]
          _ = cf₂.memory.lookup a₂' := by symm; exact hlookup₂
    | both_unrealized _l _qt _hnone₁ _hnone₂ =>
        exact Or.inr ⟨_hnone₁, _hnone₂⟩
  · -- Return value agrees
    cases hretOpt : obs.retEtyp? with
    | none =>
        simp
    | some et =>
        -- Use return agreement from the step proof.
        rcases hobs_ret _ hretOpt with ⟨hret_et, hret_poison⟩
        have hret_notfun_obs : et.isFunctionType = false := by
          simpa [wfObsSpec, hretOpt] using _hos
        -- Use output regime since hret_agree now uses (ctxAfter ctx res).regime
        have hret_clean : qtypCleanUnder (ctxAfter ctx res).regime res.qualType := by
          exact qtypCleanUnder.clean hret_poison
        have hret_agree' :
            agreeValueUnder predSat (ctxAfter ctx res).regime cf₁.memory cf₂.memory θ₁' θ₂' res.qualType o₁ o₂ :=
          hret_agree hret_clean
        cases et with
        | ref ls =>
            cases hret_agree' with
            | @clean_ref ls' l a₁' a₂' _qt _v₁ _v₂ hpoison' hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by
                  have h_eq : ETyp.ref ls' = ETyp.ref ls := by rw [← hetyp, hret_et]
                  injection h_eq
                subst hls_eq
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | @withPred_true_ref k ls' l a₁' a₂' _qt _v₁ _v₂ htag hregime hetyp hlookup1 hin hv1 hlookup2 hv2 =>
                have hls_eq : ls' = ls := by
                  have h_eq : ETyp.ref ls' = ETyp.ref ls := by rw [← hetyp, hret_et]
                  injection h_eq
                subst hls_eq
                refine And.intro ?_ ?_
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₁', ?_⟩
                  exact And.intro hlookup1 hv1
                · refine ⟨l, ?_⟩
                  refine And.intro hin ?_
                  refine ⟨a₂', ?_⟩
                  exact And.intro hlookup2 hv2
            | clean_eq_nonref_nonarrow _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨ls, hret_et⟩
                exact False.elim this
            | withPred_true_eq _ _ _ _ hnotref _ =>
                have : False := by
                  apply hnotref
                  exact ⟨ls, hret_et⟩
                exact False.elim this
            | clean_internal_arrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_arrow _ hisArrow =>
                -- qt.etyp is an arrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : False := by
                  have hisArrow_ref : (ETyp.ref ls).isArrow = true := by
                    simpa [hret_et] using hisArrow
                  simp [ETyp.isArrow] at hisArrow_ref
                exact False.elim this
            | clean_internal_parrow _ hetyp _ _ _ _ _ _ _ =>
                cases (Eq.trans (Eq.symm hetyp) hret_et)
            | dirty_internal_parrow _ hisParrow =>
                -- qt.etyp is a parrow but hret_et says it's et (from observable spec).
                -- This would contradict if observable types are not function types.
                have : False := by
                  have hisParrow_ref : (ETyp.ref ls).isParrow = true := by
                    simpa [hret_et] using hisParrow
                  simp [ETyp.isParrow] at hisParrow_ref
                exact False.elim this
        | int =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | bool =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | unit =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | string =>
            have hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
              simp [hret_et]
            have hnotfun : res.qualType.etyp.isFunctionType = false := by
              simp [hret_et, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            exact ret_eq_of_agreeValueUnder_nonref hnotref hnotfun hret_poison hret_agree'
        | arrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs
        | parrow st₁ st₂ p tcls =>
            exfalso
            simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hret_notfun_obs

-- Main I/O-free theorem
theorem TypeSystemEnforcesFaultRobustness_IOFree
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesFaultRobustness_spec_ioFree e s obs := by
  apply TypeSystemEnforcesFaultRobustness_impl_IOFree
  · intro e' ctxᵢ predSat tm
    exact TypeSystemEnforcesFaultRobustness_step_IOFree e' ctxᵢ predSat tm
