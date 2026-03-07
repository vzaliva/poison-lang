/-
  StepFRApp.lean - Fault-robustness proof for function application (stepFR_app).

  Contains the stepFR_app lemma and all helper lemmas used exclusively by it,
  including join-transport lemmas, applyFnTClosure/applyPFnTClosure infrastructure,
  and joinTypeResults compatibility lemmas.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

-- Helper lemmas for stepFR_app: join-lifting and body-context bridges.
--
-- Join-transport lemmas: when `joinTypeResults ctx first rest = .ok res`, transport
-- properties from `(ctxAfter ctx first)` to `(ctxAfter ctx res)`. Used by both peClosure
-- and closure branches.

private lemma join_transport_runtimeInstantiatesCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_mem : ∀ l, first.memEnv'.contains l → res.memEnv'.contains l)
  (h_first : runtimeInstantiatesCtx (ctxAfter ctx first) μ ρ θ) :
  runtimeInstantiatesCtx (ctxAfter ctx res) μ ρ θ := by
  unfold runtimeInstantiatesCtx at h_first ⊢
  simp only [ctxAfter]
  constructor
  · intro l a hθ
    have ⟨hcontains, hμ⟩ := h_first.1 l a hθ
    exact ⟨h_mem l hcontains, hμ⟩
  · exact h_first.2

private lemma join_transport_wfTypeContext
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_mem : ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l)
  (h_first : wfTypeContext (ctxAfter ctx first))
  (h_rest_wf : ∀ r ∈ rest, wfTypeResult r) :
  wfTypeContext (ctxAfter ctx res) := by
  intro l hcontains
  simp only [ctxAfter]
  rcases h_mem l hcontains with hfirst | ⟨r, hr_mem, h_in⟩
  · -- l in first
    have hlt := h_first l (by simp only [ctxAfter]; exact hfirst)
    rw [joinTypeResults_nextLoc_eq_max _ _ _ _ _h_join]
    have hle : first.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem
      simp
    exact Nat.lt_of_lt_of_le hlt hle
  · -- l in some r ∈ rest
    have hwf := h_rest_wf r hr_mem
    have hlt := hwf l h_in
    rw [joinTypeResults_nextLoc_eq_max _ _ _ _ _h_join]
    have hle : r.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem
      simp only [List.mem_cons, List.mem_map]
      right
      exact ⟨r, hr_mem, rfl⟩
    exact Nat.lt_of_lt_of_le hlt hle

private lemma join_transport_regimeConsistentWithCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_bound_le : res.regime'.bound ≤ first.regime'.bound)
  (h_tag_join : tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first)) :
  regimeConsistentWithCtx (ctxAfter ctx res) := by
  simp only [regimeConsistentWithCtx, ctxAfter]
  constructor
  · exact h_tag_join
  · have h_first_bound := h_first.2
    rw [joinTypeResults_nextTag_eq_max _ _ _ _ _h_join]
    have hle : first.nextTag' ≤ List.max (first.nextTag' :: rest.map TypeResult.nextTag') (by intro h; cases h) := by
      apply List.le_max_of_mem
      simp
    exact Nat.le_trans h_regime_bound_le (Nat.le_trans h_first_bound hle)

private lemma join_transport_valueConsistentWithRegime
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_first : valueConsistentWithRegime predSat (ctxAfter ctx first).regime qt μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime qt μ θ v :=
  valueConsistentWithRegime_monotone h_regime_mono h_first

-- Single-step: transport closureCapturedVarsRegime across one joinETyps application.
private lemma closureCapturedVarsRegime_joinETyps_step
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegime predSat R ⟨etyp1, p1, pr1⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨joinETyps etyp1 resEtyp p1 resPoison,
    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases etyp1 with
  | int | bool | unit | string =>
      simp [joinETyps]
      exact closureCapturedVarsRegime_transport_etyp (by simp) hcap
  | ref ls =>
      cases resEtyp with
      | ref ls2 =>
          simp only [beqETypSignature] at hcompat
          cases hcap with
          | intro hdeep =>
              cases hdeep with
              | nonClosure hv hpe => exact .intro (.nonClosure hv hpe)
              | closure _ _ _ _ _ _ _ _ _ hetyp_arr _ _ => exfalso; exact ETyp.noConfusion hetyp_arr
              | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_parr _ _ => exfalso; exact ETyp.noConfusion hetyp_parr
      | _ => simp [beqETypSignature] at hcompat
  | arrow st1 st2 p tcls =>
      have hisArrow : resEtyp.isArrow := by cases resEtyp with | arrow => rfl | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_arrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisArrow hcompat
      have hcap' :=
        closureCapturedVarsRegime_weaken_fnTClosures'
          (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegime_transport_etyp heq.symm hcap'
  | parrow st1 st2 p tcls =>
      have hisParrow : resEtyp.isParrow := by cases resEtyp with | parrow => rfl | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_parrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisParrow hcompat
      have hcap' :=
        closureCapturedVarsRegime_weaken_pFnTClosures'
          (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegime_transport_etyp heq.symm hcap'

-- Transport closureCapturedVarsRegime from first.qualType to res.qualType when joinTypeResults succeeds.
-- Proved by induction on the join fold; each step uses closureCapturedVarsRegime_joinETyps_step.
private lemma joinTypeResults_closure_cvcr_transport
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (hcap : closureCapturedVarsRegime predSat R first.qualType μ θ v) :
  closureCapturedVarsRegime predSat R res.qualType μ θ v := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_cvcr :
      ∀ (rs' : List TypeResult) (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        closureCapturedVarsRegime predSat R ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' hcompat hfold hcap_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hcap_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 := (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 x.regime',
              max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcap1 := closureCapturedVarsRegime_joinETyps_step predSat R μ θ v acc.1 resEtyp
              acc.2.2.1 resPoison acc.2.2.2.1 resPred hcompat_x hcap_acc
            have hcap1' : closureCapturedVarsRegime predSat R ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
              simpa [acc1] using hcap1
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by simpa [acc1] using hfold
            exact ih acc1 hcompat_tail hfold_tail hcap1'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ => erw [hcheck] at _h_join; contradiction
      | ok _ =>
          erw [hcheck] at _h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ => erw [hfold] at _h_join; contradiction
          | ok a =>
              erw [hfold] at _h_join
              have heq := Except.ok.inj _h_join
              have hetyp : (⟨a.1, a.2.2.1, a.2.2.2.1⟩ : QTyp).etyp = res.qualType.etyp :=
                congr_arg (·.qualType.etyp) heq
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              have hcvcr_acc := h_fold_cvcr rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') a hcompat hfold
                (hqt ▸ hcap)
              exact closureCapturedVarsRegime_transport_etyp hetyp hcvcr_acc

-- Transport valueConsistentWithRegime when qualType changes from first to res (via pred transport).
private lemma join_transport_valueConsistentWithRegime_resQual
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hpred : res.qualType.pred = first.qualType.pred)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_first : valueConsistentWithRegime predSat (ctxAfter ctx first).regime first.qualType μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v := by
  have h_mono := valueConsistentWithRegime_monotone h_regime_mono h_first
  refine valueConsistentWithRegime_transport_pred' (_hpred.symm)
    (fun hcap => joinTypeResults_closure_cvcr_transport predSat ctx first rest res
      (ctxAfter ctx res).regime μ θ v _h_join hcap) h_mono

-- Weaken runtimeInstantiatesCtx when going from post-e1 context to post-e2 context.
-- Requires memEnv equality (holds when e1 is var/fn/pfn producing arrow).
private lemma runtimeInstantiatesCtx_weaken_ctx
  (ctx : TypeContext) (res_outer res_inner : TypeResult) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_mem_eq : res_outer.memEnv' = res_inner.memEnv')
  (_hric : runtimeInstantiatesCtx (ctxAfter ctx res_inner) μ ρ θ) :
  runtimeInstantiatesCtx (ctxAfter ctx res_outer) μ ρ θ := by
  unfold runtimeInstantiatesCtx
  simp only [ctxAfter, _h_mem_eq]
  exact _hric

-- Obtain runtimeInstantiatesCtx for closure env from post-e1 instantiation and closure typing.
-- The body context needs env₀ (closure's captured env), not c₁₀.varEnv.
-- Requires memEnv equality and that env₀ realises the context's varEnv.
private lemma runtimeInstantiatesCtx_of_closure_env
  (ctx : TypeContext) (res2 res1 : TypeResult) (μ : Memory) (env₀ ρ : VarEnv) (θ : RealizationMap)
  (_h_mem_eq : res2.memEnv' = res1.memEnv')
  (_hric : runtimeInstantiatesCtx (ctxAfter (ctxAfter ctx res2) res1) μ ρ θ)
  (_h_env : ∀ x qt, (ctxAfter ctx res2).varEnv.lookup x = some qt →
    ∃ v, env₀.lookup x = some v ∧ valueHasETyp θ v qt.etyp) :
  runtimeInstantiatesCtx (ctxAfter ctx res2) μ env₀ θ := by
  unfold runtimeInstantiatesCtx at _hric ⊢
  simp only [ctxAfter] at _hric ⊢
  constructor
  · intro l a hθ
    obtain ⟨hctx, hμ⟩ := _hric.1 l a hθ
    rw [_h_mem_eq]; exact ⟨hctx, hμ⟩
  · intro x qt h
    exact _h_env x qt h

-- Inversion for regular closures: from
-- `applyFnTClosure (FnTClosure.regular x body tenv) ... fuel = .ok first`,
-- extract that the application ran with positive fuel.
--
-- Suggested proof strategy:
-- unfold `applyFnTClosure` and split on fuel.
private lemma applyFnTClosure_regular_structure
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate) (result2 : TypeResult) (fuel : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (_happly : applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok first) :
  ∃ fuelBody, fuel = Nat.succ fuelBody := by
  cases fuel with
  | zero =>
      simp [applyFnTClosure] at _happly
  | succ fuelBody =>
      exact ⟨fuelBody, rfl⟩

-- In ioFree mode, extern closure application always throws (so cannot occur in stepFR_app).
private lemma applyFnTClosure_ioFree_extern_fails
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult) :
  applyFnTClosure .ioFree (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel ≠ .ok r := by
  intro h
  cases fuel with
  | zero =>
    unfold applyFnTClosure at h
    simp at h
  | succ _ =>
    unfold applyFnTClosure at h
    have hcond : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := rfl
    simp only [hcond, ite_true, bind, Except.bind] at h
    exact absurd h (Except.error_ne_ok "Extern function application forbidden in ioFree mode" r)

-- Inversion for regular closures: successful application exposes the body typing
-- derivation and successful return-type subtype check.
private lemma applyFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } body fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  unfold applyFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } body fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isSubtype st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

-- If `List.mapM f xs` succeeds and `x ∈ xs`, then `f x` succeeded for some output
-- appearing in the mapped result list.
private lemma list_mapM_ok_mem_input_exists_output
  {α β ε : Type}
  (f : α → Except ε β) :
  ∀ {xs ys x}, List.mapM f xs = .ok ys → x ∈ xs →
    ∃ y, y ∈ ys ∧ f x = .ok y := by
  intro xs ys x hmap hmem
  have hforall2 : List.Forall₂ (fun x y => f x = Except.ok y) xs ys :=
    List.mapM_Except_ok_implies_forall2 xs f ys hmap
  rcases List.Forall2.exists_of_mem_left (R := fun x y => f x = Except.ok y) hforall2 x hmem with
    ⟨y, hy, hxy⟩
  exact ⟨y, hy, hxy⟩

-- Specialized extraction for closure-application maps used in `stepFR_app`.
private lemma applyFnTClosure_ok_of_mem_mapM
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult) (tcl : FnTClosure)
  (hmap : List.mapM
      (fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      tcls = .ok results)
  (hmem : tcl ∈ tcls) :
  ∃ r, r ∈ results ∧
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r := by
  simpa using
    (list_mapM_ok_mem_input_exists_output
      (f := fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      (xs := tcls) (ys := results) (x := tcl) hmap hmem)

-- Combined extraction for regular closures from a successful application map.
-- Gives the selected closure's successful application together with body-typing inversion.
private lemma applyFnTClosure_regular_inv_of_mapM_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (hmap : List.mapM
      (fun tcl' => applyFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx bodyState fuel)
      tcls = .ok results)
  (hmem : FnTClosure.regular x body tenv ∈ tcls) :
  ∃ fuelBody first result3,
    applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx bodyState fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := bodyState.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := bodyState.tagEnv'
        nextTag := bodyState.nextTag'
        nextLoc := bodyState.nextLoc'
        regime := bodyState.regime' } body fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases applyFnTClosure_ok_of_mem_mapM
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel tcls results
      (FnTClosure.regular x body tenv) hmap hmem with
    ⟨first, _hfirst_mem, happly⟩
  rcases applyFnTClosure_regular_structure
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel x body tenv first happly with
    ⟨fuelBody, hfuel⟩
  have happly_succ :
      applyFnTClosure .ioFree (FnTClosure.regular x body tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx bodyState (Nat.succ fuelBody) = .ok first := by
    simpa [hfuel] using happly
  rcases applyFnTClosure_regular_inv
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuelBody x body tenv first happly_succ with
    ⟨result3, htc_body, hsub, hfirst_eq⟩
  exact ⟨fuelBody, first, result3, happly, hfuel, htc_body, hsub, hfirst_eq⟩

-- Forall₂ gives an existence for membership on the right.
private lemma list_Forall2_exists_of_mem_right
    {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} :
    List.Forall₂ R xs ys →
    ∀ y ∈ ys, ∃ x, x ∈ xs ∧ R x y := by
  intro h
  induction h with
  | nil =>
      intro y hy
      cases hy
  | cons hxy _htail ih =>
      intro y hymem
      simp [List.mem_cons] at hymem
      cases hymem with
      | inl hyeq =>
          subst hyeq
          exact ⟨_, by simp, hxy⟩
      | inr hyrest =>
          rcases ih y hyrest with ⟨x, hxmem, hR⟩
          exact ⟨x, by simp [hxmem], hR⟩

-- If `List.mapM f xs` succeeds and `y ∈ ys`, then some `x ∈ xs` maps to `y`.
private lemma list_mapM_ok_mem_output_exists_input
  {α β ε : Type}
  (f : α → Except ε β)
  {xs : List α} {ys : List β} {y : β}
  (hmap : List.mapM f xs = .ok ys)
  (hmem : y ∈ ys) :
  ∃ x, x ∈ xs ∧ f x = .ok y := by
  have hforall2 :
      List.Forall₂ (fun x y => f x = Except.ok y) xs ys :=
    List.mapM_Except_ok_implies_forall2 xs f ys hmap
  rcases list_Forall2_exists_of_mem_right (R := fun x y => f x = Except.ok y) hforall2 y hmem with
    ⟨x, hxmem, hxy⟩
  exact ⟨x, hxmem, hxy⟩

-- Body typecheck in app context: wfTypeResult for result3 from typecheckExpr_preserves_wfTypeResult.
private lemma applyFnTClosure_regular_body_wfTypeResult
  (ctx : TypeContext) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuelBody : Nat)
  (x : Name) (body : Expr) (tenv : CapturedVarEnv)
  (hwf1 : wfTypeResult result1)
  (ctx'' : TypeContext)
  (hctx'' : ctx'' = { ctx with
      pc := joinPoison p (joinPoison p1 ctx.pc)
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      tagEnv := result1.tagEnv'
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' })
  (result3 : TypeResult)
  (htc : typecheckExpr .ioFree ctx'' body fuelBody = .ok result3) :
  wfTypeResult result3 := by
  have hwf_ctx'' : wfTypeContext ctx'' := by
    rw [hctx'']
    simp only [wfTypeContext]
    exact hwf1
  exact typecheckExpr_preserves_wfTypeResult ctx'' body fuelBody result3 hwf_ctx''
    (by simpa [typecheck] using htc)

-- Helper lemmas for wfTagMeaningCtx in closure body contexts.
-- These need to be before applyFnTClosure_ok_wfTypeResult.

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
  have hcapMem : (y, qtCap) ∈ σcap :=
    List_lookup_some_mem y qtCap σcap (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  have hroot :
      QTypInQTyp qtCap qtRes :=
    QTypInQTyp.in_arrow qtCap qtRes st1 st2 p tcls
      (FnTClosure.regular xFun body σcap) y
      hetyp hmem (by simpa [fnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd

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

private lemma wfTagMeaningCtx_closure_body
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
    simpa [ctxCap, ctxAfter] using hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

private lemma PExpr_toExpr_of_toPExpr?_some : ∀ (e : Expr) (pe : PExpr),
    Expr.toPExpr? e = some pe → PExpr.toExpr pe = e
  | .unit, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .num n, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .bool b, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .str s, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .var x, _, h => by simp [Expr.toPExpr?] at h; subst h; rfl
  | .op e1 o e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h
          subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .unaryop o e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .ite e1 e2 e3, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          cases h3 : Expr.toPExpr? e3 with
          | none => simp [h1, h2, h3] at h
          | some pe3 =>
            simp [h1, h2, h3] at h; subst h; simp [PExpr.toExpr]
            exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1,
                   PExpr_toExpr_of_toPExpr?_some e2 pe2 h2,
                   PExpr_toExpr_of_toPExpr?_some e3 pe3 h3⟩
  | .deref e1, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        simp [h1] at h; subst h; simp [PExpr.toExpr]
        exact PExpr_toExpr_of_toPExpr?_some e1 pe1 h1
  | .vlet x e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .app e1 e2, pe, h => by
      simp only [Expr.toPExpr?] at h
      cases h1 : Expr.toPExpr? e1 with
      | none => simp [h1] at h
      | some pe1 =>
        cases h2 : Expr.toPExpr? e2 with
        | none => simp [h1, h2] at h
        | some pe2 =>
          simp [h1, h2] at h; subst h; simp [PExpr.toExpr]
          exact ⟨PExpr_toExpr_of_toPExpr?_some e1 pe1 h1, PExpr_toExpr_of_toPExpr?_some e2 pe2 h2⟩
  | .newRef _, _, h => by simp [Expr.toPExpr?] at h
  | .assign _ _, _, h => by simp [Expr.toPExpr?] at h
  | .seq _ _, _, h => by simp [Expr.toPExpr?] at h
  | .kwhile _ _, _, h => by simp [Expr.toPExpr?] at h
  | .fn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .pfn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .rand _, _, h => by simp [Expr.toPExpr?] at h
  | .frand _, _, h => by simp [Expr.toPExpr?] at h
  | .printString _, _, h => by simp [Expr.toPExpr?] at h
  | .printInt _, _, h => by simp [Expr.toPExpr?] at h
  | .externVal _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externFn _ _ _ _, _, h => by simp [Expr.toPExpr?] at h
  | .externPfn _ _ _, _, h => by simp [Expr.toPExpr?] at h

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
  have hcapMem : (y, qtCap) ∈ σcap :=
    List_lookup_some_mem y qtCap σcap (by simpa [CapturedVarEnv.lookup_eq] using hlookup)
  have hroot :
      QTypInQTyp qtCap qtRes :=
    QTypInQTyp.in_parrow qtCap qtRes st1 st2 p tcls
      (PFnTClosure.regular xFun pbody σcap) y
      hetyp hmem (by simpa [pfnCapturedEnv] using hcapMem)
  exact hresTm (QTypInQTyp.trans qt qtCap qtRes hinq hroot) hqd

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

private lemma wfTagMeaningCtx_pclosure_body
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
    simpa [ctxCap, ctxAfter] using hcapTm
  have hbodyTm :
      wfTagMeaningCtx tm { ctxCap with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) xArg argQt } :=
    wfTagMeaningCtx_varEnv_ext tm ctxCap xArg argQt hctxCapTm hargTm
  simpa [ctxCap] using hbodyTm

-- Layer A (per-member): static facts for successful closure-application typing.
-- wfTypeResult for the body result comes from stepFR IH (StepFR for body → wfTypeResult).
-- These are intentionally isolated so `stepFR_app` can consume them now and we
-- can prove them incrementally.
private lemma applyFnTClosure_ok_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf1 : wfTypeResult result1)
  (tcl : FnTClosure)
  (r : TypeResult)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTypeResult r := by
  cases fuel with
  | zero =>
    unfold applyFnTClosure at happly
    simp at happly
  | succ fuelBody =>
    cases tcl with
    | regular x body tenv =>
      rcases applyFnTClosure_regular_inv ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuelBody
          x body tenv r (by simpa using happly) with
        ⟨result3, htc_body, _hsub, hfirst⟩
      have hwf3 := applyFnTClosure_regular_body_wfTypeResult ctx p p1 argEtyp argPoison argPred
        result1 fuelBody x body tenv hwf1
        { ctx with
          pc := joinPoison p (joinPoison p1 ctx.pc)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := result1.tagEnv'
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
        rfl result3 htc_body
      rw [hfirst]
      exact hwf3
    | extern x retSpec effects capturedEnv =>
      exfalso
      exact applyFnTClosure_ioFree_extern_fails ctx st1 st2 p p1 argEtyp argPoison argPred result1
        (Nat.succ fuelBody) x retSpec effects capturedEnv r happly

-- ==========================================================================
-- typecheckExpr preserves regimeConsistentWithCtx
-- ==========================================================================
-- This is a key preservation theorem: successful typechecking in ioFree mode
-- preserves the regime consistency invariant (tagEnv/regime agreement + bound).

-- Helper: regimeConsistentWithCtx only depends on tagEnv, regime, nextTag
private lemma regimeConsistentWithCtx_of_tagEnv_regime_nextTag
    (ctx₁ ctx₂ : TypeContext)
    (htag : ctx₂.tagEnv = ctx₁.tagEnv)
    (hreg : ctx₂.regime = ctx₁.regime)
    (hnt : ctx₂.nextTag = ctx₁.nextTag)
    (h : regimeConsistentWithCtx ctx₁) :
    regimeConsistentWithCtx ctx₂ := by
  simp only [regimeConsistentWithCtx] at h ⊢
  rw [htag, hreg, hnt]; exact h

private lemma joinTypeResults_tagEnvConsistentWithRegime'
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
              simpa [regimeConsistentWithCtx, ctxAfter] using hx.1
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
                simpa [regimeConsistentWithCtx, ctxAfter] using h_first.1
              exact
                h_fold_tag rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_tag h_rest

private lemma joinTypeResults_regimeConsistentWithCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  regimeConsistentWithCtx (ctxAfter ctx res) := by
  constructor
  · exact joinTypeResults_tagEnvConsistentWithRegime' ctx first rest res h_join h_first h_rest
  · -- res.regime'.bound ≤ res.nextTag'
    -- From joinTypeResults_regime_bound_le_head: res.regime'.bound ≤ first.regime'.bound
    -- From h_first: first.regime'.bound ≤ first.nextTag'
    -- From joinTypeResults_nextTag_eq_max: res.nextTag' = List.max (first.nextTag' :: ...)
    -- So first.nextTag' ≤ res.nextTag'
    have hbound_le_first := joinTypeResults_regime_bound_le_head ctx first rest res h_join
    have hfirst_bound : first.regime'.bound ≤ first.nextTag' := by
      simpa [regimeConsistentWithCtx, ctxAfter] using h_first.2
    have h_nextTag_eq := joinTypeResults_nextTag_eq_max ctx first rest res h_join
    have hfirst_le_res : first.nextTag' ≤ res.nextTag' := by
      rw [h_nextTag_eq]
      apply List.le_max_of_mem
      simp
    show (ctxAfter ctx res).regime.bound ≤ (ctxAfter ctx res).nextTag
    simp [ctxAfter]
    exact Nat.le_trans (Nat.le_trans hbound_le_first hfirst_bound) hfirst_le_res

private lemma typecheckExpr_preserves_regimeConsistentWithCtx_main :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    regimeConsistentWithCtx ctx →
    typecheck .ioFree ctx e fuel = .ok res →
    regimeConsistentWithCtx (ctxAfter ctx res) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res hreg htc
    have IH' : ∀ m < fuel, ∀ (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        regimeConsistentWithCtx ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        regimeConsistentWithCtx (ctxAfter ctx' res') := by
      intro m hm ctx' e' res'; exact IH m hm ctx' e' res'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        cases e with
        -- Literals and simple forms: tagEnv'/regime'/nextTag' = ctx fields
        | num _n =>
            unfold typecheckInt at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | bool _b =>
            unfold typecheckBool at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | unit =>
            unfold typecheckUnit at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | str _s =>
            unfold typecheckString at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | var x =>
            -- typecheckVar always returns tagEnv' = ctx.tagEnv, regime' = ctx.regime, nextTag' = ctx.nextTag
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
                  simp [pure, Except.pure] at htc; cases htc
                  simpa [ctxAfter, regimeConsistentWithCtx]
                | guardOnly k =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; simpa [ctxAfter, regimeConsistentWithCtx]
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        simpa [ctxAfter, regimeConsistentWithCtx]
                | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; simpa [ctxAfter, regimeConsistentWithCtx]
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        simpa [ctxAfter, regimeConsistentWithCtx]
        | fn _ _ _ _ =>
            unfold typecheckFn at htc; simp [pure, Except.pure] at htc; cases htc
            simpa [ctxAfter, regimeConsistentWithCtx]
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ =>
              simp [h_topexpr, pure, Except.pure] at htc; subst htc
              simpa [ctxAfter, regimeConsistentWithCtx]
        -- Impossible in ioFree mode
        | externVal _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternVal at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externFn _ _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternFn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externPfn _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternPfn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | rand _ =>
            simp at htc
            exact absurd htc (typecheckRand_ioFree_impossible ctx _ fuel' res)
        | frand _ =>
            simp at htc
            exact absurd htc (typecheckFrand_ioFree_impossible ctx _ fuel' res)
        | printInt _ =>
            simp at htc
            exact absurd htc (typecheckPrintInt_ioFree_impossible ctx _ fuel' res)
        | printString _ =>
            simp at htc
            exact absurd htc (typecheckPrintString_ioFree_impossible ctx _ fuel' res)
        -- Compound expressions with sub-expression chaining
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, htag, _, hnextTag, hreg', _, _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, _, _, _, _, htag, _, hnextTag, hreg'⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH ⊢
            rwa [htag, hnextTag, hreg']
        | op e1 op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
            rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, _, htag, _, hnextTag, hregime', _, _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx (updateCtxFromResult ctx result1) := by
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck .ioFree (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH' (fuel' - 1) (by omega) (updateCtxFromResult ctx result1) e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
            rwa [htag, hnextTag, hregime']
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · simp [ctxAfter, updateCtxFromResult]
              · exact hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok res := by simpa using htc2
            exact IH' (fuel' - 1) (by omega) ctx' e2 res hreg_mid htc2'
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, htag, _, hnextTag, hregime', _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 result1 hreg htc1'
            have hreg_mid : regimeConsistentWithCtx ctx' := by
              rw [hctx']
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
              · simp [ctxAfter]
              · simp [ctxAfter]
              · simp [ctxAfter]
              · exact hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH' (fuel' - 1) (by omega) ctx' e2 result2 hreg_mid htc2'
            simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
            rwa [htag, hnextTag, hregime']
        | assign e1 e2 =>
            unfold typecheckAssign at htc
            cases fuel' with
            | zero => simp at htc
            | succ fuel'' =>
            simp only [bind, Except.bind] at htc
            cases h_tc1 : typecheckExpr .ioFree ctx e1 fuel'' with
            | error _ => simp [h_tc1] at htc
            | ok result1 =>
              simp only [h_tc1] at htc
              have htc1' : typecheck .ioFree ctx e1 fuel'' = .ok result1 := by simpa using h_tc1
              have hIH1 := IH' fuel'' (by omega) ctx e1 result1 hreg htc1'
              cases h_qt1 : result1.qualType with
              | mk etyp1 p1 pred1 =>
                rw [h_qt1] at htc; simp at htc
                cases etyp1 with
                | ref ls =>
                  simp at htc
                  set ctx2 : TypeContext := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                  have hreg2 : regimeConsistentWithCtx ctx2 := by
                    apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result1)
                    · simp [ctxAfter, ctx2]
                    · simp [ctxAfter, ctx2]
                    · simp [ctxAfter, ctx2]
                    · exact hIH1
                  cases h_tc2 : typecheckExpr .ioFree ctx2 e2 fuel'' with
                  | error _ => simp [h_tc2] at htc
                  | ok result2 =>
                    simp only [h_tc2] at htc
                    have htc2' : typecheck .ioFree ctx2 e2 fuel'' = .ok result2 := by simpa using h_tc2
                    have hIH2 := IH' fuel'' (by omega) ctx2 e2 result2 hreg2 htc2'
                    cases h_qt2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                      rw [h_qt2] at htc; simp at htc
                      by_cases h_etyp2_int : etyp2 = ETyp.int
                      · subst h_etyp2_int; simp at htc; cases htc
                        simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
                        constructor
                        · exact invalidateRegimeDeps_preserves_true result2.tagEnv' result2.regime' ls hIH2.1
                        · simpa [invalidateRegimeDeps] using hIH2.2
                      · simp [h_etyp2_int] at htc
                | _ => simp at htc
        | ite e1 e2 e3 =>
            -- typecheckExpr dispatches to typecheckIf with fuel already decremented to fuel'
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            rcases hstruct with h1 | h2 | h3 | h4
            · -- Mode 1: R(k) = true, then-branch effective
              rcases h1 with ⟨k, deps, _, hRk, _, _, _, res2, htc2, hmem, htag, _, hnextTag, hregEq, _⟩
              have hreg_true : regimeConsistentWithCtx { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } := by
                constructor
                · exact tagEnvConsistentWithRegime_insert_true ctx.tagEnv ctx.regime k deps hreg.1 hRk
                · exact hreg.2
              -- htc2 is at fuel' - 1; convert to typecheck call for IH
              have htc2' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 (fuel' - 1) = .ok res2 := by simpa using htc2
              have hIH2 := IH' (fuel' - 1) (by omega) { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hreg_true htc2'
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH2 ⊢
              rwa [htag, hnextTag, hregEq]
            · -- Mode 2: R(k) = false, else-branch effective
              rcases h2 with ⟨k, deps, _, _, _, _, _, res3, htc3, hmem, htag, _, hnextTag, hregEq, _⟩
              have hreg_false : regimeConsistentWithCtx { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } := by
                constructor
                · exact tagEnvConsistentWithRegime_insert_false ctx.tagEnv ctx.regime k deps hreg.1
                · exact hreg.2
              have htc3' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } e3 (fuel' - 1) = .ok res3 := by simpa using htc3
              have hIH3 := IH' (fuel' - 1) (by omega) { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } e3 res3 hreg_false htc3'
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH3 ⊢
              rwa [htag, hnextTag, hregEq]
            · -- Mode 3: R(k) = none, conservative join
              -- Tag insertion k↦true breaks tagEnvConsistentWithRegime when R(k)=none
              -- This case requires specialized handling (parallel to stepFR_ite_mode3 sorry)
              sorry
            · -- Mode 4: Standard (matchGuard fails), join of both branches
              rcases h4 with ⟨_, res1, htc1, _, res2, htc2, res3, htc3, hmem, htag, _, hnextTag, hregEq, _⟩
              have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok res1 := by simpa using htc1
              have hIH1 := IH' (fuel' - 1) (by omega) ctx e1 res1 hreg htc1'
              -- Build ctx' (after e1)
              set ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                     nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
              have hreg1 : regimeConsistentWithCtx ctx' := by
                apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx res1)
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · simp [ctxAfter, ctx']
                · exact hIH1
              -- ctx'' just changes pc, doesn't affect regimeConsistentWithCtx
              set ctx'' := { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
              have hreg1' : regimeConsistentWithCtx ctx'' := hreg1
              have htc2' : typecheck .ioFree ctx'' e2 (fuel' - 1) = .ok res2 := by simpa using htc2
              have hIH2 := IH' (fuel' - 1) (by omega) ctx'' e2 res2 hreg1' htc2'
              -- ctxForE3: same tagEnv/regime as ctx'', but nextLoc/nextTag from res2
              set ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
              -- ctxForE3 has tagEnv/regime from ctx'' (= res1's), but nextLoc/nextTag from res2
              -- Need: tagEnvConsistentWithRegime ctx''.tagEnv ctx''.regime (from IH1)
              -- Need: ctx''.regime.bound ≤ res2.nextTag' (from IH1 bound + nextTag mono)
              have hIH1_tagEnv : tagEnvConsistentWithRegime res1.tagEnv' res1.regime' := by
                have h := hIH1; simp only [ctxAfter, regimeConsistentWithCtx] at h; exact h.1
              have hIH1_bound : res1.regime'.bound ≤ res1.nextTag' := by
                have h := hIH1; simp only [ctxAfter, regimeConsistentWithCtx] at h; exact h.2
              have hnextTag_mono : res1.nextTag' ≤ res2.nextTag' := by
                have : ctx''.nextTag ≤ res2.nextTag' :=
                  typecheck_nextTag_mono .ioFree ctx'' e2 (fuel' - 1) res2 htc2'
                simpa [ctx'', ctx'] using this
              have hreg2 : regimeConsistentWithCtx ctxForE3 := by
                constructor
                · -- tagEnvConsistentWithRegime: ctxForE3.tagEnv = ctx''.tagEnv = res1.tagEnv'
                  show tagEnvConsistentWithRegime ctxForE3.tagEnv ctxForE3.regime
                  simp only [ctxForE3, ctx'', ctx']
                  exact hIH1_tagEnv
                · -- bound: ctxForE3.regime.bound = res1.regime'.bound ≤ res1.nextTag' ≤ res2.nextTag'
                  show ctxForE3.regime.bound ≤ ctxForE3.nextTag
                  simp only [ctxForE3, ctx'', ctx']
                  exact Nat.le_trans hIH1_bound hnextTag_mono
              have htc3' : typecheck .ioFree ctxForE3 e3 (fuel' - 1) = .ok res3 := by simpa using htc3
              have hIH3 := IH' (fuel' - 1) (by omega) ctxForE3 e3 res3 hreg2 htc3'
              have hIH2' : regimeConsistentWithCtx (ctxAfter ctx'' res2) := hIH2
              simp only [ctxAfter, regimeConsistentWithCtx] at hIH2' hIH3 ⊢
              rw [htag, hnextTag, hregEq]
              constructor
              · exact tagEnvConsistentWithRegime_join res2.tagEnv' res3.tagEnv' res2.regime' res3.regime' hIH2'.1 hIH3.1
              · -- (joinRegimes res2.regime' res3.regime').bound ≤ max res2.nextTag' res3.nextTag'
                show (joinRegimes res2.regime' res3.regime').bound ≤ max res2.nextTag' res3.nextTag'
                unfold joinRegimes; simp only
                exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hIH2'.2 (Nat.le_max_left _ _))
        | app e1 e2 =>
            simp at htc
            -- htc : typecheckApp .ioFree ctx e1 e2 fuel' = .ok res
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
            -- htc : typecheckApp .ioFree ctx e1 e2 (fuel''.succ) = .ok res
            rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
              ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩
            -- IH on e2 (fuel'' < fuel''.succ.succ = fuel)
            have hIH2 := IH' fuel'' (by omega) ctx e2 result2 hreg htc2
            -- Build regime consistency for the e1 typecheck context
            have hreg' : regimeConsistentWithCtx
                (⟨ctx.pc, result2.regime', result2.memEnv', ctx.varEnv, result2.tagEnv',
                  result2.nextLoc', result2.nextTag', ctx.pureCtx⟩ : TypeContext) := by
              apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter ctx result2)
              · simp [ctxAfter]
              · simp [ctxAfter]
              · simp [ctxAfter]
              · exact hIH2
            -- IH on e1 (fuel'' < fuel)
            have hIH1 := IH' fuel'' (by omega) _ e1 result1 hreg' htc1
            -- Helper: for any closure result r from applyFnTClosure, regimeConsistentWithCtx (ctxAfter ctx r)
            -- Derive regimeConsistentWithCtx for the body context (same tagEnv/regime/nextTag as ctxAfter _ result1)
            have hIH1_tagEnv : tagEnvConsistentWithRegime result1.tagEnv' result1.regime' := by
              have := hIH1.1; simp [ctxAfter] at this; exact this
            have hIH1_bound : result1.regime'.bound ≤ result1.nextTag' := by
              have := hIH1.2; simp [ctxAfter] at this; exact this
            have h_fn_closure_reg :
                ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
                  (results : List TypeResult),
                  List.mapM (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'') tcls = .ok results →
                  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro st1 st2 p p1 tcls results hmap r hr
              rcases list_mapM_ok_mem_output_exists_input
                  (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'')
                  (hmap := hmap) (hmem := hr) with
                ⟨tcl, _htcl_mem, happly⟩
              cases tcl with
              | regular x body env =>
                cases fuel'' with
                | zero => simp [applyFnTClosure] at happly
                | succ k =>
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
                      have hreg_body : regimeConsistentWithCtx
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                            tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                            nextLoc := result1.nextLoc', regime := result1.regime' } := by
                        exact ⟨hIH1_tagEnv, hIH1_bound⟩
                      have htcBody' : typecheck .ioFree
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                            tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                            nextLoc := result1.nextLoc', regime := result1.regime' }
                          body k = .ok result3 := by simpa using htcBody
                      have hIH_body := IH' k (by omega) _ body result3 hreg_body htcBody'
                      simp only [ctxAfter, regimeConsistentWithCtx] at hIH_body ⊢
                      exact hIH_body
              | extern x retSpec effects capturedEnv =>
                cases fuel'' with
                | zero => simp [applyFnTClosure] at happly
                | succ k =>
                  simp only [applyFnTClosure] at happly
                  have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                  rw [hioFree] at happly
                  simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
                  exact absurd happly (by simp)
            -- Helper: for any closure result r from applyPFnTClosure, regimeConsistentWithCtx (ctxAfter ctx r)
            have h_pfn_closure_reg :
                ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
                  (results : List TypeResult),
                  List.mapM (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'') tcls = .ok results →
                  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
              intro st1 st2 p p1 tcls results hmap r hr
              rcases list_mapM_ok_mem_output_exists_input
                  (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel'')
                  (hmap := hmap) (hmem := hr) with
                ⟨tcl, _htcl_mem, happly⟩
              cases tcl with
              | regular x body env =>
                cases fuel'' with
                | zero => simp [applyPFnTClosure] at happly
                | succ k =>
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
                          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                          tagEnv := result1.tagEnv', nextTag := result1.nextTag',
                          pureCtx := true,
                          nextLoc := result1.nextLoc', regime := result1.regime' }
                      have hreg_body : regimeConsistentWithCtx bodyCtx := by
                        constructor
                        · exact hIH1.1
                        · exact hIH1.2
                      have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) k = .ok result3 := by simpa using htcBody
                      have hIH_body := IH' k (by omega) bodyCtx (PExpr.toExpr body) result3 hreg_body htcBody'
                      apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
                      · simp [ctxAfter]
                      · simp [ctxAfter]
                      · simp [ctxAfter]
                      · exact hIH_body
              | extern x retSpec capturedEnv =>
                cases fuel'' with
                | zero => simp [applyPFnTClosure] at happly
                | succ k =>
                  simp only [applyPFnTClosure] at happly
                  have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                  rw [hioFree] at happly
                  simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
                  exact absurd happly (by simp)
            -- Now handle arrow/parrow cases
            rcases hcases with
              ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1, _hpure, _hne, _hsub, hmap, hresults, h_join⟩ |
              ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1, _hne, _hsub, hmap, hresults, h_join⟩
            · -- Arrow case
              subst hresults
              have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtx (ctxAfter ctx r) :=
                h_fn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
              exact joinTypeResults_regimeConsistentWithCtx ctx first rest res h_join
                (h_all_reg first (List.mem_cons_self ..))
                (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))
            · -- Parrow case
              subst hresults
              have h_all_reg : ∀ r, r ∈ (first :: rest) → regimeConsistentWithCtx (ctxAfter ctx r) :=
                h_pfn_closure_reg st1 st2 p p1 tcls (first :: rest) hmap
              exact joinTypeResults_regimeConsistentWithCtx ctx first rest res h_join
                (h_all_reg first (List.mem_cons_self ..))
                (fun r hr => h_all_reg r (List.mem_cons_of_mem _ hr))
        | kwhile e1 e2 =>
            simp at htc
            sorry -- permanently postponed: kwhile proofs are out of active scope

lemma typecheckExpr_preserves_regimeConsistentWithCtx
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hreg : regimeConsistentWithCtx ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    regimeConsistentWithCtx (ctxAfter ctx res) :=
  typecheckExpr_preserves_regimeConsistentWithCtx_main fuel ctx e res hreg htc

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

/-- typecheckIf always produces a result with pred = noPred in ioFree mode. -/
private lemma typecheckIf_pred_noPred
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckIf .ioFree ctx e1 e2 e3 fuel = .ok res) :
    res.qualType.pred = Predicate.noPred := by
  cases fuel with
  | zero => simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind] at htc
    cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
    | ok kd =>
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      cases hregime : ctx.regime.lookup? k with
      | some b =>
        cases b with
        | true =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · have heq_mode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                  pure, Except.pure, heq_mode] at htc
                cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
                | error e => rw [htc2] at htc; simp at htc
                | ok result2 =>
                  rw [htc2] at htc; simp at htc
                  match hq2 : result2.qualType with
                  | ⟨_, _, _⟩ =>
                    simp only [hq2] at htc
                    injection htc with heq_res; rw [← heq_res]
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
        | false =>
          simp only [hregime] at htc
          cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            match hq1 : result1.qualType with
            | ⟨etyp1, _, _⟩ =>
              simp only [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · have heq_mode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
                simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                  pure, Except.pure, heq_mode] at htc
                cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
                | error e => rw [htc3] at htc; simp at htc
                | ok result3 =>
                  rw [htc3] at htc; simp at htc
                  match hq3 : result3.qualType with
                  | ⟨_, _, _⟩ =>
                    simp only [hq3] at htc
                    injection htc with heq_res; rw [← heq_res]
              · simp only [hbool, bne_iff_ne, ne_eq] at htc
                cases htc
      | none =>
        simp only [hregime] at htc
        cases htc1 : typecheckExpr .ioFree { ctx with pureCtx := true } e1 fuel' with
        | error e => simp only [htc1] at htc; cases htc
        | ok result1 =>
          simp only [htc1] at htc
          match hq1 : result1.qualType with
          | ⟨etyp1, _, _⟩ =>
            simp only [hq1] at htc
            by_cases hbool : etyp1 = ETyp.bool
            · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                pure, Except.pure] at htc
              cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
              | error e => rw [htc2] at htc; simp at htc
              | ok result2 =>
                rw [htc2] at htc; simp at htc
                match hq2 : result2.qualType with
                | ⟨etyp2, _, _⟩ =>
                  simp only [hq2] at htc
                  cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
                  | error e => rw [htc3] at htc; cases htc
                  | ok result3 =>
                    rw [htc3] at htc
                    match hq3 : result3.qualType with
                    | ⟨etyp3, _, _⟩ =>
                      simp only [hq3] at htc
                      by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                      · simp only [hcompat, ↓reduceIte] at htc; cases htc
                      · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                          cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                        simp only [hcompat'] at htc; cases htc; simp [*]
            · simp only [hbool, bne_iff_ne, ne_eq] at htc
              cases htc
    | error err =>
      simp only [hmatch] at htc
      cases htc1 : typecheckExpr .ioFree ctx e1 fuel' with
      | error e => simp only [htc1] at htc; cases htc
      | ok result1 =>
        simp only [htc1] at htc
        match hq1 : result1.qualType with
        | ⟨etyp1, _, _⟩ =>
          simp only [hq1] at htc
          by_cases hbool : etyp1 = ETyp.bool
          · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
            cases htc2 : typecheckExpr .ioFree _ e2 fuel' with
            | error e => rw [htc2] at htc; cases htc
            | ok result2 =>
              rw [htc2] at htc
              match hq2 : result2.qualType with
              | ⟨etyp2, _, _⟩ =>
                simp only [hq2] at htc
                cases htc3 : typecheckExpr .ioFree _ e3 fuel' with
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
                      simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        pure, Except.pure, Except.ok.injEq] at htc
                      subst htc; rfl
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
-- (Moved before _main because ite modes 3/4 need it.)
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
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x hetyp htcl hcap hjoined => by
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
        (fun qtInner qtOuter st₁ st₂ _p tcls tcl x hetyp htcl hcap hjoined => by
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

/-- Body typecheck preserves wfTagMeaningCtx (fuel induction).
    wfTagMeaningCtx tm ctx = EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv, so we need
    to show that after typechecking, all guard descriptors in (ctx.varEnv, res.memEnv')
    are in tm. Since ctxAfter preserves varEnv, the varEnv side is automatic. For memEnv,
    we track how each expression form transforms memEnv and use join/update lemmas. -/
private lemma typecheckExpr_preserves_wfTagMeaningCtx_main :
    ∀ (fuel : Nat) (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    wfTagMeaningCtx tm ctx →
    typecheck .ioFree ctx e fuel = .ok res →
    wfTagMeaningCtx tm (ctxAfter ctx res) ∧ QTypRespectsTagMeaning tm res.qualType := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro tm ctx e res hwf htc
    have IH_wf : ∀ m < fuel, ∀ (tm' : TagMeaning) (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        wfTagMeaningCtx tm' ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        wfTagMeaningCtx tm' (ctxAfter ctx' res') := by
      intro m hm tm' ctx' e' res' hwf' htc'; exact (IH m hm tm' ctx' e' res' hwf' htc').1
    have IH_qt : ∀ m < fuel, ∀ (tm' : TagMeaning) (ctx' : TypeContext) (e' : Expr) (res' : TypeResult),
        wfTagMeaningCtx tm' ctx' →
        typecheck .ioFree ctx' e' m = .ok res' →
        QTypRespectsTagMeaning tm' res'.qualType := by
      intro m hm tm' ctx' e' res' hwf' htc'; exact (IH m hm tm' ctx' e' res' hwf' htc').2
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        -- ===== Trivial cases: memEnv unchanged (ctxAfter preserves both varEnv and memEnv) =====
        -- Result qualType has noPred + non-function etyp → QTypRespectsTagMeaning vacuous
        | num _n =>
            unfold typecheckInt at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | bool _b =>
            unfold typecheckBool at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | unit =>
            unfold typecheckUnit at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | str _s =>
            unfold typecheckString at htc; simp [pure, Except.pure] at htc; cases htc
            refine ⟨by simpa [wfTagMeaningCtx, ctxAfter], ?_⟩
            exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ rfl rfl
        | var x =>
            -- typecheckVar always returns memEnv' = ctx.memEnv
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
                -- All var sub-cases have non-function etyp (function case errors) and
                -- result pred ∈ {noPred, guardOnly k} → qtypGuardDesc? = none → QTypRespects vacuous
                cases pred with
                | noPred =>
                  simp [pure, Except.pure] at htc; cases htc
                  refine ⟨?_, ?_⟩
                  · simpa [wfTagMeaningCtx, ctxAfter]
                  · exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                      ⟨etyp, poison, Predicate.noPred⟩ _
                      (wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ hwf hlookup)
                      (by simp) (by simp [qtypGuardDesc?])
                | guardOnly k =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc
                              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                                QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                          QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                  | true => simp [hfn] at htc
                | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  cases hfn : etyp.isFunctionType with
                  | false =>
                    simp [hfn] at htc
                    have hqt_orig : QTypRespectsTagMeaning tm ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩ :=
                      wfTagMeaningCtx_var_lookup_qtyp tm ctx x _ hwf hlookup
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc
                              -- pred preserved as guardClosure — transport from original var binding
                              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                                QTypRespectsTagMeaning_transport_etyp_pred tm
                                  ⟨etyp, poison, Predicate.guardClosure k tcls ptcls body_t⟩
                                  ⟨etyp, joinPoison ctx.pc poison, Predicate.guardClosure k tcls ptcls body_t⟩
                                  hqt_orig rfl rfl⟩
                    | some tv => cases tv with | mk val deps =>
                      -- true/false → result pred = noPred
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                        exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                          QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hfn (by simp [qtypGuardDesc?])⟩
                  | true => simp [hfn] at htc
        | fn x st1 body st2 =>
            unfold typecheckFn at htc; simp [pure, Except.pure] at htc; cases htc
            exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
              QTypRespectsTagMeaning_fn_regular tm ctx x st1 st2 ctx.pc body hwf⟩
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok pbody =>
              simp [h_topexpr, pure, Except.pure] at htc; subst htc
              exact ⟨by simpa [wfTagMeaningCtx, ctxAfter],
                QTypRespectsTagMeaning_pfn_regular tm ctx x st1 st2 ctx.pc pbody hwf⟩
        -- Impossible in ioFree mode
        | externVal _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternVal at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externFn _ _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternFn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | externPfn _ _ _ =>
            exfalso; simp at htc; unfold typecheckExternPfn at htc
            have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
            simp only [heq, ite_true, bind, Except.bind] at htc
            exact absurd htc (Except.error_ne_ok _ _)
        | rand _ =>
            simp at htc
            exact absurd htc (typecheckRand_ioFree_impossible ctx _ fuel' res)
        | frand _ =>
            simp at htc
            exact absurd htc (typecheckFrand_ioFree_impossible ctx _ fuel' res)
        | printInt _ =>
            simp at htc
            exact absurd htc (typecheckPrintInt_ioFree_impossible ctx _ fuel' res)
        | printString _ =>
            simp at htc
            exact absurd htc (typecheckPrintString_ioFree_impossible ctx _ fuel' res)
        -- ===== Single-IH cases: memEnv from sub-expression =====
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, result_etyp, htc1, _hopEtyp, hmemEnv, _, _, _, _, hetyp, _, hpred⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            refine ⟨?_, ?_⟩
            · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv] using hIH
            · -- result_etyp from opUnaryEType? is always non-function (bool)
              have hnf : result_etyp.isFunctionType = false := by
                have : result_etyp = .bool := by
                  revert _hopEtyp; unfold opUnaryEType?; split <;> simp [eq_comm]
                subst this; decide
              apply QTypRespectsTagMeaning_of_nonFunction_noGuard
              · rw [hetyp]; exact hnf
              · simp [qtypGuardDesc?, hpred]
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, hmem, _, _, _, _⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            refine ⟨?_, ?_⟩
            · simpa [wfTagMeaningCtx, ctxAfter, hmem] using hIH
            · -- deref result qualType depends on memEnv lookup — use sorry for now
              sorry
        -- ===== Double-IH cases: memEnv chains through sub-expressions =====
        | op e1 _op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 _op fuel' res htc
            rcases hstruct with ⟨result1, result2, result_etyp, htc1, htc2, _hopEtyp, hmemEnv, _, _, _, _, hetyp, _, hpred⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hwf_mid : wfTagMeaningCtx tm (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck .ioFree (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2 := IH_wf (fuel' - 1) (by omega) tm (updateCtxFromResult ctx result1) e2 result2 hwf_mid htc2'
            refine ⟨?_, ?_⟩
            · simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hmemEnv] using hIH2
            · -- result_etyp from opEType? is always non-function (int/bool/float/string)
              have hnf : result_etyp.isFunctionType = false := by
                have : result_etyp = .int ∨ result_etyp = .bool := by
                  revert _hopEtyp; unfold opEType?; split <;> simp [eq_comm] <;> tauto
                rcases this with rfl | rfl <;> decide
              apply QTypRespectsTagMeaning_of_nonFunction_noGuard
              · rw [hetyp]; exact hnf
              · simp [qtypGuardDesc?, hpred]
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hwf_mid : wfTagMeaningCtx tm ctx' := by
              rw [hctx']
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using hIH1
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok res := by simpa using htc2
            -- IH on e2 gives both parts: wfTagMeaningCtx and QTypRespectsTagMeaning
            have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm ctx' e2 res hwf_mid htc2'
            have hIH2_qt : QTypRespectsTagMeaning tm res.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx' e2 res hwf_mid htc2'
            exact ⟨by simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult, hctx'] using hIH2_wf,
                   hIH2_qt⟩
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp_res, hmemEnv, _, _, _, _, _, hpred_res⟩
            have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok result1 := by simpa using htc1
            have hIH1_wf := IH_wf (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            have hIH1_qt : QTypRespectsTagMeaning tm result1.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx e1 result1 hwf htc1'
            -- ctx' extends varEnv with x ↦ result1.qualType. Use IH_qt for the new binding.
            have hwf_mid : wfTagMeaningCtx tm ctx' := by
              rw [hctx']
              have hwf_after : wfTagMeaningCtx tm (ctxAfter ctx result1) := hIH1_wf
              simp only [wfTagMeaningCtx, ctxAfter] at hwf_after
              let ctxBase : TypeContext :=
                ⟨ctx.pc, result1.regime', result1.memEnv', ctx.varEnv, result1.tagEnv',
                 result1.nextLoc', result1.nextTag', ctx.pureCtx⟩
              exact wfTagMeaningCtx_varEnv_ext tm ctxBase x result1.qualType
                (by simpa [wfTagMeaningCtx, ctxAfter, ctxBase] using hwf_after)
                hIH1_qt
            have htc2' : typecheck .ioFree ctx' e2 (fuel' - 1) = .ok result2 := by simpa using htc2
            have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm ctx' e2 result2 hwf_mid htc2'
            have hIH2_qt : QTypRespectsTagMeaning tm result2.qualType :=
              IH_qt (fuel' - 1) (by omega) tm ctx' e2 result2 hwf_mid htc2'
            refine ⟨?_, ?_⟩
            · -- wfTagMeaningCtx: mix varEnv from hwf, memEnv from IH2
              simp only [wfTagMeaningCtx, ctxAfter]
              rw [hmemEnv]
              have hIH2' : EnvRespectsTagMeaning tm ctx'.varEnv result2.memEnv' := by
                simpa [wfTagMeaningCtx, ctxAfter] using hIH2_wf
              exact EnvRespectsTagMeaning_mix tm ctx.varEnv ctx.memEnv ctx'.varEnv result2.memEnv' hwf hIH2'
            · -- QTypRespectsTagMeaning: res.qualType has same etyp and pred as result2.qualType
              exact QTypRespectsTagMeaning_transport_etyp_pred tm result2.qualType res.qualType
                hIH2_qt (by rw [hetyp_res]) (by rw [hpred_res])
        -- ===== Memory update cases =====
        | newRef e1 =>
            sorry -- TODO: updateMemEnv with new location
        | assign e1 e2 =>
            sorry -- TODO: updateMemEnv / updateLocsetWeak
        -- ===== Branch/join cases =====
        -- All ite modes produce noPred in result qualType.
        | ite e1 e2 e3 =>
            simp at htc
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            cases hstruct with
            | inl h1 =>
                -- Mode 1: only true branch. res.qualType.etyp = res2.qualType.etyp, pred = noPred
                rcases h1 with ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, hmemEnv, _, _, _, _, _, hetyp_res⟩
                have htc2' : typecheck .ioFree { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 (fuel' - 1) = .ok res2 := by
                  simpa [typecheck] using htc2
                have hwf_true : wfTagMeaningCtx tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } := by
                  simpa [wfTagMeaningCtx, ctxAfter] using hwf
                have hIH2_wf := IH_wf (fuel' - 1) (by omega) tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hwf_true htc2'
                have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                  IH_qt (fuel' - 1) (by omega) tm { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 res2 hwf_true htc2'
                refine ⟨?_, ?_⟩
                · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv] using hIH2_wf
                · exact QTypRespectsTagMeaning_of_etyp_noPred tm res2.qualType res.qualType
                    hIH2_qt hetyp_res (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
            | inr h_rest =>
              cases h_rest with
              | inl h2 =>
                  -- Mode 2: only false branch. res.qualType.etyp = res3.qualType.etyp, pred = noPred
                  rcases h2 with ⟨k, deps, _, _, res1, _htc1, _hbool, res3, htc3, hmemEnv, _, _, _, _, _, hetyp_res⟩
                  let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                  have htc3' : typecheck .ioFree ctxFalse e3 (fuel' - 1) = .ok res3 := by
                    simpa [typecheck, ctxFalse] using htc3
                  have hwf_false : wfTagMeaningCtx tm ctxFalse := by
                    simpa [wfTagMeaningCtx, ctxAfter, ctxFalse] using hwf
                  have hIH3_wf := IH_wf (fuel' - 1) (by omega) tm ctxFalse e3 res3 hwf_false htc3'
                  have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                    IH_qt (fuel' - 1) (by omega) tm ctxFalse e3 res3 hwf_false htc3'
                  refine ⟨?_, ?_⟩
                  · simpa [wfTagMeaningCtx, ctxAfter, hmemEnv, ctxFalse] using hIH3_wf
                  · exact QTypRespectsTagMeaning_of_etyp_noPred tm res3.qualType res.qualType
                      hIH3_qt hetyp_res (typecheckIf_pred_noPred ctx e1 e2 e3 fuel' res htc)
              | inr h_rest2 =>
                cases h_rest2 with
                | inl h3 =>
                    -- Mode 3: both branches, join. res.qualType.pred = noPred.
                    rcases h3 with ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, res3, htc3_raw, hmemEnv, _, _, _, _, _hpoison, hetyp_res, hpred_res⟩
                    let branchPc := joinPoison ctx.pc res1.qualType.poison
                    let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
                    have htc2' : typecheck .ioFree ctxTrue e2 (fuel' - 1) = .ok res2 := by
                      simpa [typecheck, ctxTrue, branchPc] using htc2
                    have hwf_true : wfTagMeaningCtx tm ctxTrue := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxTrue] using hwf
                    have hIH2 := IH_wf (fuel' - 1) (by omega) tm ctxTrue e2 res2 hwf_true htc2'
                    have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctxTrue e2 res2 hwf_true htc2'
                    -- For mode 3 false branch QTypRespects
                    let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
                    have htc3' : typecheck .ioFree { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } e3 (fuel' - 1) = .ok res3 := by
                      simpa [typecheck, ctxFalse, branchPc] using htc3_raw
                    have hwf_false : wfTagMeaningCtx tm { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxFalse] using hwf
                    have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } e3 res3 hwf_false htc3'
                    have hIH2' : EnvRespectsTagMeaning tm ctx.varEnv res2.memEnv' := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctxTrue] using hIH2
                    refine ⟨?_, ?_⟩
                    · simp only [wfTagMeaningCtx, ctxAfter]
                      rw [hmemEnv]
                      exact EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv res2.memEnv' res3.memEnv' hIH2'
                    · -- Use joinStep + etyp_noPred transport.
                      -- @[reducible] QTypRespectsTagMeaning requires intro + full application.
                      cases hq2 : res2.qualType with
                      | mk e2 p2 pred2 =>
                      cases hq3 : res3.qualType with
                      | mk e3' p3 pred3 =>
                      have hjoin_qt : QTypRespectsTagMeaning tm
                          ⟨joinETyps e2 e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩ :=
                        QTypRespectsTagMeaning_joinStep tm e2 e3' p2 p3 pred2 pred3
                          (hq2 ▸ hIH2_qt) (hq3 ▸ hIH3_qt)
                      simp only [hq2, hq3] at hetyp_res
                      intro q' k' d' hinq hgd
                      exact QTypRespectsTagMeaning_of_etyp_noPred tm
                        ⟨joinETyps e2 e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩
                        res.qualType hjoin_qt hetyp_res hpred_res hinq hgd
                | inr h4 =>
                    -- Mode 4: matchGuard fails, both branches, join. res.qualType.pred = noPred.
                    obtain ⟨⟨err, _hmatch_fail⟩, res1, htc1, _hbool, res2, htc2, res3, htc3_raw, hmemEnv, _, _, _, _, _hpoison, hetyp_res, hpred_res⟩ := h4
                    let ctx1 : TypeContext := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                                         nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
                    let pc' := joinPoison ctx.pc res1.qualType.poison
                    let ctx'' := { ctx1 with pc := pc' }
                    have htc1' : typecheck .ioFree ctx e1 (fuel' - 1) = .ok res1 := by simpa [typecheck] using htc1
                    have hIH1 := IH_wf (fuel' - 1) (by omega) tm ctx e1 res1 hwf htc1'
                    have hwf_mid : wfTagMeaningCtx tm ctx'' := by
                      simp only [wfTagMeaningCtx, ctx'', ctx1]
                      simpa [wfTagMeaningCtx, ctxAfter] using hIH1
                    have htc2' : typecheck .ioFree ctx'' e2 (fuel' - 1) = .ok res2 := by
                      simpa [typecheck, ctx'', ctx1, pc'] using htc2
                    have hIH2 := IH_wf (fuel' - 1) (by omega) tm ctx'' e2 res2 hwf_mid htc2'
                    have hIH2_qt : QTypRespectsTagMeaning tm res2.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctx'' e2 res2 hwf_mid htc2'
                    -- For mode 4 false branch QTypRespects
                    let ctx''3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                    have htc3' : typecheck .ioFree ctx''3 e3 (fuel' - 1) = .ok res3 := by
                      simpa [typecheck, ctx''3, ctx'', ctx1, pc'] using htc3_raw
                    have hwf_mid3 : wfTagMeaningCtx tm ctx''3 := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctx''3, ctx'', ctx1] using hwf_mid
                    have hIH3_qt : QTypRespectsTagMeaning tm res3.qualType :=
                      IH_qt (fuel' - 1) (by omega) tm ctx''3 e3 res3 hwf_mid3 htc3'
                    have hIH2' : EnvRespectsTagMeaning tm ctx.varEnv res2.memEnv' := by
                      simpa [wfTagMeaningCtx, ctxAfter, ctx'', ctx1] using hIH2
                    refine ⟨?_, ?_⟩
                    · simp only [wfTagMeaningCtx, ctxAfter]
                      rw [hmemEnv]
                      exact EnvRespectsTagMeaning_joinMemEnvsStrong' tm ctx.varEnv res2.memEnv' res3.memEnv' hIH2'
                    · -- @[reducible] QTypRespectsTagMeaning requires intro + full application.
                      cases hq2 : res2.qualType with
                      | mk e2' p2 pred2 =>
                      cases hq3 : res3.qualType with
                      | mk e3' p3 pred3 =>
                      have hjoin_qt : QTypRespectsTagMeaning tm
                          ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩ :=
                        QTypRespectsTagMeaning_joinStep tm e2' e3' p2 p3 pred2 pred3
                          (hq2 ▸ hIH2_qt) (hq3 ▸ hIH3_qt)
                      simp only [hq2, hq3] at hetyp_res
                      intro q' k' d' hinq hgd
                      exact QTypRespectsTagMeaning_of_etyp_noPred tm
                        ⟨joinETyps e2' e3' p2 p3, joinPoison p2 p3, joinPredicates pred2 pred3⟩
                        res.qualType hjoin_qt hetyp_res hpred_res hinq hgd
        -- notExpr is not a constructor of Expr; it desugars during parsing
        -- ===== App and kwhile cases =====
        | app e1 e2 =>
            sorry -- TODO: body typecheck + joinTypeResults
        | kwhile e1 e2 =>
            sorry -- permanently postponed: kwhile proofs are out of active scope

private lemma typecheckExpr_preserves_wfTagMeaningCtx
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    wfTagMeaningCtx tm (ctxAfter ctx res) :=
  (typecheckExpr_preserves_wfTagMeaningCtx_main fuel tm ctx e res hwf htc).1

private lemma typecheckExpr_preserves_QTypRespectsTagMeaning
    (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTagMeaningCtx tm ctx)
    (htc : typecheck .ioFree ctx e fuel = .ok res) :
    QTypRespectsTagMeaning tm res.qualType :=
  (typecheckExpr_preserves_wfTagMeaningCtx_main fuel tm ctx e res hwf htc).2

private lemma applyFnTClosure_ok_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
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
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          -- r = { result3 with qualType := normalizeAppResultByProvenance (joinPoison p1 p) taintedQt }
          -- ctxAfter ctx r has varEnv = ctx.varEnv, memEnv = result3.memEnv'
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          -- Body context wfTagMeaningCtx
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          -- Body preservation gives wfTagMeaningCtx for post-body context
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            typecheckExpr_preserves_wfTagMeaningCtx tm bodyCtx body fuel' result3 hwf_body htcBody'
          -- Mix: inVar from hctxTm1 (ctx.varEnv), inMem from hIH (result3.memEnv')
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec effects capturedEnv =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

private lemma applyFnTClosure_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
  cases tcl with
  | regular x body env =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure, bind, Except.bind] at happly
      -- Split on typecheckExpr result in happly
      split at happly
      · -- error case: happly is Except.error = .ok, contradiction
        exact absurd happly (Except.error_ne_ok _ _)
      · -- ok case
        next result3 htcBody =>
        cases hqt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
        simp only [hqt3] at happly
        split at happly
        · simp at happly
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          have hreg_body : regimeConsistentWithCtx bodyCtx := by
            constructor
            · exact hreg1.1
            · exact hreg1.2
          have hIH := typecheckExpr_preserves_regimeConsistentWithCtx bodyCtx body fuel' result3 hreg_body htcBody'
          apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
          · simp [ctxAfter]
          · simp [ctxAfter]
          · simp [ctxAfter]
          · exact hIH
  | extern x retSpec effects capturedEnv =>
    -- extern closures are impossible in ioFree mode
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

private lemma applyFnTClosure_ok_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : FnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
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
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          -- r.qualType = normalizeAppResultByProvenance (joinPoison p1 p) { result3.qualType with poison := taintedPoison }
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx body fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_closure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact typecheckExpr_preserves_QTypRespectsTagMeaning tm bodyCtx body fuel' result3 hwf_body htcBody'
          -- Transport through normalizeAppResultByProvenance
          simp only [normalizeAppResultByProvenance]
          split
          · -- p1 = true: pred becomes noPred
            intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · -- p1 = false: same etyp and pred, only poison differs
            intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec effects capturedEnv =>
    cases fuel with
    | zero => simp [applyFnTClosure] at happly
    | succ fuel' =>
      simp only [applyFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      simp at happly

private lemma mapM_applyFnTClosure_forall_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf_result1 : wfTypeResult result1)
  (tcls : List FnTClosure) (results : List TypeResult)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTypeResult r := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_wfTypeResult
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel)
      hwf_result1 (tcl := tcl) (r := r) happly

private lemma mapM_applyFnTClosure_forall_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_wfTagMeaningCtx
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma mapM_applyFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma mapM_applyFnTClosure_forall_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List FnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyFnTClosure_ok_QTypRespectsTagMeaning
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma joinTypeResults_tagEnvConsistentWithRegime
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (h_first : regimeConsistentWithCtx (ctxAfter ctx first))
  (h_rest : ∀ r ∈ rest, regimeConsistentWithCtx (ctxAfter ctx r)) :
  tagEnvConsistentWithRegime (ctxAfter ctx res).tagEnv (ctxAfter ctx res).regime :=
  joinTypeResults_tagEnvConsistentWithRegime' ctx first rest res h_join h_first h_rest

-- Any deep sub-type of a tag-meaning-respecting type also respects tag meaning.
private lemma QTypRespectsTagMeaning_sub (tm : TagMeaning) {qt qt' : QTyp}
    (h : QTypRespectsTagMeaning tm qt) (hinq : QTypInQTyp qt' qt) :
    QTypRespectsTagMeaning tm qt' :=
  fun hinq'' hqd => h (QTypInQTyp.trans _ qt' qt hinq'' hinq) hqd

private lemma joinTypeResults_QTypRespectsTagMeaning
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
  -- Fold invariant: the accumulated (etyp, poison, pred) satisfies QTypRespectsTagMeaning.
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
            -- Use term-mode proof to avoid simpa + @[reducible] metavariable issues
            have hacc1 : QTypRespectsTagMeaning tm ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ :=
              QTypRespectsTagMeaning_joinStep tm acc.1 resEtyp acc.2.2.1 resPoison
                acc.2.2.2.1 resPred hacc (hqx ▸ hx)
            have hrs_tail : ∀ r ∈ xs, QTypRespectsTagMeaning tm r.qualType := by
              intro r hr; exact hrs r (by simp [hr])
            -- Use show to force correct return type; avoids @[reducible] expansion issues
            show QTypRespectsTagMeaning tm ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩
            exact ih (acc := acc1) hfold_tail hacc1 hrs_tail
  -- Apply the fold lemma and handle the finalPred adjustment.
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
              erw [hfold] at h_join; simp at h_join; subst res
              -- Pre-compute to avoid metavariable issues with simpa + reducible def
              have h_first_qtm : QTypRespectsTagMeaning tm ⟨etyp, poison, pred⟩ :=
                hqt ▸ h_first
              -- Get QTypRespectsTagMeaning for the fold result
              have h_fold_result :
                  QTypRespectsTagMeaning tm ⟨a.1, a.2.2.1, a.2.2.2.1⟩ :=
                h_fold_qtm rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first_qtm h_rest
              -- Decompose a and reduce tuple projections
              obtain ⟨e, m, p, pred', te, r, l, t⟩ := a
              simp only at h_fold_result ⊢
              -- Case-split on the etyp to reduce the match and pick the right transport lemma.
              -- Each branch uses `show` to reduce `match e with ...` to a concrete pred.
              cases e with
              | int =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.int, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.int, p, pred'⟩ ⟨ETyp.int, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | bool =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.bool, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.bool, p, pred'⟩ ⟨ETyp.bool, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | unit =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.unit, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.unit, p, pred'⟩ ⟨ETyp.unit, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | string =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.string, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.string, p, pred'⟩ ⟨ETyp.string, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | ref ls =>
                  show QTypRespectsTagMeaning tm ⟨ETyp.ref ls, joinPoison ctx.pc p, pred'⟩
                  exact QTypRespectsTagMeaning_transport_etyp_pred tm
                    ⟨ETyp.ref ls, p, pred'⟩ ⟨ETyp.ref ls, joinPoison ctx.pc p, pred'⟩
                    h_fold_result rfl rfl
              | arrow st1 st2 pa tcls =>
                  -- finalPred = noPred for arrow types; use noGuard transport
                  show QTypRespectsTagMeaning tm
                    ⟨ETyp.arrow st1 st2 pa tcls, joinPoison ctx.pc p, Predicate.noPred⟩
                  exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                    ⟨ETyp.arrow st1 st2 pa tcls, p, pred'⟩
                    ⟨ETyp.arrow st1 st2 pa tcls, joinPoison ctx.pc p, Predicate.noPred⟩
                    h_fold_result rfl (by simp [qtypGuardDesc?])
              | parrow st1 st2 pa ptcls =>
                  -- finalPred = noPred for parrow types; use noGuard transport
                  show QTypRespectsTagMeaning tm
                    ⟨ETyp.parrow st1 st2 pa ptcls, joinPoison ctx.pc p, Predicate.noPred⟩
                  exact QTypRespectsTagMeaning_transport_etyp_noGuard tm
                    ⟨ETyp.parrow st1 st2 pa ptcls, p, pred'⟩
                    ⟨ETyp.parrow st1 st2 pa ptcls, joinPoison ctx.pc p, Predicate.noPred⟩
                    h_fold_result rfl (by simp [qtypGuardDesc?])

-- Inversion for regular pure-closures: from
-- `applyPFnTClosure (PFnTClosure.regular x pbody tenv) ... fuel = .ok first`,
-- extract that the application ran with positive fuel.
private lemma applyPFnTClosure_regular_structure
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate) (result2 : TypeResult) (fuel : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (_happly : applyPFnTClosure .ioFree (PFnTClosure.regular x pbody tenv) st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok first) :
  ∃ fuelBody, fuel = Nat.succ fuelBody := by
  cases fuel with
  | zero =>
      simp [applyPFnTClosure] at _happly
  | succ fuelBody =>
      exact ⟨fuelBody, rfl⟩

-- Inversion for regular pure-closures: successful application exposes the body typing
-- derivation and successful return-type subtype check.
private lemma applyPFnTClosure_regular_inv
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuelBody : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (first : TypeResult)
  (happly :
    applyPFnTClosure .ioFree (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx result2 (Nat.succ fuelBody) = .ok first) :
  ∃ result3,
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  unfold applyPFnTClosure at happly
  simp [bind, Except.bind] at happly
  cases htc_body : typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result2.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result2.tagEnv'
        pureCtx := true
        nextTag := result2.nextTag'
        nextLoc := result2.nextLoc'
        regime := result2.regime' } (PExpr.toExpr pbody) fuelBody with
  | error err =>
      simp [htc_body] at happly
  | ok result3 =>
      simp [htc_body] at happly
      cases hsub : isSubtype st2 result3.qualType with
      | false =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                simpa [hq3] using hsub
              simp [hq3, hsub'] at happly
      | true =>
          cases hq3 : result3.qualType with
          | mk et3 p3 pred3 =>
              have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                simpa [hq3] using hsub
              have happly' :
                  (Except.ok first : Except String TypeResult) =
                    Except.ok
                      { result3 with
                        qualType :=
                          normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3.qualType with
                              poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                simpa [hq3, hsub', pure, Except.pure] using happly.symm
              have hfirst :
                  first =
                    { result3 with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3.qualType with
                            poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
                injection happly' with hEq
              exact ⟨result3, rfl, hsub, hfirst⟩

-- Specialized extraction for pure-closure application maps used in `stepFR_app`.
private lemma applyPFnTClosure_ok_of_mem_mapM
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult) (tcl : PFnTClosure)
  (hmap : List.mapM
      (fun tcl' => applyPFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      tcls = .ok results)
  (hmem : tcl ∈ tcls) :
  ∃ r, r ∈ results ∧
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r := by
  simpa using
    (list_mapM_ok_mem_input_exists_output
      (f := fun tcl' => applyPFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
      (xs := tcls) (ys := results) (x := tcl) hmap hmem)

-- Combined extraction for regular pure-closures from a successful application map.
-- Gives the selected closure's successful application together with body-typing inversion.
private lemma applyPFnTClosure_regular_inv_of_mapM_mem
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (bodyState : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (hmap : List.mapM
      (fun tcl' => applyPFnTClosure .ioFree tcl' st1 st2 p p1 argEtyp argPoison argPred ctx bodyState fuel)
      tcls = .ok results)
  (hmem : PFnTClosure.regular x pbody tenv ∈ tcls) :
  ∃ fuelBody first result3,
    applyPFnTClosure .ioFree (PFnTClosure.regular x pbody tenv) st1 st2 p p1
      argEtyp argPoison argPred ctx bodyState fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := bodyState.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := bodyState.tagEnv'
        pureCtx := true
        nextTag := bodyState.nextTag'
        nextLoc := bodyState.nextLoc'
        regime := bodyState.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases applyPFnTClosure_ok_of_mem_mapM
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel tcls results
      (PFnTClosure.regular x pbody tenv) hmap hmem with
    ⟨first, _hfirst_mem, happly⟩
  rcases applyPFnTClosure_regular_structure
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuel x pbody tenv first happly with
    ⟨fuelBody, hfuel⟩
  have happly_succ :
      applyPFnTClosure .ioFree (PFnTClosure.regular x pbody tenv) st1 st2 p p1
        argEtyp argPoison argPred ctx bodyState (Nat.succ fuelBody) = .ok first := by
    simpa [hfuel] using happly
  rcases applyPFnTClosure_regular_inv
      ctx st1 st2 p p1 argEtyp argPoison argPred bodyState fuelBody x pbody tenv first happly_succ with
    ⟨result3, htc_body, hsub, hfirst_eq⟩
  exact ⟨fuelBody, first, result3, happly, hfuel, htc_body, hsub, hfirst_eq⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Parrow (PFnTClosure) versions of the per-member preservation lemmas.
-- These mirror the FnTClosure versions above, using applyPFnTClosure.
-- ═══════════════════════════════════════════════════════════════════════════

private lemma applyPFnTClosure_ioFree_extern_fails
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (r : TypeResult) :
  applyPFnTClosure .ioFree (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel ≠ .ok r := by
  intro h
  cases fuel with
  | zero =>
    unfold applyPFnTClosure at h
    simp at h
  | succ _ =>
    unfold applyPFnTClosure at h
    have hcond : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := rfl
    simp only [hcond, ite_true, bind, Except.bind] at h
    exact absurd h (Except.error_ne_ok "Extern function application forbidden in ioFree mode" r)

private lemma applyPFnTClosure_regular_body_wfTypeResult
  (ctx : TypeContext) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuelBody : Nat)
  (x : Name) (pbody : PExpr) (tenv : CapturedVarEnv)
  (hwf1 : wfTypeResult result1)
  (ctx'' : TypeContext)
  (hctx'' : ctx'' = { ctx with
      pc := joinPoison p (joinPoison ctx.pc p1)
      memEnv := result1.memEnv'
      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
      tagEnv := result1.tagEnv'
      pureCtx := true
      nextTag := result1.nextTag'
      nextLoc := result1.nextLoc'
      regime := result1.regime' })
  (result3 : TypeResult)
  (htc : typecheckExpr .ioFree ctx'' (PExpr.toExpr pbody) fuelBody = .ok result3) :
  wfTypeResult result3 := by
  have hwf_ctx'' : wfTypeContext ctx'' := by
    rw [hctx'']
    simp only [wfTypeContext]
    exact hwf1
  exact typecheckExpr_preserves_wfTypeResult ctx'' (PExpr.toExpr pbody) fuelBody result3 hwf_ctx''
    (by simpa [typecheck] using htc)

private lemma applyPFnTClosure_ok_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf1 : wfTypeResult result1)
  (tcl : PFnTClosure)
  (r : TypeResult)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTypeResult r := by
  cases fuel with
  | zero =>
    unfold applyPFnTClosure at happly
    simp at happly
  | succ fuelBody =>
    cases tcl with
    | regular x pbody tenv =>
      rcases applyPFnTClosure_regular_inv ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuelBody
          x pbody tenv r (by simpa using happly) with
        ⟨result3, htc_body, _hsub, hfirst⟩
      have hwf3 := applyPFnTClosure_regular_body_wfTypeResult ctx p p1 argEtyp argPoison argPred
        result1 fuelBody x pbody tenv hwf1
        { ctx with
          pc := joinPoison p (joinPoison ctx.pc p1)
          memEnv := result1.memEnv'
          varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
          tagEnv := result1.tagEnv'
          pureCtx := true
          nextTag := result1.nextTag'
          nextLoc := result1.nextLoc'
          regime := result1.regime' }
        rfl result3 htc_body
      rw [hfirst]
      exact hwf3
    | extern x retSpec capturedEnv =>
      exfalso
      exact applyPFnTClosure_ioFree_extern_fails ctx st1 st2 p p1 argEtyp argPoison argPred result1
        (Nat.succ fuelBody) x retSpec capturedEnv r happly

private lemma applyPFnTClosure_ok_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  wfTagMeaningCtx tm (ctxAfter ctx r) := by
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
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hIH : wfTagMeaningCtx tm (ctxAfter bodyCtx result3) :=
            typecheckExpr_preserves_wfTagMeaningCtx tm bodyCtx (PExpr.toExpr body) fuel' result3 hwf_body htcBody'
          show wfTagMeaningCtx tm (ctxAfter ctx _)
          unfold wfTagMeaningCtx at hctxTm1 hIH ⊢
          simp only [ctxAfter] at hctxTm1 hIH ⊢
          exact EnvRespectsTagMeaning_mix tm ctx.varEnv result1.memEnv'
            bodyCtx.varEnv result3.memEnv' hctxTm1 hIH
  | extern x retSpec capturedEnv =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

private lemma applyPFnTClosure_ok_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  regimeConsistentWithCtx (ctxAfter ctx r) := by
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
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hreg_body : regimeConsistentWithCtx bodyCtx := by
            constructor
            · exact hreg1.1
            · exact hreg1.2
          have hIH := typecheckExpr_preserves_regimeConsistentWithCtx bodyCtx (PExpr.toExpr body) fuel' result3 hreg_body htcBody'
          apply regimeConsistentWithCtx_of_tagEnv_regime_nextTag (ctxAfter bodyCtx result3)
          · simp [ctxAfter]
          · simp [ctxAfter]
          · simp [ctxAfter]
          · exact hIH
  | extern x retSpec capturedEnv =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      exact absurd happly (by simp)

private lemma applyPFnTClosure_ok_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcl : PFnTClosure) (r : TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hmem_tcl : tcl ∈ tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel = .ok r) :
  QTypRespectsTagMeaning tm r.qualType := by
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
        · next hsub =>
          simp only [pure, Except.pure] at happly
          cases happly
          set bodyCtx := { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result1.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result1.tagEnv', nextTag := result1.nextTag',
              pureCtx := true,
              nextLoc := result1.nextLoc', regime := result1.regime' }
          have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr body) fuel' = .ok result3 := by simpa using htcBody
          have hargTm' : QTypRespectsTagMeaning tm ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            QTypRespectsTagMeaning_transport_etyp_pred tm
              ⟨argEtyp, argPoison, argPred⟩ ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              hargTm rfl rfl
          have hwf_body : wfTagMeaningCtx tm bodyCtx := by
            simpa [bodyCtx, ctxAfter] using
              wfTagMeaningCtx_pclosure_body tm ctx result1 result1.qualType st1 st2 p tcls
                x body env x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                hctxTm1 hresTm1 hetyp1 hmem_tcl hargTm'
          have hresTm3 : QTypRespectsTagMeaning tm ⟨etyp3, p3, pred3⟩ := by
            rw [← hqt3]
            exact typecheckExpr_preserves_QTypRespectsTagMeaning tm bodyCtx (PExpr.toExpr body) fuel' result3 hwf_body htcBody'
          simp only [normalizeAppResultByProvenance]
          split
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_of_etyp_noPred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, true, Predicate.noPred⟩ hresTm3 rfl rfl hinq hgd
          · intro q' k' d' hinq hgd
            exact QTypRespectsTagMeaning_transport_etyp_pred tm ⟨etyp3, p3, pred3⟩
              ⟨etyp3, joinPoison p1 (joinPoison p p3), pred3⟩ hresTm3 rfl rfl hinq hgd
  | extern x retSpec capturedEnv =>
    cases fuel with
    | zero => simp [applyPFnTClosure] at happly
    | succ fuel' =>
      simp only [applyPFnTClosure] at happly
      have hioFree : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by native_decide
      rw [hioFree] at happly
      simp only [ite_true] at happly; simp only [bind, Except.bind] at happly
      simp at happly

private lemma mapM_applyPFnTClosure_forall_wfTypeResult'
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (hwf_result1 : wfTypeResult result1)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTypeResult r := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_wfTypeResult
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel)
      hwf_result1 (tcl := tcl) (r := r) happly

private lemma mapM_applyPFnTClosure_forall_wfTagMeaningCtx
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_wfTagMeaningCtx
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

private lemma mapM_applyPFnTClosure_forall_regimeConsistentWithCtx
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (hreg1 : regimeConsistentWithCtx (ctxAfter ctx result1))
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → regimeConsistentWithCtx (ctxAfter ctx r) := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, _htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_regimeConsistentWithCtx
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hreg1 happly

private lemma mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning
  (tm : TagMeaning)
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (tcls : List PFnTClosure)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (results : List TypeResult)
  (hctxTm1 : wfTagMeaningCtx tm (ctxAfter ctx result1))
  (hresTm1 : QTypRespectsTagMeaning tm result1.qualType)
  (hetyp1 : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hargTm : QTypRespectsTagMeaning tm ⟨argEtyp, argPoison, argPred⟩)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results) :
  ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType := by
  intro r hr
  rcases list_mapM_ok_mem_output_exists_input
      (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      (hmap := hmap) (hmem := hr) with
    ⟨tcl, htcl_mem, happly⟩
  exact
    applyPFnTClosure_ok_QTypRespectsTagMeaning
      (tm := tm)
      (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
      (tcls := tcls)
      (argEtyp := argEtyp) (argPoison := argPoison) (argPred := argPred)
      (result1 := result1) (fuel := fuel) (tcl := tcl) (r := r)
      hctxTm1 hresTm1 hetyp1 htcl_mem hargTm happly

-- Body context instantiation: establishing runtimeInstantiatesCtx for the closure body
-- context. Requires strengthening valueHasETyp.closure (henv) to existential form.
--
-- Suggested proof strategy:
-- use `valueHasETyp.closure` to recover captured-env typing, then build the two
-- conjuncts of `runtimeInstantiatesCtx` for the body context:
-- 1) location/memory part is inherited from `_hric` (memEnv is `result2.memEnv'`);
-- 2) variable part combines captured bindings + updated argument binding.
--
-- Helpful already-proven ingredients:
-- * `runtimeInstantiatesCtx_of_closure_env` in this file (for env substitution),
-- * var-env update lookup lemmas from `RegimeConsistency.lean`.
private lemma runtimeInstantiatesCtx_closure_body
  (ctx : TypeContext) (result2 : TypeResult) (x : Name) (tenv : CapturedVarEnv)
  (argQt : QTyp) (argVal : Value) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_hric : runtimeInstantiatesCtx (ctxAfter ctx result2) μ ρ θ)
  (_harg : valueHasETyp θ argVal argQt.etyp)
  (_hcap : ∀ y qt, (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ∃ v, ρ.lookup y = some v ∧ valueHasETyp θ v qt.etyp) :
  let bodyVarEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x argQt
  let bodyCtx : TypeContext := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime', varEnv := bodyVarEnv }
  runtimeInstantiatesCtx bodyCtx μ (VarEnv.update ρ x argVal) θ := by
  intro bodyVarEnv bodyCtx
  constructor
  · intro l a hθ
    -- memEnv/heap obligations are inherited from the post-`e2` context.
    exact _hric.1 l a hθ
  · intro y qt hlookup
    have hlookup_var : bodyVarEnv.lookup y = some qt := by
      simpa [bodyCtx] using hlookup
    by_cases hyx : y = x
    · subst y
      refine ⟨argVal, ?_⟩
      constructor
      · simp [VarEnv.update, VarEnv.lookup]
      · have hx_lookup : bodyVarEnv.lookup x = some argQt :=
          VarTypeEnv_lookup_update_eq (VarTypeEnv.ofCaptured tenv) x argQt
        have hqt : qt = argQt := by
          have : some qt = some argQt := by
            calc
              some qt = bodyVarEnv.lookup x := by symm; exact hlookup_var
              _ = some argQt := hx_lookup
          exact Option.some.inj this
        simpa [hqt] using _harg
    · have hlookup_cap : (VarTypeEnv.ofCaptured tenv).lookup y = some qt := by
        have hne_lookup :
            bodyVarEnv.lookup y = (VarTypeEnv.ofCaptured tenv).lookup y :=
          VarTypeEnv_lookup_update_ne (VarTypeEnv.ofCaptured tenv) x y argQt hyx
        simpa [hne_lookup] using hlookup_var
      rcases _hcap y qt hlookup_cap with ⟨v, hlookupρ, hvtyp⟩
      refine ⟨v, ?_⟩
      constructor
      · have hne_lookup :
            (VarEnv.update ρ x argVal).lookup y = ρ.lookup y :=
          VarEnv_lookup_update_ne ρ x y argVal hyx
        simpa [hne_lookup] using hlookupρ
      · exact hvtyp

-- Bridge from closure typing's captured-env implication (`henv`) to the existential
-- payload required by `runtimeInstantiatesCtx_closure_body`, under an explicit
-- captured-env domain coverage assumption.
--
-- This isolates the known blocker:
-- `valueHasETyp.closure` gives only
--   `tenv.lookup y = some qt → env.lookup y = some v → valueHasETyp ...`
-- whereas runtime instantiation needs
--   `tenv.lookup y = some qt → ∃ v, env.lookup y = some v ∧ valueHasETyp ...`.
--
-- The missing ingredient is exactly `_hcover`: every typed captured binding is
-- actually present in the runtime captured environment.
private lemma runtimeInstantiatesCtx_closure_body_from_henv
  (ctx : TypeContext) (result2 : TypeResult) (x : Name) (tenv : CapturedVarEnv)
  (argQt : QTyp) (argVal : Value) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_hric : runtimeInstantiatesCtx (ctxAfter ctx result2) μ ρ θ)
  (_harg : valueHasETyp θ argVal argQt.etyp)
  (_henv : ∀ y qt v, (VarTypeEnv.ofCaptured tenv).lookup y = some qt →
    ρ.lookup y = some v → valueHasETyp θ v qt.etyp)
  (_hcover : ∀ y qt, (VarTypeEnv.ofCaptured tenv).lookup y = some qt → ∃ v, ρ.lookup y = some v) :
  let bodyVarEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x argQt
  let bodyCtx : TypeContext := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime', varEnv := bodyVarEnv }
  runtimeInstantiatesCtx bodyCtx μ (VarEnv.update ρ x argVal) θ := by
  apply runtimeInstantiatesCtx_closure_body
    (ctx := ctx) (result2 := result2) (x := x) (tenv := tenv)
    (argQt := argQt) (argVal := argVal) (μ := μ) (ρ := ρ) (θ := θ)
    _hric _harg
  intro y qt hlookup
  rcases _hcover y qt hlookup with ⟨v, hlookupρ⟩
  exact ⟨v, hlookupρ, _henv y qt v hlookup hlookupρ⟩

-- NOTE: old packed app helpers from the head-oriented approach were removed.
-- The app proof now keeps obligations inline and will use member-oriented join helpers.
-- (QTypRespectsTagMeaning_of_arrow_captured_lookup, wfTagMeaningCtx_ofCaptured_from_arrow,
--  and wfTagMeaningCtx_closure_body have been moved earlier in the file.)

-- Extract per-member evidence from closureCapturedVarsRegime for a closure value.
-- Given that the value is a closure with arrow type, the deepValueQTypProperty
-- must use the .closure constructor, yielding σcap with regime, typing, and recursive
-- evidence. This avoids the σcap matching problem between valueHasETyp.closure
-- and closureCapturedVarsRegime.
private lemma closureCapturedVarsRegime_closure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (h : closureCapturedVarsRegime predSat R qt μ θ (Value.closure x body env)) :
    ∃ σcap,
      FnTClosure.regular x body σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (y : Name) (qt_y : QTyp) (v_y : Value),
        σcap.lookup y = some qt_y →
        env.lookup y = some v_y →
        closureCapturedVarsRegime predSat R qt_y μ θ v_y) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure hnotclo _ =>
      exact absurd rfl (hnotclo x body env)
  | closure xp bp rp σ s1 s2 pp tcl hveq hteq hmem hP hrec =>
      rw [Value.closure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.arrow s1 s2 pp tcl = ETyp.arrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.arrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      exact ⟨σ, hmem, hP.1, hP.2, fun y qt_y v_y hy hv =>
        closureCapturedVarsRegime.intro (hrec y qt_y v_y hy hv)⟩
  | peClosure _ _ _ _ _ _ _ _ _ hveq _ _ _ _ _ =>
      exact absurd hveq (by simp)

private lemma closureCapturedVarsRegime_peClosure_extract
    {predSat : PredSat} {R : Regime} {qt : QTyp} {μ : Memory} {θ : RealizationMap}
    {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
    (h : closureCapturedVarsRegime predSat R qt μ θ (Value.peClosure x body env)) :
    ∃ σcap pbody,
      Expr.toPExpr? body = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      capturedVarsRegimeProperty predSat R μ σcap env ∧
      capturedVarsTypingProperty θ σcap env ∧
      (∀ (y : Name) (qt_y : QTyp) (v_y : Value),
        σcap.lookup y = some qt_y →
        env.lookup y = some v_y →
        closureCapturedVarsRegime predSat R qt_y μ θ v_y) := by
  rcases h with ⟨h_deep⟩
  cases h_deep with
  | nonClosure _ hnotpe =>
      exact absurd rfl (hnotpe x body env)
  | closure _ _ _ _ _ _ _ _ hveq _ _ _ _ =>
      exact absurd hveq (by simp)
  | peClosure xp bp pbody ρ σ s1 s2 pp tcl hveq hteq hpure hmem hP hrec =>
      rw [Value.peClosure.injEq] at hveq
      obtain ⟨rfl, rfl, rfl⟩ := hveq
      have htcl_eq : ETyp.parrow s1 s2 pp tcl = ETyp.parrow st1 st2 p tcls :=
        hteq.symm.trans hetyp
      rw [ETyp.parrow.injEq] at htcl_eq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := htcl_eq
      exact ⟨σ, pbody, hpure, hmem, hP.1, hP.2, fun y qt_y v_y hy hv =>
        closureCapturedVarsRegime.intro (hrec y qt_y v_y hy hv)⟩

private lemma join_transport_wfTagMeaningCtx
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
  -- Guard descriptors in joinMemEnvsStrong are a subset of the left side's:
  -- single-sided entries get noPred (no guard); both-sided entries preserve guardClosure
  -- only on exact match (same as left). So only first member's EnvRespectsTagMeaning is needed.
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
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr etyp) ++
                        toString " vs " ++ toString (repr resEtyp))
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              exact h_fold_tm rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') a
                hfold h_first_env


private lemma join_transport_consistentWithRegime
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_mem_guarded_from_first :
    ∀ l qt k,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypGuardTag qt = some k →
      (ctxAfter ctx res).regime.lookup? k ≠ none →
      (ctxAfter ctx first).memEnv.lookup l = some qt)
  (h_first : consistentWithRegime predSat (ctxAfter ctx first).regime (ctxAfter ctx first) μ ρ θ) :
  consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  simp only [consistentWithRegime, ctxAfter]
  constructor
  · intro l qt k hlookup hguard hR'def
    have hlookup_first := h_mem_guarded_from_first l qt k hlookup hguard hR'def
    have hRdef : first.regime'.lookup? k ≠ none := h_regime_mono.2.2 k hR'def
    cases hk' : res.regime'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        cases hk : first.regime'.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h_eq := h_regime_mono.2.1 k b' hk
            cases h_eq with
            | inl heq =>
                have hb : b' = b := Option.some.inj (heq.symm.trans hk')
                have h_locsR := h_first.1 l qt k hlookup_first hguard hRdef
                exact locsRegime_monotone h_regime_mono hguard (by rw [← hb]; exact hk) hk' h_locsR
            | inr h_none => simp [h_none] at hk'
  constructor
  · intro x qt k hlookup hguard hR'def
    have hRdef : first.regime'.lookup? k ≠ none := h_regime_mono.2.2 k hR'def
    cases hk' : res.regime'.lookup? k with
    | none => exact absurd hk' hR'def
    | some b =>
        cases hk : first.regime'.lookup? k with
        | none => exact absurd hk hRdef
        | some b' =>
            have h_eq := h_regime_mono.2.1 k b' hk
            cases h_eq with
            | inl heq =>
                have hb : b' = b := Option.some.inj (heq.symm.trans hk')
                have h_varsR := h_first.2.1 x qt k hlookup hguard hRdef
                exact varsRegime_monotone h_regime_mono hguard (by rw [← hb]; exact hk) hk' h_varsR
            | inr h_none => simp [h_none] at hk'
  · intro x qt v hlookup hlookup_v
    exact closureCapturedVarsRegime_monotone h_regime_mono
      (h_first.2.2 x qt v hlookup hlookup_v)

private lemma cleanUnder_of_monotone {R R' : Regime} {qt : QTyp} :
    Regime.monotoneStep R R' → qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro h_mono h_clean
  cases h_clean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hkR' hnotfun =>
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
              simp [hkR'_none] at hkR'

private lemma agreeValueUnder_clean_monotoneRegime
    {predSat : PredSat} {R R' : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
    Regime.monotoneStep R R' →
      qtypCleanUnder R' qt →
        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
          agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro h_mono hclean hagree
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

private lemma qtypCleanUnder_lookup_true_back
    {R R' : Regime}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    {qt : QTyp} :
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hk hnotfun =>
      exact qtypCleanUnder.guard k htag (hlookup_true_back k hk) hnotfun

private lemma agreeValueUnder_clean_transport_by_lookupTrueBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ σcap ρcap)
    (hmemberCvcr₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₁ θ₁ σcap ρcap) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
  have h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt := by
    intro qt' hclean'
    exact qtypCleanUnder_lookup_true_back hlookup_true_back hclean'
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      h_clean_back
      hmemberVars₀_transport hmemberCvcr₀_transport
      hmemberVars₁_transport hmemberCvcr₁_transport
      hclean hagree

private lemma agreeCapturedEnv_transport_by_lookupTrueBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ σcap ρcap)
    (hmemberCvcr₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₁ θ₁ σcap ρcap) :
    agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
      agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ := by
  intro hcap
  have h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt := by
    intro qt hclean
    exact qtypCleanUnder_lookup_true_back hlookup_true_back hclean
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₀ v₁ _ =>
      qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₀ ρcap₁ _ =>
      agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁
  have htransport : motive₂ σcap ρcap₀ ρcap₁ hcap :=
    agreeCapturedEnv.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref_nonarrow := by
        intro qt v₀ v₁ hpoison hnotfun hnotref heq _hclean
        exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq)
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap _hclean
        exact agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
          hv₀ hv₁)
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 _hclean
        exact agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2)
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₀ hv₁ ihcap _hclean
        exact agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch ihcap
          (hmemberVars₀_transport hmemberVars₀)
          (hmemberCvcr₀_transport hmemberCvcr₀)
          (hmemberVars₁_transport hmemberVars₁)
          (hmemberCvcr₁_transport hmemberCvcr₁)
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
          exact hdirty (h_clean_back qt hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      hcap
  exact htransport

private lemma join_transport_agreeOnClean
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_clean_res_to_first :
    ∀ qt,
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      qtypCleanUnder (ctxAfter ctx first).regime qt)
  (h_mem_clean_from_first :
    ∀ l qt,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      (ctxAfter ctx first).memEnv.lookup l = some qt)
  (h_first : agreeOnClean predSat (ctxAfter ctx first).regime (ctxAfter ctx first) μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
  agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  simp only [agreeOnClean, ctxAfter]
  constructor
  · intro l qt hlookup hclean
    have hlookup_first := h_mem_clean_from_first l qt hlookup hclean
    have hclean_first := h_clean_res_to_first qt hclean
    have hagree_first := h_first.1 l qt hlookup_first hclean_first
    cases hagree_first with
    | both_unrealized _ _ hnone₀ hnone₁ =>
        exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
    | agree_values _ _ a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
        have hagree' := agreeValueUnder_clean_monotoneRegime h_regime_mono hclean hagree
        exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree'
  · intro x qt hlookup hclean
    have hclean_first := h_clean_res_to_first qt hclean
    have hagree_first := h_first.2 x qt hlookup hclean_first
    cases hagree_first with
    | both_none _ _ hnone₀ hnone₁ =>
        exact agreeVarUnder.both_none x qt hnone₀ hnone₁
    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
        have hagree' := agreeValueUnder_clean_monotoneRegime h_regime_mono hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'

private lemma join_transport_agreeOnClean_from_member
  (predSat : PredSat) (ctx : TypeContext)
  (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src :
    agreeOnClean predSat (ctxAfter ctx src).regime (ctxAfter ctx src)
      μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
  (h_clean_res_to_src :
    ∀ qt,
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      qtypCleanUnder (ctxAfter ctx src).regime qt)
  (h_mem_from_src_or_unrealized :
    ∀ l qt,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      ((∃ qt_src,
          (ctxAfter ctx src).memEnv.lookup l = some qt_src ∧
          qtypCleanUnder (ctxAfter ctx src).regime qt_src ∧
          qt.etyp = qt_src.etyp ∧
          (qt.poison = false → qt_src.poison = false)) ∨
        (θ₀.lookup l = none ∧ θ₁.lookup l = none)))
  (hmemberVars₀_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberVarsRegimeEvidence predSat src.regime' μ₀ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₀ σcap ρcap)
  (hmemberCvcr₀_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberCvcrEvidence predSat src.regime' μ₀ θ₀ σcap ρcap →
        MemberCvcrEvidence predSat res.regime' μ₀ θ₀ σcap ρcap)
  (hmemberVars₁_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberVarsRegimeEvidence predSat src.regime' μ₁ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₁ σcap ρcap)
  (hmemberCvcr₁_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberCvcrEvidence predSat src.regime' μ₁ θ₁ σcap ρcap →
        MemberCvcrEvidence predSat res.regime' μ₁ θ₁ σcap ρcap) :
  agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
    μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  simp only [agreeOnClean, ctxAfter]
  have hlookup_true_back :
      ∀ (k : Tag),
        (ctxAfter ctx res).regime.lookup? k = some true →
        (ctxAfter ctx src).regime.lookup? k = some true := by
    intro k hk
    let qtWitness : QTyp := ⟨ETyp.int, true, Predicate.guardOnly k⟩
    have hclean_res_witness :
        qtypCleanUnder (ctxAfter ctx res).regime qtWitness :=
      qtypCleanUnder.guard k (by simp [qtWitness, qtypGuardTag]) hk
        (by simp [qtWitness, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    have hclean_src_witness :
        qtypCleanUnder (ctxAfter ctx src).regime qtWitness :=
      h_clean_res_to_src qtWitness hclean_res_witness
    cases hclean_src_witness with
    | clean hpoison =>
        simp [qtWitness] at hpoison
    | guard k' htag_src hk_src _ =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qtWitness := by symm; exact htag_src
              _ = some k := by simp [qtWitness, qtypGuardTag]
          exact Option.some.inj this
        simpa [hk_eq] using hk_src
  constructor
  · intro l qt hlookup hclean
    rcases h_mem_from_src_or_unrealized l qt hlookup hclean with hlookup_src | hunrealized
    · rcases hlookup_src with ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
      have hloc_agree_src := h_src.1 l qt_src hlookup_src hclean_src
      cases hloc_agree_src with
      | both_unrealized _ _ hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values _ _ a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
          have hagree_src_qt :
              agreeValueUnder predSat src.regime' μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_transport_clean
              (predSat := predSat)
              (R := src.regime')
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              (qt := qt) (qt2 := qt_src)
              (o₀ := Value.num n₀) (o₁ := Value.num n₁)
              (h_clean_res_to_src qt hclean) hetyp_eq hpoison_imp hagree
          have hagree' :
              agreeValueUnder predSat res.regime' μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_clean_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := src.regime') (R' := res.regime')
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              (qt := qt) (v₀ := Value.num n₀) (v₁ := Value.num n₁)
              hlookup_true_back
              hmemberVars₀_transport hmemberCvcr₀_transport
              hmemberVars₁_transport hmemberCvcr₁_transport
              hclean hagree_src_qt
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree'
    · exact agreeLocUnder.both_unrealized l qt hunrealized.1 hunrealized.2
  · intro x qt hlookup hclean
    have hclean_src : qtypCleanUnder src.regime' qt :=
      h_clean_res_to_src qt hclean
    have hagree_src := h_src.2 x qt hlookup hclean_src
    cases hagree_src with
    | both_none _ _ hnone₀ hnone₁ =>
        exact agreeVarUnder.both_none x qt hnone₀ hnone₁
    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
        have hagree' :
            agreeValueUnder predSat res.regime' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
          agreeValueUnder_clean_transport_by_lookupTrueBack
            (predSat := predSat)
            (R := src.regime') (R' := res.regime')
            (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
            (qt := qt) (v₀ := v₀) (v₁ := v₁)
            hlookup_true_back
            hmemberVars₀_transport hmemberCvcr₀_transport
            hmemberVars₁_transport hmemberCvcr₁_transport
            hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'


private lemma join_transport_resultAgreesIfClean
  (predSat : PredSat) (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (qt : QTyp) (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_regime_mono : Regime.monotoneStep first.regime' res.regime')
  (h_clean_res_to_first :
    qtypCleanUnder (ctxAfter ctx res).regime qt →
    qtypCleanUnder (ctxAfter ctx first).regime qt)
  (h_first : resultAgreesIfClean predSat (ctxAfter ctx first).regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁) :
  resultAgreesIfClean predSat (ctxAfter ctx res).regime μ₀ μ₁ θ₀ θ₁ qt o₀ o₁ := by
  intro hclean_res
  have hclean_first := h_clean_res_to_first hclean_res
  have hagree_first := h_first hclean_first
  exact agreeValueUnder_clean_monotoneRegime h_regime_mono hclean_res hagree_first

-- Single-step: transport closureCapturedVarsRegime from the RIGHT argument of joinETyps.
private lemma closureCapturedVarsRegime_joinETyps_step_right
  (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegime predSat R ⟨resEtyp, resPoison, resPred⟩ μ θ v) :
  closureCapturedVarsRegime predSat R ⟨joinETyps etyp1 resEtyp p1 resPoison,
    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases hcap with
  | intro hdeep =>
      cases hdeep with
      | nonClosure hv hpe =>
          exact .intro (.nonClosure hv hpe)
      | closure x body ρcap σcap st1r st2r pr tclr hval hetyp_r htcl hP hrec =>
          have hetyp_r' : resEtyp = ETyp.arrow st1r st2r pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.closure x body ρcap σcap st1l st2l pr tclr
                    hval rfl htcl hP hrec))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.arrow st1l st2l (joinPoison pl pr) (mergeFnTClosures tclsl tclr),
                      resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_fnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := st2l) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergeFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergeFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.arrow st1l st2l pl tclsl) (ETyp.arrow st1l st2l pr tclr)
                    p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join
          | parrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
      | peClosure x body pbody ρcap σcap st1r st2r pr tclr hval hetyp_r hpure htcl hP hrec =>
          have hetyp_r' : resEtyp = ETyp.parrow st1r st2r pr tclr := by
            simpa using hetyp_r
          subst resEtyp
          cases etyp1 with
          | int =>
              exfalso
              simp [beqETypSignature] at hcompat
          | bool =>
              exfalso
              simp [beqETypSignature] at hcompat
          | unit =>
              exfalso
              simp [beqETypSignature] at hcompat
          | string =>
              exfalso
              simp [beqETypSignature] at hcompat
          | ref ls =>
              exfalso
              simp [beqETypSignature] at hcompat
          | arrow st1l st2l pl tclsl =>
              exfalso
              simp [beqETypSignature] at hcompat
          | parrow st1l st2l pl tclsl =>
              simp [beqETypSignature] at hcompat
              obtain ⟨rfl, rfl⟩ := hcompat
              have hcap_src :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
                simpa using (closureCapturedVarsRegime.intro
                  (deepValueQTypProperty.peClosure x body pbody ρcap σcap st1l st2l pr tclr
                    hval rfl hpure htcl hP hrec))
              have hcap_join :
                  closureCapturedVarsRegime predSat R
                    ⟨ETyp.parrow st1l st2l (joinPoison pl pr) (mergePFnTClosures tclsl tclr),
                      resPoison, resPred⟩ μ θ v :=
                closureCapturedVarsRegime_weaken_pFnTClosures'
                  (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
                  (st1 := st1l) (st2 := st2l) (p := pr)
                  (p' := joinPoison pl pr) (tcls := tclr)
                  (tcls' := mergePFnTClosures tclsl tclr)
                  (poison := resPoison) (pred := resPred)
                  (fun tcl hmem => mem_mergePFnTClosures_right tclsl tclr tcl hmem)
                  hcap_src
              exact closureCapturedVarsRegime_transport_etyp (qt := _)
                (qt' := ⟨joinETyps (ETyp.parrow st1l st2l pl tclsl) (ETyp.parrow st1l st2l pr tclr)
                    p1 resPoison,
                    joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
                (by simp [joinETyps]) hcap_join

-- Member-oriented transport for closureCapturedVarsRegime across joinTypeResults.
private lemma joinTypeResults_closure_cvcr_transport_from_member
  (predSat : PredSat) (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult)
  (res : TypeResult) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (hcap_src : closureCapturedVarsRegime predSat R src.qualType μ θ v) :
  closureCapturedVarsRegime predSat R res.qualType μ θ v := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        closureCapturedVarsRegime predSat R ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' hcompat hfold hcap_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        simpa using hcap_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcap_acc1 :
                closureCapturedVarsRegime predSat R ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
              have hstep :=
                closureCapturedVarsRegime_joinETyps_step
                  predSat R μ θ v acc.1 resEtyp acc.2.2.1 resPoison acc.2.2.2.1 resPred
                  hcompat_x hcap_acc
              simpa [acc1] using hstep
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            exact ih (acc := acc1) hcompat_tail hfold_tail hcap_acc1
  have h_fold_member_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        closureCapturedVarsRegime predSat R src'.qualType μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hcap_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hcap_acc1 :
                  closureCapturedVarsRegime predSat R
                    ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
                have hstep :=
                  closureCapturedVarsRegime_joinETyps_step_right
                    predSat R μ θ v acc.1 resEtyp acc.2.2.1 resPoison acc.2.2.2.1 resPred
                    hcompat_x (by simpa [hqx] using hcap_src')
                simpa [acc1] using hstep
              exact h_fold_left_cvcr xs acc1 acc' hcompat_tail hfold_tail hcap_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src')
                hcompat_tail hfold_tail hsrc_tail hcap_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at _h_join
          contradiction
      | ok _ =>
          erw [hcheck] at _h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at _h_join
              contradiction
          | ok a =>
              erw [hfold] at _h_join
              have heq := Except.ok.inj _h_join
              have hetyp_res : (⟨a.1, a.2.2.1, a.2.2.2.1⟩ : QTyp).etyp = res.qualType.etyp := by
                exact congrArg (fun tr => tr.qualType.etyp) heq
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hcap_a :
                    closureCapturedVarsRegime predSat R ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_left_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a hcompat hfold (by simpa [hqt] using hcap_src)
                exact closureCapturedVarsRegime_transport_etyp hetyp_res hcap_a
              · have hcap_a :
                    closureCapturedVarsRegime predSat R ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_member_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a src hcompat hfold hsrc_tail hcap_src
                exact closureCapturedVarsRegime_transport_etyp hetyp_res hcap_a

-- If the joined result predicate is a guardClosure, every contributing member keeps that exact predicate.
private lemma joinTypeResults_pred_eq_guardClosure_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hmem_src : src ∈ first :: rest)
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv}
  (hpred_res : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  src.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_pred :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
        acc.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' hfold hpred_out
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hpred_out
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
            have hpred_acc1 : acc1.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
              ih (acc := acc1) hfold_tail
            have hjoin :
                joinPredicates acc.2.2.2.1 resPred = Predicate.guardClosure k arg_name pred_body var_env := by
              simpa [acc1] using hpred_acc1
            exact (joinPredicates_eq_guardClosure (p := acc.2.2.2.1) (q := resPred) hjoin).1
  have h_fold_member_pred :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
        src'.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' src' hfold hmem_src' hpred_out
    induction rs' generalizing acc acc' src' with
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
            have hpred_acc1 : acc1.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
              h_fold_left_pred xs acc1 acc' hfold_tail hpred_out
            have hjoin :
                joinPredicates acc.2.2.2.1 resPred = Predicate.guardClosure k arg_name pred_body var_env := by
              simpa [acc1] using hpred_acc1
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              simpa [hqx] using
                (joinPredicates_eq_guardClosure (p := acc.2.2.2.1) (q := resPred) hjoin).2
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail hpred_out
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at h_join
          contradiction
      | ok _ =>
          erw [hcheck] at h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at h_join
              contradiction
          | ok a =>
              erw [hfold] at h_join
              have heq := Except.ok.inj h_join
              have hpred_match :
                  (match a.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => a.2.2.2.1) =
                    Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  (match a.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => a.2.2.2.1)
                      = res.qualType.pred := by
                        exact congrArg (fun tr => tr.qualType.pred) heq
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_res
              have hpred_a : a.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                cases ha1 : a.1 <;> simp [ha1] at hpred_match <;> exact hpred_match
              rcases (List.mem_cons.mp hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hpred_first :
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag').2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
                  h_fold_left_pred
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold hpred_a
                simpa [hqt] using hpred_first
              · exact h_fold_member_pred
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a src hfold hsrc_tail hpred_a

-- App-closure normalization transport stubs (`result3` -> `firstShared`).
private lemma valueConsistentWithRegime_transport_normalizeAppResultByProvenance
  (predSat : PredSat) (R : Regime) (p p1 : Poison) (qt : QTyp)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (h : valueConsistentWithRegime predSat R qt μ θ v) :
  valueConsistentWithRegime predSat R
    (normalizeAppResultByProvenance (joinPoison p1 p)
      { qt with poison := joinPoison p1 (joinPoison p qt.poison) }) μ θ v := by
  unfold normalizeAppResultByProvenance
  split
  · -- joinPoison p1 p = true: result has pred := noPred, etyp unchanged
    have hcap_src : closureCapturedVarsRegime predSat R qt μ θ v := by
      cases h with
      | noTag _ hcap => exact hcap
      | guardOnly_ok _ _ hcap => exact hcap
      | notInRegime _ _ _ hcap => exact hcap
      | inRegimeTrue _ _ _ _ hcap => exact hcap
      | inRegimeFalse _ _ _ _ hcap => exact hcap
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag])
      (closureCapturedVarsRegime_transport_etyp (by simp) hcap_src)
  · rename_i hp1p_false
    have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
    have hand : p1 = false ∧ p = false := (Bool.or_eq_false_iff).mp (by simpa [joinPoison] using hp1p)
    rw [hand.1, hand.2]
    simp only [joinPoison, Bool.false_or]
    set qt' : QTyp := { qt with poison := joinPoison false qt.poison } with hqt'_def
    have hpred_eq : qt.pred = qt'.pred := rfl
    cases h with
    | noTag htag hcap =>
        exact valueConsistentWithRegime.noTag
          (show qtypGuardTag qt' = none by simp [qtypGuardTag, hqt'_def]; exact htag)
          (closureCapturedVarsRegime_transport_pred hpred_eq hcap)
    | guardOnly_ok k hgo hcap =>
        exact valueConsistentWithRegime.guardOnly_ok k
          (show qt'.pred = Predicate.guardOnly k from hgo)
          (closureCapturedVarsRegime_transport_pred hpred_eq hcap)
    | notInRegime k htag hlookup hcap =>
        exact valueConsistentWithRegime.notInRegime k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (closureCapturedVarsRegime_transport_pred hpred_eq hcap)
    | inRegimeTrue k htag hlookup hpred hcap =>
        exact valueConsistentWithRegime.inRegimeTrue k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (qtypPredHolds_transport_pred (qt := qt) (qt' := qt')
            (show qt.pred = qt'.pred from rfl) hpred)
          (closureCapturedVarsRegime_transport_pred hpred_eq hcap)
    | inRegimeFalse k htag hlookup hnpred hcap =>
        exact valueConsistentWithRegime.inRegimeFalse k
          (show qtypGuardTag qt' = some k by simp [qtypGuardTag, hqt'_def]; exact htag) hlookup
          (fun habs => hnpred (qtypPredHolds_transport_pred (qt := qt') (qt' := qt)
            (show qt'.pred = qt.pred from rfl) habs))
          (closureCapturedVarsRegime_transport_pred hpred_eq hcap)

private lemma resultAgreesIfClean_transport_normalizeAppResultByProvenance
  (predSat : PredSat) (R : Regime) (p p1 : Poison) (qt : QTyp)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (h : resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁) :
  resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁
    (normalizeAppResultByProvenance (joinPoison p1 p)
      { qt with poison := joinPoison p1 (joinPoison p qt.poison) }) o₀ o₁ := by
  intro hclean_norm
  unfold normalizeAppResultByProvenance at hclean_norm
  split at hclean_norm
  · exfalso
    cases hclean_norm with
    | clean hpoison => simp at hpoison
    | guard k htag => simp [qtypGuardTag] at htag
  · rename_i hp1p_false
    have hp1p : joinPoison p1 p = false := by simpa using hp1p_false
    obtain ⟨hp1, hp⟩ := Bool.or_eq_false_iff.mp (by simpa [joinPoison] using hp1p)
    subst hp1; subst hp
    simp only [joinPoison, Bool.false_or] at hclean_norm
    have hclean_qt : qtypCleanUnder R qt := by
      convert hclean_norm using 1; cases qt; rfl
    have hagree := h hclean_qt
    unfold normalizeAppResultByProvenance
    simp [joinPoison]
    convert hagree using 1
    cases qt; rfl

-- Join-compatibility helpers for transporting clean location agreement from the
-- join result back to the head seed `first` in app-closure proofs.
private lemma joinTypeResults_lookup_head_etyp_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first) :
  qt.etyp = qt_first.etyp := by
  have hres_int : qt.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx res).memEnv) l qt hlookup_res
  have hfirst_int : qt_first.etyp = ETyp.int :=
    memEnv_lookup_etyp_int (env := (ctxAfter ctx first).memEnv) l qt_first hlookup_first
  calc
    qt.etyp = ETyp.int := hres_int
    _ = qt_first.etyp := hfirst_int.symm

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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a qt_first
                  hfold hlookup_first' hlookup_res' hpoison_res

private lemma joinTypeResults_lookup_head_clean_compat
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (l : Loc) (qt qt_first : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime qt)
  (hlookup_first : (ctxAfter ctx first).memEnv.lookup l = some qt_first) :
  qtypCleanUnder (ctxAfter ctx first).regime qt_first := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_lookup_head_poison_imp
          (ctx := ctx) (first := first) (rest := rest) (res := res)
          _h_join l qt qt_first hlookup_res hlookup_first hpoison)
  | guard k htag hreg hnotfun =>
      have htag_first : qtypGuardTag qt_first = some k :=
        joinTypeResults_lookup_head_guardTag_compat
          (ctx := ctx) (first := first) (rest := rest) (res := res)
          _h_join l qt qt_first k hlookup_res hlookup_first htag
      have hreg_first : (ctxAfter ctx first).regime.lookup? k = some true :=
        joinTypeResults_lookup_head_regime_compat
          (ctx := ctx) (first := first) (rest := rest) (res := res)
          _h_join k true hreg
      have hetyp_eq : qt.etyp = qt_first.etyp :=
        joinTypeResults_lookup_head_etyp_compat
          (ctx := ctx) (first := first) (rest := rest) (res := res)
          _h_join l qt qt_first hlookup_res hlookup_first
      have hnotfun_first : qt_first.etyp.isFunctionType = false := by
        simpa [hetyp_eq.symm] using hnotfun
      exact qtypCleanUnder.guard k htag_first hreg_first hnotfun_first

-- Member-oriented companions for `joinTypeResults` lookup compatibility.
-- These are the target interface for `stepFR_app`; proofs are staged and can be
-- completed incrementally after wiring.
private lemma joinTypeResults_lookup_member_regime_compat
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
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
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold hlookup_res'
                have hsrc_lookup : src.regime'.lookup? k = some b := hpack.2 src hsrc_rest
                simpa [ctxAfter] using hsrc_lookup

private lemma joinTypeResults_transport_valueConsistentWithRegime_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : valueConsistentWithRegime predSat (ctxAfter ctx src).regime src.qualType μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  have hcap_src :
      closureCapturedVarsRegime predSat (ctxAfter ctx src).regime src.qualType μ θ v :=
    valueConsistentWithRegime_closureCapturedVarsRegime h_src
  have hcap_src_resR :
      closureCapturedVarsRegime predSat (ctxAfter ctx res).regime src.qualType μ θ v :=
    closureCapturedVarsRegime_transport_lookup_back
      (predSat := predSat)
      (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
      (qt := src.qualType) (μ := μ) (θ := θ) (v := v)
      hlookup_back hcap_src
  have hcap_res :
      closureCapturedVarsRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v :=
    joinTypeResults_closure_cvcr_transport_from_member
      (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (R := (ctxAfter ctx res).regime) (μ := μ) (θ := θ) (v := v)
      _h_join _hmem_src hcap_src_resR
  cases hpred_res : res.qualType.pred with
  | noPred =>
      exact valueConsistentWithRegime.noTag
        (show qtypGuardTag res.qualType = none by simp [qtypGuardTag, hpred_res])
        hcap_res
  | guardOnly k =>
      exact valueConsistentWithRegime.guardOnly_ok k hpred_res hcap_res
  | guardClosure k arg_name pred_body var_env =>
      have hpred_src :
          src.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env :=
        joinTypeResults_pred_eq_guardClosure_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src hpred_res
      have hpred_eq : src.qualType.pred = res.qualType.pred := by
        simpa [hpred_res] using hpred_src
      have htag_res : qtypGuardTag res.qualType = some k := by
        simp [qtypGuardTag, hpred_res]
      cases hlookupR : (ctxAfter ctx res).regime.lookup? k with
      | none =>
          exact valueConsistentWithRegime.notInRegime k htag_res hlookupR hcap_res
      | some b =>
          have hlookup_src :
              (ctxAfter ctx src).regime.lookup? k = some b := hlookup_back k b hlookupR
          have hcons_src :
              (b = true → qtypPredHolds predSat src.qualType μ v) ∧
              (b = false → ¬ qtypPredHolds predSat src.qualType μ v) :=
            valueConsistentWithRegime_guardClosure_consistency
              (predSat := predSat) (R := (ctxAfter ctx src).regime)
              (qt := src.qualType) (μ := μ) (v := v)
              (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
              (b := b) h_src hpred_src hlookup_src
          cases b with
          | false =>
              have hnot_src : ¬ qtypPredHolds predSat src.qualType μ v := hcons_src.2 rfl
              have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                qtypPredHolds_transport_pred_not
                  (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                  (μ := μ) (v := v) hpred_eq hnot_src
              exact valueConsistentWithRegime.inRegimeFalse k htag_res hlookupR hnot_res hcap_res
          | true =>
              have hholds_src : qtypPredHolds predSat src.qualType μ v := hcons_src.1 rfl
              have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                qtypPredHolds_transport_pred
                  (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                  (μ := μ) (v := v) hpred_eq hholds_src
              exact valueConsistentWithRegime.inRegimeTrue k htag_res hlookupR hholds_res hcap_res

private lemma etyp_isFunctionType_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isFunctionType = t2.isFunctionType := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hsig ⊢

private lemma etyp_isArrow_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isArrow = t2.isArrow := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isArrow] at hsig ⊢

private lemma etyp_isParrow_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isParrow = t2.isParrow := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isParrow] at hsig ⊢

private lemma etyp_not_ref_left_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true)
  (hnotref_right : ¬ ∃ ls, t2 = ETyp.ref ls) :
  ¬ ∃ ls, t1 = ETyp.ref ls := by
  intro href_left
  rcases href_left with ⟨ls, ht1⟩
  subst ht1
  cases t2 <;> simp [beqETypSignature] at hsig
  case ref ls2 =>
    exact hnotref_right ⟨ls2, rfl⟩

private lemma joinTypeResults_qualType_etyp_signature_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest) :
  beqETypSignature res.qualType.etyp src.qualType.etyp = true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_sig_invariant :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ t, beqETypSignature acc.1 t = beqETypSignature acc'.1 t := by
    intro rs' acc acc' hcompat hfold
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        intro t
        rfl
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hinv_tail := ih (acc := acc1) hcompat_tail hfold_tail
            intro t
            calc
              beqETypSignature acc.1 t = beqETypSignature acc1.1 t := by
                simpa [acc1] using
                  (beqETypSignature_joinETyps_left
                    (t1 := acc.1) (t2 := resEtyp) (t3 := t)
                    (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x)
              _ = beqETypSignature acc'.1 t := hinv_tail t
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              have hinv :=
                h_fold_sig_invariant
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a hcompat hfold
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hself : beqETypSignature etyp etyp = true :=
                  beqETypSignature_refl etyp
                have : beqETypSignature a.1 etyp = true := by
                  have hinv' := hinv etyp
                  simpa [hself] using hinv'.symm
                simpa [ctxAfter, hqt] using this
              · have hsrc_compat : beqETypSignature etyp src.qualType.etyp = true := hcompat src hsrc_rest
                have : beqETypSignature a.1 src.qualType.etyp = true := by
                  have hinv' := hinv src.qualType.etyp
                  simpa [hsrc_compat] using hinv'.symm
                simpa [ctxAfter] using this

private lemma joinTypeResults_qualType_poison_imp_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest) :
  res.qualType.poison = false → src.qualType.poison = false := by
  intro hpoison_res
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_poison :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.1 = false →
        acc.2.2.1 = false := by
    intro rs' acc acc' hfold hpoison_out
    induction rs' generalizing acc acc' with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hpoison_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hpoison_acc1 : acc1.2.2.1 = false :=
              ih (acc := acc1) (acc' := acc') hfold_tail hpoison_out
            have : joinPoison acc.2.2.1 resPoison = false := by
              simpa [acc1] using hpoison_acc1
            exact (joinPoison_eq_false this).1
  have h_fold_member_poison :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.2.1 = false →
        src'.qualType.poison = false := by
    intro rs' acc acc' src' hfold hmem_src' hpoison_out
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hpoison_acc1 : acc1.2.2.1 = false :=
                h_fold_left_poison xs acc1 acc' hfold_tail hpoison_out
              have : joinPoison acc.2.2.1 resPoison = false := by
                simpa [acc1] using hpoison_acc1
              have hresPoison : resPoison = false := (joinPoison_eq_false this).2
              simpa [hqx] using hresPoison
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail hpoison_out
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hpoison_match :
                  joinPoison ctx.pc a.2.2.1 = false := by
                simpa using hpoison_res
              have hpoison_a : a.2.2.1 = false := (joinPoison_eq_false hpoison_match).2
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hfirst_poison : poison = false :=
                  h_fold_left_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold hpoison_a
                simpa [hqt] using hfirst_poison
              · exact
                  h_fold_member_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hfold hsrc_rest hpoison_a

private lemma joinTypeResults_qualType_guardTag_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {k : Tag}
  (htag_res : qtypGuardTag res.qualType = some k) :
  qtypGuardTag src.qualType = some k := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_guardTag :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        predGuardTag acc'.2.2.2.1 = some k →
        predGuardTag acc.2.2.2.1 = some k := by
    intro rs' acc acc' hfold htag_out
    induction rs' generalizing acc acc' with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact htag_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have htag_acc1 : predGuardTag acc1.2.2.2.1 = some k :=
              ih (acc := acc1) (acc' := acc') hfold_tail htag_out
            have hjoin : predGuardTag (joinPredicates acc.2.2.2.1 resPred) = some k := by
              simpa [acc1] using htag_acc1
            exact (predGuardTag_joinPredicates (p := acc.2.2.2.1) (q := resPred) (k := k) hjoin).1
  have h_fold_member_guardTag :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        predGuardTag acc'.2.2.2.1 = some k →
        qtypGuardTag src'.qualType = some k := by
    intro rs' acc acc' src' hfold hmem_src' htag_out
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have htag_acc1 : predGuardTag acc1.2.2.2.1 = some k :=
              h_fold_left_guardTag xs acc1 acc' hfold_tail htag_out
            have hjoin : predGuardTag (joinPredicates acc.2.2.2.1 resPred) = some k := by
              simpa [acc1] using htag_acc1
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have htag_resPred : predGuardTag resPred = some k :=
                (predGuardTag_joinPredicates (p := acc.2.2.2.1) (q := resPred) (k := k) hjoin).2
              simpa [hqx, qtypGuardTag, predGuardTag] using htag_resPred
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail htag_out
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have htag_match :
                  predGuardTag
                    (match a.1 with
                    | ETyp.arrow _ _ _ _ => Predicate.noPred
                    | ETyp.parrow _ _ _ _ => Predicate.noPred
                    | _ => a.2.2.2.1) = some k := by
                simpa [qtypGuardTag, predGuardTag] using htag_res
              have htag_a : predGuardTag a.2.2.2.1 = some k := by
                cases ha1 : a.1 <;> simp [ha1, predGuardTag] at htag_match <;> exact htag_match
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have htag_first :
                    predGuardTag pred = some k :=
                  h_fold_left_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold htag_a
                simpa [hqt, qtypGuardTag, predGuardTag] using htag_first
              · exact
                  h_fold_member_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hfold hsrc_rest htag_a

private lemma joinTypeResults_qualType_clean_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime res.qualType) :
  qtypCleanUnder (ctxAfter ctx src).regime src.qualType := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_qualType_poison_imp_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src hpoison)
  | guard k htag hreg hnotfun =>
      have htag_src :
          qtypGuardTag src.qualType = some k :=
        joinTypeResults_qualType_guardTag_compat_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src htag
      have hreg_src :
          (ctxAfter ctx src).regime.lookup? k = some true :=
        joinTypeResults_lookup_member_regime_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src k true hreg
      have hsig :
          beqETypSignature res.qualType.etyp src.qualType.etyp = true :=
        joinTypeResults_qualType_etyp_signature_compat_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src
      have hfunEq :
          res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType :=
        etyp_isFunctionType_eq_of_beqSignature_true hsig
      have hnotfun_src : src.qualType.etyp.isFunctionType = false := by
        calc
          src.qualType.etyp.isFunctionType = res.qualType.etyp.isFunctionType := by
            simpa using hfunEq.symm
          _ = false := hnotfun
      exact qtypCleanUnder.guard k htag_src hreg_src hnotfun_src

private lemma joinETyps_preserves_dirty_arrow_right
    {t1 : ETyp} {st1 st2 : Typ} {tcls2 : List FnTClosure}
    {p1 p1' p2' : Poison}
    (hcompat : beqETypSignature t1 (ETyp.arrow st1 st2 p1 tcls2) = true)
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps t1 (ETyp.arrow st1 st2 p1 tcls2) p1' p2') = some true := by
  subst hDirty
  cases t1 with
  | arrow st1' st2' pL tclsL =>
      simp only [beqETypSignature] at hcompat
      have hshape : (st1' == st1 && st2' == st2) = true := hcompat
      simp [joinETyps, hshape, getInternalPoison, joinPoison]
  | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
      simp [beqETypSignature] at hcompat

private lemma joinETyps_preserves_dirty_parrow_right
    {t1 : ETyp} {st1 st2 : Typ} {tcls2 : List PFnTClosure}
    {p1 p1' p2' : Poison}
    (hcompat : beqETypSignature t1 (ETyp.parrow st1 st2 p1 tcls2) = true)
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps t1 (ETyp.parrow st1 st2 p1 tcls2) p1' p2') = some true := by
  subst hDirty
  cases t1 with
  | parrow st1' st2' pL tclsL =>
      simp only [beqETypSignature] at hcompat
      have hshape : (st1' == st1 && st2' == st2) = true := hcompat
      simp [joinETyps, hshape, getInternalPoison, joinPoison]
  | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
      simp [beqETypSignature] at hcompat

private lemma joinTypeResults_qualType_getInternalPoison_true_from_member_arrow
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {tcls : List FnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.arrow st1 st2 true tcls) :
  getInternalPoison res.qualType.etyp = some true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.1.isArrow = true →
        getInternalPoison acc.1 = some true →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' hcompat hfold hisArrow_acc hdirty_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hdirty_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hsig_acc1_acc : beqETypSignature acc1.1 acc.1 = true := by
              have htmp :
                  beqETypSignature acc.1 acc.1 =
                    beqETypSignature (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) acc.1 :=
                beqETypSignature_joinETyps_left
                  (t1 := acc.1) (t2 := resEtyp) (t3 := acc.1)
                  (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x
              have hself : beqETypSignature acc.1 acc.1 = true := beqETypSignature_refl acc.1
              simpa [acc1, hself] using htmp
            have hisArrow_acc1 : acc1.1.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hsig_acc1_acc
              calc
                acc1.1.isArrow = acc.1.isArrow := by simpa using hEq
                _ = true := hisArrow_acc
            have hdirty_acc1 : getInternalPoison acc1.1 = some true := by
              cases hacc : acc.1 with
              | arrow st1' st2' p' tcls' =>
                  have hptrue : p' = true := by
                    simpa [hacc, getInternalPoison] using hdirty_acc
                  have hdirty' :
                      getInternalPoison
                        (joinETyps (ETyp.arrow st1' st2' p' tcls') resEtyp acc.2.2.1 resPoison) = some true :=
                    joinETyps_preserves_dirty_arrow
                      (st1 := st1') (st2 := st2') (p1 := p') (tcls1 := tcls')
                      (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison) hptrue
                  simpa [acc1, hacc] using hdirty'
              | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                  simp [ETyp.isArrow, hacc] at hisArrow_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hisArrow_acc1 hdirty_acc1
  have h_fold_member_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.arrow st1 st2 true tcls →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hetyp_resEtyp : resEtyp = ETyp.arrow st1 st2 true tcls := by
                simpa [hqx] using hetyp_src'
              have hdirty_acc1 :
                  getInternalPoison acc1.1 = some true := by
                have hdirty' :
                    getInternalPoison (joinETyps acc.1 (ETyp.arrow st1 st2 true tcls) acc.2.2.1 resPoison) = some true :=
                  joinETyps_preserves_dirty_arrow_right
                    (t1 := acc.1) (st1 := st1) (st2 := st2) (tcls2 := tcls)
                    (p1 := true) (p1' := acc.2.2.1) (p2' := resPoison)
                    (by simpa [hetyp_resEtyp] using hcompat_x) rfl
                simpa [acc1, hqx, hetyp_resEtyp] using hdirty'
              exact h_fold_left_dirty xs acc1 acc' hcompat_tail hfold_tail
                (by
                  have hsig_acc1_src : beqETypSignature acc1.1 (ETyp.arrow st1 st2 true tcls) = true := by
                    have htmp :
                        beqETypSignature acc.1 (ETyp.arrow st1 st2 true tcls) =
                          beqETypSignature
                            (joinETyps acc.1 (ETyp.arrow st1 st2 true tcls) acc.2.2.1 resPoison)
                            (ETyp.arrow st1 st2 true tcls) :=
                      beqETypSignature_joinETyps_left
                        (t1 := acc.1) (t2 := ETyp.arrow st1 st2 true tcls)
                        (t3 := ETyp.arrow st1 st2 true tcls)
                        (p1 := acc.2.2.1) (p2 := resPoison)
                        (by simpa [hetyp_resEtyp] using hcompat_x)
                    have hlhs : beqETypSignature acc.1 (ETyp.arrow st1 st2 true tcls) = true := by
                      simpa [hetyp_resEtyp] using hcompat_x
                    simpa [hqx, hetyp_resEtyp, acc1, hlhs] using htmp
                  have hEq := etyp_isArrow_eq_of_beqSignature_true hsig_acc1_src
                  simpa [ETyp.isArrow] using hEq)
                hdirty_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hetyp_first : etyp = ETyp.arrow st1 st2 true tcls := by
                  simpa [hqt] using hetyp_src
                have hisArrow_first : etyp.isArrow = true := by
                  simp [hetyp_first, ETyp.isArrow]
                have hdirty_first : getInternalPoison etyp = some true := by
                  simp [hetyp_first, getInternalPoison]
                exact
                  h_fold_left_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold hisArrow_first hdirty_first
              · exact
                  h_fold_member_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    (by simpa [ctxAfter] using hetyp_src)

private lemma joinTypeResults_qualType_getInternalPoison_true_from_member_parrow
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {tcls : List PFnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.parrow st1 st2 true tcls) :
  getInternalPoison res.qualType.etyp = some true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.1.isParrow = true →
        getInternalPoison acc.1 = some true →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' hcompat hfold hisParrow_acc hdirty_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hdirty_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hsig_acc1_acc : beqETypSignature acc1.1 acc.1 = true := by
              have htmp :
                  beqETypSignature acc.1 acc.1 =
                    beqETypSignature (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) acc.1 :=
                beqETypSignature_joinETyps_left
                  (t1 := acc.1) (t2 := resEtyp) (t3 := acc.1)
                  (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x
              have hself : beqETypSignature acc.1 acc.1 = true := beqETypSignature_refl acc.1
              simpa [acc1, hself] using htmp
            have hisParrow_acc1 : acc1.1.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hsig_acc1_acc
              calc
                acc1.1.isParrow = acc.1.isParrow := by simpa using hEq
                _ = true := hisParrow_acc
            have hdirty_acc1 : getInternalPoison acc1.1 = some true := by
              cases hacc : acc.1 with
              | parrow st1' st2' p' tcls' =>
                  have hptrue : p' = true := by
                    simpa [hacc, getInternalPoison] using hdirty_acc
                  have hdirty' :
                      getInternalPoison
                        (joinETyps (ETyp.parrow st1' st2' p' tcls') resEtyp acc.2.2.1 resPoison) = some true :=
                    joinETyps_preserves_dirty_parrow
                      (st1 := st1') (st2 := st2') (p1 := p') (tcls1 := tcls')
                      (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison) hptrue
                  simpa [acc1, hacc] using hdirty'
              | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                  simp [ETyp.isParrow, hacc] at hisParrow_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hisParrow_acc1 hdirty_acc1
  have h_fold_member_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.parrow st1 st2 true tcls →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hetyp_resEtyp : resEtyp = ETyp.parrow st1 st2 true tcls := by
                simpa [hqx] using hetyp_src'
              have hdirty_acc1 :
                  getInternalPoison acc1.1 = some true := by
                have hdirty' :
                    getInternalPoison (joinETyps acc.1 (ETyp.parrow st1 st2 true tcls) acc.2.2.1 resPoison) = some true :=
                  joinETyps_preserves_dirty_parrow_right
                    (t1 := acc.1) (st1 := st1) (st2 := st2) (tcls2 := tcls)
                    (p1 := true) (p1' := acc.2.2.1) (p2' := resPoison)
                    (by simpa [hetyp_resEtyp] using hcompat_x) rfl
                simpa [acc1, hqx, hetyp_resEtyp] using hdirty'
              exact h_fold_left_dirty xs acc1 acc' hcompat_tail hfold_tail
                (by
                  have hsig_acc1_src : beqETypSignature acc1.1 (ETyp.parrow st1 st2 true tcls) = true := by
                    have htmp :
                        beqETypSignature acc.1 (ETyp.parrow st1 st2 true tcls) =
                          beqETypSignature
                            (joinETyps acc.1 (ETyp.parrow st1 st2 true tcls) acc.2.2.1 resPoison)
                            (ETyp.parrow st1 st2 true tcls) :=
                      beqETypSignature_joinETyps_left
                        (t1 := acc.1) (t2 := ETyp.parrow st1 st2 true tcls)
                        (t3 := ETyp.parrow st1 st2 true tcls)
                        (p1 := acc.2.2.1) (p2 := resPoison)
                        (by simpa [hetyp_resEtyp] using hcompat_x)
                    have hlhs : beqETypSignature acc.1 (ETyp.parrow st1 st2 true tcls) = true := by
                      simpa [hetyp_resEtyp] using hcompat_x
                    simpa [hqx, hetyp_resEtyp, acc1, hlhs] using htmp
                  have hEq := etyp_isParrow_eq_of_beqSignature_true hsig_acc1_src
                  simpa [ETyp.isParrow] using hEq)
                hdirty_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hetyp_first : etyp = ETyp.parrow st1 st2 true tcls := by
                  simpa [hqt] using hetyp_src
                have hisParrow_first : etyp.isParrow = true := by
                  simp [hetyp_first, ETyp.isParrow]
                have hdirty_first : getInternalPoison etyp = some true := by
                  simp [hetyp_first, getInternalPoison]
                exact
                  h_fold_left_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold hisParrow_first hdirty_first
              · exact
                  h_fold_member_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    (by simpa [ctxAfter] using hetyp_src)

private lemma joinTypeResults_qualType_ref_membership_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) {ls_src : LocSet}
  (hetyp_src : src.qualType.etyp = ETyp.ref ls_src)
  (hin_src : l ∈ ls_src) :
  ∃ ls_res, res.qualType.etyp = ETyp.ref ls_res ∧ l ∈ ls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_ref :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ ls, acc.1 = ETyp.ref ls ∧ l ∈ ls) →
        ∃ ls, acc'.1 = ETyp.ref ls ∧ l ∈ ls := by
    intro rs' acc acc' hcompat hfold href_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact href_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases href_acc with ⟨ls_acc, hacc_ref, hin_acc⟩
            have href_acc1 : ∃ ls, acc1.1 = ETyp.ref ls ∧ l ∈ ls := by
              cases hres : resEtyp with
              | ref ls2 =>
                  refine ⟨LocSet.union ls_acc ls2, ?_, ?_⟩
                  · simp [acc1, hacc_ref, hres, joinETyps]
                  · simpa [LocSet.union] using (Or.inl hin_acc : l ∈ ls_acc ∨ l ∈ ls2)
              | int | bool | unit | string | arrow _ _ _ _ | parrow _ _ _ _ =>
                  exfalso
                  simp [hacc_ref, hres, beqETypSignature] at hcompat_x
            exact ih (acc := acc1) hcompat_tail hfold_tail href_acc1
  have h_fold_member_ref :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        (∃ ls, src'.qualType.etyp = ETyp.ref ls ∧ l ∈ ls) →
        ∃ ls, acc'.1 = ETyp.ref ls ∧ l ∈ ls := by
    intro rs' acc acc' src' hcompat hfold hmem_src' href_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              rcases href_src' with ⟨ls_x, hetyp_x, hin_x⟩
              have hetyp_resEtyp : resEtyp = ETyp.ref ls_x := by
                simpa [hqx] using hetyp_x
              have href_acc1 : ∃ ls, acc1.1 = ETyp.ref ls ∧ l ∈ ls := by
                cases hacc : acc.1 with
                | ref ls_acc =>
                    subst resEtyp
                    refine ⟨LocSet.union ls_acc ls_x, ?_, ?_⟩
                    · simp [acc1, hacc, joinETyps]
                    · simpa [LocSet.union] using (Or.inr hin_x : l ∈ ls_acc ∨ l ∈ ls_x)
                | int | bool | unit | string | arrow _ _ _ _ | parrow _ _ _ _ =>
                    exfalso
                    simp [hacc, hetyp_resEtyp, beqETypSignature] at hcompat_x
              exact h_fold_left_ref xs acc1 acc' hcompat_tail hfold_tail href_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail href_src'
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have href_first : ∃ ls, etyp = ETyp.ref ls ∧ l ∈ ls := by
                  refine ⟨ls_src, ?_, hin_src⟩
                  simpa [hqt] using hetyp_src
                rcases h_fold_left_ref
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold href_first with ⟨ls_res, hetyp_res, hin_res⟩
                exact ⟨ls_res, by simpa [ctxAfter] using hetyp_res, hin_res⟩
              · rcases h_fold_member_ref
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    ⟨ls_src, by simpa [ctxAfter] using hetyp_src, hin_src⟩
                  with ⟨ls_res, hetyp_res, hin_res⟩
                exact ⟨ls_res, by simpa [ctxAfter] using hetyp_res, hin_res⟩

private lemma joinTypeResults_qualType_arrow_member_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {p_src : Poison} {tcls_src : List FnTClosure} {tcl : FnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.arrow st1 st2 p_src tcls_src)
  (htcl_src : tcl ∈ tcls_src) :
  ∃ p_res tcls_res, res.qualType.etyp = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_arrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ p_acc tcls_acc, acc.1 = ETyp.arrow st1 st2 p_acc tcls_acc ∧ tcl ∈ tcls_acc) →
        ∃ p_res tcls_res, acc'.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' hcompat hfold harrow_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact harrow_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases harrow_acc with ⟨p_acc, tcls_acc, hacc_arrow, htcl_acc⟩
            have hisArrow_x : resEtyp.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hcompat_x
              calc
                resEtyp.isArrow = acc.1.isArrow := by
                  symm
                  simpa using hEq
                _ = true := by simp [hacc_arrow, ETyp.isArrow]
            rcases
                (joinETyps_arrow_structure
                  (st1 := st1) (st2 := st2) (p1 := p_acc) (tcls1 := tcls_acc)
                  (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison)
                  (by simpa [hacc_arrow] using hisArrow_x)
                  (by simpa [hacc_arrow] using hcompat_x))
              with ⟨p_acc1, tcls_acc1, hjoin_acc1, hmem_pres_left⟩
            have harrow_acc1 :
                ∃ p_mid tcls_mid, acc1.1 = ETyp.arrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
              refine ⟨p_acc1, tcls_acc1, ?_, ?_⟩
              · simpa [acc1, hacc_arrow] using hjoin_acc1
              · exact hmem_pres_left tcl htcl_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail harrow_acc1
  have h_fold_member_arrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.arrow st1 st2 p_src tcls_src →
        ∃ p_res tcls_res, acc'.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hsrc_resEtyp : resEtyp = ETyp.arrow st1 st2 p_src tcls_src := by
                simpa [hqx] using hetyp_src'
              have hisArrow_acc : acc.1.isArrow = true := by
                have hEq := etyp_isArrow_eq_of_beqSignature_true hcompat_x
                calc
                  acc.1.isArrow = resEtyp.isArrow := by
                    simpa using hEq
                  _ = true := by simp [hsrc_resEtyp, ETyp.isArrow]
              have harrow_acc1 :
                  ∃ p_mid tcls_mid, acc1.1 = ETyp.arrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
                cases hacc : acc.1 with
                | arrow st1l st2l pl tclsl =>
                    have hshape : (st1l == st1 && st2l == st2) = true := by
                      simpa [hacc, hsrc_resEtyp, beqETypSignature] using hcompat_x
                    have hshape_eq : st1l = st1 ∧ st2l = st2 := by
                      simpa using hshape
                    rcases hshape_eq with ⟨rfl, rfl⟩
                    refine ⟨joinPoison pl p_src, mergeFnTClosures tclsl tcls_src, ?_, ?_⟩
                    · simp [acc1, hacc, hsrc_resEtyp, joinETyps]
                    · exact mem_mergeFnTClosures_right tclsl tcls_src tcl htcl_src
                | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                    simp [ETyp.isArrow, hacc] at hisArrow_acc
              exact h_fold_left_arrow xs acc1 acc' hcompat_tail hfold_tail harrow_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have harrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_left_arrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold
                    ⟨p_src, tcls_src, by simpa [hqt] using hetyp_src, htcl_src⟩
                rcases harrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩
              · have harrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_member_arrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_tail
                    (by simpa [ctxAfter] using hetyp_src)
                rcases harrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩

private lemma joinTypeResults_qualType_parrow_member_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {p_src : Poison} {tcls_src : List PFnTClosure} {tcl : PFnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.parrow st1 st2 p_src tcls_src)
  (htcl_src : tcl ∈ tcls_src) :
  ∃ p_res tcls_res, res.qualType.etyp = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_parrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ p_acc tcls_acc, acc.1 = ETyp.parrow st1 st2 p_acc tcls_acc ∧ tcl ∈ tcls_acc) →
        ∃ p_res tcls_res, acc'.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' hcompat hfold hparrow_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hparrow_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases hparrow_acc with ⟨p_acc, tcls_acc, hacc_parrow, htcl_acc⟩
            have hisParrow_x : resEtyp.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hcompat_x
              calc
                resEtyp.isParrow = acc.1.isParrow := by
                  symm
                  simpa using hEq
                _ = true := by simp [hacc_parrow, ETyp.isParrow]
            rcases
                (joinETyps_parrow_structure
                  (st1 := st1) (st2 := st2) (p1 := p_acc) (tcls1 := tcls_acc)
                  (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison)
                  (by simpa [hacc_parrow] using hisParrow_x)
                  (by simpa [hacc_parrow] using hcompat_x))
              with ⟨p_acc1, tcls_acc1, hjoin_acc1, hmem_pres_left⟩
            have hparrow_acc1 :
                ∃ p_mid tcls_mid, acc1.1 = ETyp.parrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
              refine ⟨p_acc1, tcls_acc1, ?_, ?_⟩
              · simpa [acc1, hacc_parrow] using hjoin_acc1
              · exact hmem_pres_left tcl htcl_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hparrow_acc1
  have h_fold_member_parrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.parrow st1 st2 p_src tcls_src →
        ∃ p_res tcls_res, acc'.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hsrc_resEtyp : resEtyp = ETyp.parrow st1 st2 p_src tcls_src := by
                simpa [hqx] using hetyp_src'
              have hisParrow_acc : acc.1.isParrow = true := by
                have hEq := etyp_isParrow_eq_of_beqSignature_true hcompat_x
                calc
                  acc.1.isParrow = resEtyp.isParrow := by
                    simpa using hEq
                  _ = true := by simp [hsrc_resEtyp, ETyp.isParrow]
              have hparrow_acc1 :
                  ∃ p_mid tcls_mid, acc1.1 = ETyp.parrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
                cases hacc : acc.1 with
                | parrow st1l st2l pl tclsl =>
                    have hshape : (st1l == st1 && st2l == st2) = true := by
                      simpa [hacc, hsrc_resEtyp, beqETypSignature] using hcompat_x
                    have hshape_eq : st1l = st1 ∧ st2l = st2 := by
                      simpa using hshape
                    rcases hshape_eq with ⟨rfl, rfl⟩
                    refine ⟨joinPoison pl p_src, mergePFnTClosures tclsl tcls_src, ?_, ?_⟩
                    · simp [acc1, hacc, hsrc_resEtyp, joinETyps]
                    · exact mem_mergePFnTClosures_right tclsl tcls_src tcl htcl_src
                | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                    simp [ETyp.isParrow, hacc] at hisParrow_acc
              exact h_fold_left_parrow xs acc1 acc' hcompat_tail hfold_tail hparrow_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hparrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_left_parrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold
                    ⟨p_src, tcls_src, by simpa [hqt] using hetyp_src, htcl_src⟩
                rcases hparrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩
              · have hparrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_member_parrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_tail
                    (by simpa [ctxAfter] using hetyp_src)
                rcases hparrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩

private lemma joinTypeResults_transport_resultAgreesIfClean_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src :
    resultAgreesIfClean predSat (ctxAfter ctx src).regime
      μ₀ μ₁ θ₀ θ₁ src.qualType o₀ o₁) :
  resultAgreesIfClean predSat (ctxAfter ctx res).regime
    μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
  intro hclean_res
  have hclean_src :
      qtypCleanUnder (ctxAfter ctx src).regime src.qualType :=
    joinTypeResults_qualType_clean_compat_from_member
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      _h_join _hmem_src hclean_res
  have hagree_src :
      agreeValueUnder predSat (ctxAfter ctx src).regime μ₀ μ₁ θ₀ θ₁ src.qualType o₀ o₁ :=
    h_src hclean_src
  have _hagree_src_keep := hagree_src
  have hsig :
      beqETypSignature res.qualType.etyp src.qualType.etyp = true :=
    joinTypeResults_qualType_etyp_signature_compat_from_member
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      _h_join _hmem_src
  have hfunEq :
      res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType :=
    etyp_isFunctionType_eq_of_beqSignature_true hsig
  cases hagree_src with
  | clean_eq_nonref_nonarrow hpoison_src hnotfun_src hnotref_src hEq =>
      cases hclean_res with
      | clean hpoison_res =>
          have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = false := hnotfun_src
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref_res hEq
      | guard k htag hreg hnotfun_res =>
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun_res hnotref_res hEq
  | withPred_true_eq _ _ _ hnotfun_src hnotref_src hEq =>
      cases hclean_res with
      | clean hpoison_res =>
          have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = false := hnotfun_src
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref_res hEq
      | guard k htag hreg hnotfun_res =>
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun_res hnotref_res hEq
  | @clean_internal_arrow st1 st2 p tcls _qt tcl x body σcap ρcap₀ ρcap₁ _v₀ _v₁
      hclean_internal_src hetyp_src htcl hmatch hcap
      hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src hv₁ hv₂ =>
      cases hclean_res with
      | clean _hpoison_res =>
          have hlookup_back :
              ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                (ctxAfter ctx src).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src k b hk
          have hlookup_true_back :
              ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                (ctxAfter ctx src).regime.lookup? k = some true := by
            intro k hk
            exact hlookup_back k true hk
          have hcap_res :=
            agreeCapturedEnv_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              hlookup_true_back
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              hcap
          have hmemberVars₀_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberVars₀_src
          have hmemberCvcr₀_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberCvcr₀_src
          have hmemberVars₁_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberVars₁_src
          have hmemberCvcr₁_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberCvcr₁_src
          rcases
              joinTypeResults_qualType_arrow_member_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src hetyp_src htcl
            with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
          by_cases hclean_internal_res : internalPoisonClean res.qualType
          · exact agreeValueUnder.clean_internal_arrow hclean_internal_res hetyp_res htcl_res hmatch hcap_res
              hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res hv₁ hv₂
          · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
              have htyped_closure :
                  valueHasETyp θ₀ (Value.closure x body ρcap₀) (ETyp.arrow st1 st2 p tcls) := by
                have htcl_match : FnTClosure.regular x body σcap ∈ tcls := by
                  simpa [hmatch] using htcl
                refine valueHasETyp.closure (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₀.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₁] using htyped_closure
            have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
              have htyped_closure :
                  valueHasETyp θ₁ (Value.closure x body ρcap₁) (ETyp.arrow st1 st2 p tcls) := by
                have htcl_match : FnTClosure.regular x body σcap ∈ tcls := by
                  simpa [hmatch] using htcl
                refine valueHasETyp.closure (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₁.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₂] using htyped_closure
            have htyp1_res :
                valueHasETyp θ₀ o₀ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
            have htyp2_res :
                valueHasETyp θ₁ o₁ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
            have hisArrow_src : src.qualType.etyp.isArrow = true := by
              simp [hetyp_src, ETyp.isArrow]
            have hisArrow_res : res.qualType.etyp.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hsig
              calc
                res.qualType.etyp.isArrow = src.qualType.etyp.isArrow := hEq
                _ = true := hisArrow_src
            exact agreeValueUnder.dirty_internal_arrow hclean_internal_res hisArrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | @clean_internal_parrow st1 st2 p tcls _qt tcl x body pbody σcap ρcap₀ ρcap₁ _v₀ _v₁
      hclean_internal_src hetyp_src htcl hmatch hcap
      hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src hv₁ hv₂ =>
      cases hclean_res with
      | clean _hpoison_res =>
          have hlookup_back :
              ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                (ctxAfter ctx src).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src k b hk
          have hlookup_true_back :
              ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                (ctxAfter ctx src).regime.lookup? k = some true := by
            intro k hk
            exact hlookup_back k true hk
          have hcap_res :=
            agreeCapturedEnv_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              hlookup_true_back
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              hcap
          have hmemberVars₀_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberVars₀_src
          have hmemberCvcr₀_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberCvcr₀_src
          have hmemberVars₁_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberVars₁_src
          have hmemberCvcr₁_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberCvcr₁_src
          rcases
              joinTypeResults_qualType_parrow_member_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src hetyp_src htcl
            with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
          by_cases hclean_internal_res : internalPoisonClean res.qualType
          · exact agreeValueUnder.clean_internal_parrow hclean_internal_res hetyp_res htcl_res hmatch hcap_res
              hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res hv₁ hv₂
          · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
              have hpure : Expr.toPExpr? body = some pbody := hmatch.1
              have htyped_closure :
                  valueHasETyp θ₀ (Value.peClosure x body ρcap₀) (ETyp.parrow st1 st2 p tcls) := by
                have htcl_match : PFnTClosure.regular x pbody σcap ∈ tcls := by
                  simpa [hmatch.2] using htcl
                refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₀.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₁] using htyped_closure
            have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
              have hpure : Expr.toPExpr? body = some pbody := hmatch.1
              have htyped_closure :
                  valueHasETyp θ₁ (Value.peClosure x body ρcap₁) (ETyp.parrow st1 st2 p tcls) := by
                have htcl_match : PFnTClosure.regular x pbody σcap ∈ tcls := by
                  simpa [hmatch.2] using htcl
                refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₁.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₂] using htyped_closure
            have htyp1_res :
                valueHasETyp θ₀ o₀ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
            have htyp2_res :
                valueHasETyp θ₁ o₁ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
            have hisParrow_src : src.qualType.etyp.isParrow = true := by
              simp [hetyp_src, ETyp.isParrow]
            have hisParrow_res : res.qualType.etyp.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hsig
              calc
                res.qualType.etyp.isParrow = src.qualType.etyp.isParrow := hEq
                _ = true := hisParrow_src
            exact agreeValueUnder.dirty_internal_parrow hclean_internal_res hisParrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | dirty_internal_arrow hdirty_src hisArrow_src htyp1_src htyp2_src =>
      cases hclean_res with
      | clean _hpoison_res =>
          have htyp1_res :
              valueHasETyp θ₀ o₀ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
          have htyp2_res :
              valueHasETyp θ₁ o₁ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
          have hisArrow_res : res.qualType.etyp.isArrow = true := by
            have hEq := etyp_isArrow_eq_of_beqSignature_true hsig
            calc
              res.qualType.etyp.isArrow = src.qualType.etyp.isArrow := hEq
              _ = true := hisArrow_src
          have hdirty_res : ¬ internalPoisonClean res.qualType := by
            -- Extract the explicit `p = true` witness from the source dirty-arrow case.
            cases hs_etyp : src.qualType.etyp with
            | arrow st1 st2 p tcls =>
                have hptrue : p = true := by
                  have : ¬ p = false := by simpa [hs_etyp, internalPoisonClean, getInternalPoison] using hdirty_src
                  cases p <;> simp at this
                  rfl
                have hdirty_join :
                    getInternalPoison res.qualType.etyp = some true :=
                  joinTypeResults_qualType_getInternalPoison_true_from_member_arrow
                    (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                    _h_join _hmem_src (by simpa [hptrue] using hs_etyp)
                simp [internalPoisonClean, hdirty_join]
            | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                simp [ETyp.isArrow, hs_etyp] at hisArrow_src
          exact agreeValueUnder.dirty_internal_arrow hdirty_res hisArrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp only [ETyp.isFunctionType, Bool.or_eq_true]
            left
            exact hisArrow_src
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | dirty_internal_parrow hdirty_src hisParrow_src htyp1_src htyp2_src =>
      cases hclean_res with
      | clean _hpoison_res =>
          have htyp1_res :
              valueHasETyp θ₀ o₀ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
          have htyp2_res :
              valueHasETyp θ₁ o₁ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
          have hisParrow_res : res.qualType.etyp.isParrow = true := by
            have hEq := etyp_isParrow_eq_of_beqSignature_true hsig
            calc
              res.qualType.etyp.isParrow = src.qualType.etyp.isParrow := hEq
              _ = true := hisParrow_src
          have hdirty_res : ¬ internalPoisonClean res.qualType := by
            cases hs_etyp : src.qualType.etyp with
            | parrow st1 st2 p tcls =>
                have hptrue : p = true := by
                  have : ¬ p = false := by simpa [hs_etyp, internalPoisonClean, getInternalPoison] using hdirty_src
                  cases p <;> simp at this
                  rfl
                have hdirty_join :
                    getInternalPoison res.qualType.etyp = some true :=
                  joinTypeResults_qualType_getInternalPoison_true_from_member_parrow
                    (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                    _h_join _hmem_src (by simpa [hptrue] using hs_etyp)
                simp [internalPoisonClean, hdirty_join]
            | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                simp [ETyp.isParrow, hs_etyp] at hisParrow_src
          exact agreeValueUnder.dirty_internal_parrow hdirty_res hisParrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp only [ETyp.isFunctionType, Bool.or_eq_true]
            right
            exact hisParrow_src
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | clean_ref hpoison_src hetyp_src hlookup1 hin hv1 hlookup2 hv2 =>
      obtain ⟨ls_res, hetyp_res, hin_res⟩ :=
        joinTypeResults_qualType_ref_membership_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src _ hetyp_src hin
      cases hclean_res with
      | clean hpoison_res =>
          exact agreeValueUnder.clean_ref hpoison_res hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
      | guard k htag hreg _hnotfun =>
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
  | withPred_true_ref _ _ _ hetyp_src hlookup1 hin hv1 hlookup2 hv2 =>
      obtain ⟨ls_res, hetyp_res, hin_res⟩ :=
        joinTypeResults_qualType_ref_membership_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src _ hetyp_src hin
      cases hclean_res with
      | clean hpoison_res =>
          exact agreeValueUnder.clean_ref hpoison_res hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
      | guard k htag hreg _hnotfun =>
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp_res hlookup1 hin_res hv1 hlookup2 hv2

private lemma joinTypeResults_lookup_member_guardTag_compat
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
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
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' htag_res hlookup_src'

private lemma joinTypeResults_lookup_member_etyp_compat
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

private lemma joinTypeResults_lookup_member_poison_imp
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
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag') rest with
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
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src qt_src
                    hfold hsrc_rest hlookup_res' hclean_out hlookup_src'

private lemma joinTypeResults_lookup_member_clean_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qtypCleanUnder (ctxAfter ctx src).regime qt_src := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_lookup_member_poison_imp
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src hpoison)
  | guard k htag hreg hnotfun =>
      have htag_src : qtypGuardTag qt_src = some k :=
        joinTypeResults_lookup_member_guardTag_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src k hlookup_res hlookup_src htag
      have hreg_src : (ctxAfter ctx src).regime.lookup? k = some true :=
        joinTypeResults_lookup_member_regime_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src k true hreg
      have hetyp_eq : qt.etyp = qt_src.etyp :=
        joinTypeResults_lookup_member_etyp_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src
      have hnotfun_src : qt_src.etyp.isFunctionType = false := by
        simpa [hetyp_eq.symm] using hnotfun
      exact qtypCleanUnder.guard k htag_src hreg_src hnotfun_src

private lemma joinMemEnvs_lookup_guardClosure_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hjoin_eq_left := joinMemEnvs_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    have hqt_eq : qt1 = qt := by
      have hqeq_opt : some qt = some qt1 := by
        calc
          some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env1.lookup l := hjoin_eq_left
          _ = some qt1 := hlookup1
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using hpred_join
  · have hlookup2_some : env2.lookup l ≠ none := hlookup2_none
    rcases Option.ne_none_iff_exists'.1 hlookup2_some with ⟨qt2, hlookup2⟩
    have he1 : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
      |> (Std.ExtTreeMap.contains_iff_mem).mp
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
      memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
    have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by
      have hjoin_go : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = f l (env1.get? l) (env2.get? l) := by
        cases hopt : f l (env1.get? l) (env2.get? l) with
        | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
        | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
      rw [← h_go_eq_f]; exact hjoin_go
    have hqt_pred : qt.pred = joinPredicates qt1.pred qt2.pred := by
      erw [he1, he2] at hmatch
      have heq := (Option.some.inj hmatch).symm
      exact congr_arg MemEntry.pred heq
    have hsplit := joinPredicates_eq_guardClosure
      (p := qt1.pred) (q := qt2.pred) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env)
      (by simpa [hqt_pred] using hpred_join)
    exact hsplit.1

private lemma joinMemEnvs_lookup_guardClosure_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hjoin_eq_right := joinMemEnvs_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    have hqt_eq : qt2 = qt := by
      have hqeq_opt : some qt = some qt2 := by
        calc
          some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env2.lookup l := hjoin_eq_right
          _ = some qt2 := hlookup2
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using hpred_join
  · have hlookup1_some : env1.lookup l ≠ none := hlookup1_none
    rcases Option.ne_none_iff_exists'.1 hlookup1_some with ⟨qt1, hlookup1⟩
    have he1 : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
      |> (Std.ExtTreeMap.contains_iff_mem).mp
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
      memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
    have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by
      have hjoin_go : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = f l (env1.get? l) (env2.get? l) := by
        cases hopt : f l (env1.get? l) (env2.get? l) with
        | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
        | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
      rw [← h_go_eq_f]; exact hjoin_go
    have hqt_pred : qt.pred = joinPredicates qt1.pred qt2.pred := by
      erw [he1, he2] at hmatch
      have heq := (Option.some.inj hmatch).symm
      exact congr_arg MemEntry.pred heq
    have hsplit := joinPredicates_eq_guardClosure
      (p := qt1.pred) (q := qt2.pred) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env)
      (by simpa [hqt_pred] using hpred_join)
    exact hsplit.2

private lemma joinMemEnvsStrong_lookup_guardClosure_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hleft :=
      joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    rw [hlookup_join] at hleft
    have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
      simpa [hlookup1] using hleft
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact
      joinMemEnvs_lookup_guardClosure_left
        env1 env2 l qt qt1 k arg_name pred_body var_env
        hlookupW hlookup1 hpred_join

private lemma joinMemEnvsStrong_lookup_guardClosure_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hright :=
      joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    rw [hlookup_join] at hright
    have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
      simpa [hlookup2] using hright
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup1_none with ⟨qt1, hlookup1⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact
      joinMemEnvs_lookup_guardClosure_right
        env1 env2 l qt qt2 k arg_name pred_body var_env
        hlookupW hlookup2 hpred_join

private lemma joinMemEnvsStrong_lookup_guardClosure_implies_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt1, env1.lookup l = some qt1 ∧ qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases h1none : env1.lookup l = none
  · have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
      memEnv_contains_of_lookup_some (env := (joinMemEnvsStrong env1 env2)) (l := l) (qt := qt) hlookup_join
    have hor := joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join
    have hnot1 : ¬ env1.contains l := by
      intro hcontains1
      rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
      rw [hlookup1] at h1none
      cases h1none
    have hcontains2 : env2.contains l := by
      cases hor with
      | inl hcontains1 => exact (hnot1 hcontains1).elim
      | inr hcontains2 => exact hcontains2
    rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
    have h1none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h1none
    have hright :=
      joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l h1none_get hcontains2
    rw [hlookup_join] at hright
    have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
      simpa [hlookup2] using hright
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 h1none with ⟨qt1, hlookup1⟩
    exact ⟨qt1, hlookup1,
      joinMemEnvsStrong_lookup_guardClosure_left
        env1 env2 l qt qt1 k arg_name pred_body var_env
        hlookup_join hlookup1 hpred_join⟩

private lemma joinMemEnvsStrong_lookup_guardClosure_implies_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt2, env2.lookup l = some qt2 ∧ qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases h2none : env2.lookup l = none
  · have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
      memEnv_contains_of_lookup_some (env := (joinMemEnvsStrong env1 env2)) (l := l) (qt := qt) hlookup_join
    have hor := joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join
    have hnot2 : ¬ env2.contains l := by
      intro hcontains2
      rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
      rw [hlookup2] at h2none
      cases h2none
    have hcontains1 : env1.contains l := by
      cases hor with
      | inl hcontains1 => exact hcontains1
      | inr hcontains2 => exact (hnot2 hcontains2).elim
    rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
    have h2none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h2none
    have hleft :=
      joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 h2none_get
    rw [hlookup_join] at hleft
    have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
      simpa [hlookup1] using hleft
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 h2none with ⟨qt2, hlookup2⟩
    exact ⟨qt2, hlookup2,
      joinMemEnvsStrong_lookup_guardClosure_right
        env1 env2 l qt qt2 k arg_name pred_body var_env
        hlookup_join hlookup2 hpred_join⟩

private lemma joinTypeResults_lookup_member_guardClosure_lookup_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt : QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hpred_res : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt_src,
    (ctxAfter ctx src).memEnv.lookup l = some qt_src ∧
    qt_src.pred = Predicate.guardClosure k arg_name pred_body var_env := by
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
  have h_fold_left_guardClosure :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_out : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.1.lookup l = some qt_out →
        qt_out.pred = Predicate.guardClosure k arg_name pred_body var_env →
        ∃ qt_acc, acc.2.1.lookup l = some qt_acc ∧
          qt_acc.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' qt_out hfold hlookup_out hpred_out
    induction rs' generalizing acc acc' qt_out with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact ⟨qt_out, hlookup_out, hpred_out⟩
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
            rcases ih (acc := acc1) (acc' := acc') (qt_out := qt_out)
                hfold_tail hlookup_out hpred_out with
              ⟨qt_acc1, hlookup_acc1, hpred_acc1⟩
            rcases
                joinMemEnvsStrong_lookup_guardClosure_implies_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                  (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                  (hlookup_join := by simpa [acc1] using hlookup_acc1)
                  (hpred_join := hpred_acc1)
              with ⟨qt_acc, hlookup_acc, hpred_acc⟩
            exact ⟨qt_acc, hlookup_acc, hpred_acc⟩
  have h_fold_member_guardClosure :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult) (qt_out : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.1.lookup l = some qt_out →
        qt_out.pred = Predicate.guardClosure k arg_name pred_body var_env →
        ∃ qt_src', src'.memEnv'.lookup l = some qt_src' ∧
          qt_src'.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' src' qt_out hfold hmem_src' hlookup_out hpred_out
    induction rs' generalizing acc acc' src' qt_out with
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
              rcases h_fold_left_guardClosure
                  (rs' := xs) (acc := acc1) (acc' := acc') (qt_out := qt_out)
                  hfold_tail hlookup_out hpred_out with
                ⟨qt_acc1, hlookup_acc1, hpred_acc1⟩
              rcases
                  joinMemEnvsStrong_lookup_guardClosure_implies_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                    (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                    (hlookup_join := by simpa [acc1] using hlookup_acc1)
                    (hpred_join := hpred_acc1)
                with ⟨qt_x, hlookup_x, hpred_x⟩
              exact ⟨qt_x, hlookup_x, hpred_x⟩
            · exact
                ih (acc := acc1) (acc' := acc') (src' := src') (qt_out := qt_out)
                  hfold_tail hsrc_tail hlookup_out hpred_out
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                rcases
                    h_fold_left_guardClosure
                      rest
                      (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                        first.nextTag')
                      a qt hfold hlookup_res' hpred_res
                  with ⟨qt_first, hlookup_first, hpred_first⟩
                exact ⟨qt_first, by simpa [ctxAfter] using hlookup_first, hpred_first⟩
              · rcases
                    h_fold_member_guardClosure
                      rest
                      (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                        first.nextTag')
                      a src qt hfold hsrc_tail hlookup_res' hpred_res
                  with ⟨qt_src, hlookup_src, hpred_src⟩
                exact ⟨qt_src, by simpa [ctxAfter] using hlookup_src, hpred_src⟩

private lemma joinTypeResults_transport_consistentWithRegime_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : consistentWithRegime predSat (ctxAfter ctx src).regime (ctxAfter ctx src) μ ρ θ) :
  consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  unfold consistentWithRegime at h_src ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred_res : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred_res] at hguard
    | guardOnly k' =>
        exact locsRegime.guardOnly_ok (l, qt) k' hpred_res
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred_res]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinTypeResults_lookup_member_guardClosure_lookup_compat
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              _h_join _hmem_src l qt k' arg_name pred_body var_env hlookup hpred_res
          with ⟨qt_src, hlookup_src, hpred_src⟩
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [hk_eq] using hkres)
          | some b =>
              have hk_src : (ctxAfter ctx src).regime.lookup? k' = some b := hlookup_back k' b hkres
              rw [hk_src] at hnone
              contradiction
        have hguard_src : qtypGuardTag qt_src = some k' := by
          simp [qtypGuardTag, hpred_src]
        have hloc_src := h_src.1 l qt_src k' hlookup_src hguard_src hRdef_src
        cases hloc_src with
        | noPred_ok hnp =>
            simp [qtypGuardTag, hpred_src] at hnp
        | guardOnly_ok _ hgo =>
            simp [hpred_src] at hgo
        | withPred_ok k_src arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
            have hclos0 : qt_src.pred = Predicate.guardClosure k_src arg_name' pred_body' var_env' := by
              simpa using hclos
            have hk_src_eq : qtypGuardTag qt_src = some k_src := by
              simp [qtypGuardTag, hclos0]
            have hk_tag_eq : k_src = k' := by
              have : some k_src = some k' := by
                calc
                  some k_src = qtypGuardTag qt_src := by symm; exact hk_src_eq
                  _ = some k' := hguard_src
              exact Option.some.inj this
            have hclos' : qt_src.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
              simpa [hk_tag_eq] using hclos0
            have hreg' : (ctxAfter ctx src).regime.lookup? k' = some b := by
              simpa [hk_tag_eq] using hreg
            have hpred_ctor_eq :
                Predicate.guardClosure k' arg_name' pred_body' var_env' =
                  Predicate.guardClosure k' arg_name pred_body var_env := by
              calc
                Predicate.guardClosure k' arg_name' pred_body' var_env' = qt_src.pred := by
                  simpa using hclos'.symm
                _ = Predicate.guardClosure k' arg_name pred_body var_env := hpred_src
            cases hpred_ctor_eq
            have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
              cases hkres : (ctxAfter ctx res).regime.lookup? k' with
              | none =>
                  exact False.elim (hRdef (by simpa [hk_eq] using hkres))
              | some b' =>
                  have hk_src' : (ctxAfter ctx src).regime.lookup? k' = some b' := hlookup_back k' b' hkres
                  have hb_eq : b = b' := by
                    have : some b = some b' := by
                      calc
                        some b = (ctxAfter ctx src).regime.lookup? k' := by symm; exact hreg'
                        _ = some b' := hk_src'
                    exact Option.some.inj this
                  simp [hb_eq]
            have hpred_eq : qt_src.pred = qt.pred := by
              simp [hpred_src, hpred_res]
            have hcons_res :
                (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
              refine ⟨?_, ?_⟩
              · intro hb
                exact
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := qt_src) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
              · intro hb
                exact
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := qt_src) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                hpred_res hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k ≠ none := by
          intro hnone
          have hk_src := hlookup_back k b hkres
          rw [hk_src] at hnone
          contradiction
        have hvar_src :=
          h_src.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_src
        exact
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
            (μ := μ) (ρ := ρ) (entry := (x, qt))
            hlookup_back hguard hkres hvar_src
  · intro x qt v hlookup hlookup_v
    have hcap_src :
        closureCapturedVarsRegime predSat (ctxAfter ctx src).regime qt μ θ v :=
      h_src.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegime_transport_lookup_back
        (predSat := predSat)
        (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_src

private lemma joinTypeResults_mem_contains_of_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest) :
  ∀ l, src.memEnv'.contains l → res.memEnv'.contains l := by
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
  have h_fold_acc_contains :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ l, acc.2.1.contains l → acc'.2.1.contains l := by
    intro rs' acc acc' hfold
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        intro l hcontains
        exact hcontains
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
            intro l hcontains_acc
            rcases memEnv_lookup_some_of_contains acc.2.1 l hcontains_acc with ⟨qt_acc, hlookup_acc⟩
            rcases joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc with
              ⟨qt_acc1, hlookup_acc1⟩
            have hcontains_acc1 : acc1.2.1.contains l := by
              apply memEnv_contains_of_lookup_some (env := acc1.2.1) (l := l) (qt := qt_acc1)
              simpa [acc1] using hlookup_acc1
            exact ih (acc := acc1) hfold_tail l hcontains_acc1
  have h_fold_member_contains :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ r ∈ rs', ∀ l, r.memEnv'.contains l → acc'.2.1.contains l := by
    intro rs' acc acc' hfold
    induction rs' generalizing acc with
    | nil =>
        intro r hr
        cases hr
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
            intro r hr l hcontains_r
            rcases (List.mem_cons.mp hr) with hrx | hrxs
            · subst r
              rcases memEnv_lookup_some_of_contains x.memEnv' l hcontains_r with ⟨qt_x, hlookup_x⟩
              rcases joinMemEnvsStrong_lookup_some_of_right_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_x) hlookup_x with
                ⟨qt_acc1, hlookup_acc1⟩
              have hcontains_acc1 : acc1.2.1.contains l := by
                apply memEnv_contains_of_lookup_some (env := acc1.2.1) (l := l) (qt := qt_acc1)
                simpa [acc1] using hlookup_acc1
              exact h_fold_acc_contains xs acc1 acc' hfold_tail l hcontains_acc1
            · exact ih (acc := acc1) hfold_tail r hrxs l hcontains_r
  have hsrc_sum : src = first ∨ src ∈ rest := List.mem_cons.mp _hmem_src
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
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              intro l hcontains_src
              cases hsrc_sum with
              | inl hsrc_eq =>
                  subst src
                  exact h_fold_acc_contains
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold l hcontains_src
              | inr hsrc_rest =>
                  exact h_fold_member_contains
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold src hsrc_rest l hcontains_src

private lemma applyFnTClosure_ok_poison_pred_of_p1_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : FnTClosure) (r : TypeResult)
  (h_p1 : p1 = true)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  subst h_p1
  unfold applyFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind, normalizeAppResultByProvenance] at happly
          cases htc :
              typecheckExpr .ioFree
                { ctx with
                  pc := joinPoison p (joinPoison true ctx.pc)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } body fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec effects capturedEnv =>
          have hmode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            decide
          have hcontra := happly
          rw [hmode] at hcontra
          simp [bind, Except.bind] at hcontra

private lemma applyPFnTClosure_ok_poison_pred_of_p1_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (h_p1 : p1 = true)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  subst h_p1
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind, normalizeAppResultByProvenance] at happly
          cases htc :
              typecheckExpr .ioFree
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc true)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  pureCtx := true
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } (PExpr.toExpr body) fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec capturedEnv =>
          have hmode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            decide
          have hcontra := happly
          rw [hmode] at hcontra
          simp [bind, Except.bind] at hcontra

-- Generalized variants: when joinPoison p1 p = true (covers both p1=true and p=true cases).
-- After the app-typing fix (AppPred (join p1 p) P3), normalizeAppResultByProvenance
-- is called with (joinPoison p1 p), so either outer or internal poison being dirty
-- forces poison=true, pred=noPred.
private lemma applyFnTClosure_ok_poison_pred_of_p1p_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : FnTClosure) (r : TypeResult)
  (h_p1p : joinPoison p1 p = true)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  unfold applyFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          cases htc :
              typecheckExpr .ioFree
                { ctx with
                  pc := joinPoison p (joinPoison p1 ctx.pc)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } body fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance, h_p1p] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec effects capturedEnv =>
          have hmode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            decide
          have hcontra := happly
          rw [hmode] at hcontra
          simp [bind, Except.bind] at hcontra

private lemma applyPFnTClosure_ok_poison_pred_of_p1p_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (h_p1p : joinPoison p1 p = true)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  r.qualType.poison = true ∧ r.qualType.pred = Predicate.noPred := by
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          cases htc :
              typecheckExpr .ioFree
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc p1)
                  memEnv := result2.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                    ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
                  tagEnv := result2.tagEnv'
                  pureCtx := true
                  nextTag := result2.nextTag'
                  nextLoc := result2.nextLoc'
                  regime := result2.regime' } (PExpr.toExpr body) fuelBody with
          | error err =>
              simp [htc] at happly
          | ok result3 =>
              simp [htc] at happly
              cases hq3 : result3.qualType with
              | mk et3 p3 pred3 =>
                  cases hsub : isSubtype st2 result3.qualType with
                  | false =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                        simpa [hq3] using hsub
                      simp [hsub', hq3] at happly
                  | true =>
                      have hsub' : isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = true := by
                        simpa [hq3] using hsub
                      have happly' :
                          (Except.ok
                              { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                                memEnv' := result3.memEnv'
                                tagEnv' := result3.tagEnv'
                                nextLoc' := result3.nextLoc'
                                nextTag' := result3.nextTag'
                                regime' := result3.regime' } : Except String TypeResult) = Except.ok r := by
                        simpa [hsub', hq3, pure, Except.pure, normalizeAppResultByProvenance, h_p1p] using happly
                      have hr :
                          { qualType := { etyp := et3, poison := true, pred := Predicate.noPred }
                            memEnv' := result3.memEnv'
                            tagEnv' := result3.tagEnv'
                            nextLoc' := result3.nextLoc'
                            nextTag' := result3.nextTag'
                            regime' := result3.regime' } = r := by
                        exact Except.ok.inj happly'
                      subst hr
                      simp
      | extern x retSpec capturedEnv =>
          have hmode : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            decide
          have hcontra := happly
          rw [hmode] at hcontra
          simp [bind, Except.bind] at hcontra

private lemma applyPFnTClosure_mem_subset
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
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
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextLoc := result2.nextLoc'
              regime := result2.regime' }
          have hsub_body :
              ∀ l, result3.memEnv'.contains l → bodyCtx.memEnv.contains l :=
            typecheckExpr_pure_mem_subset_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hsub_body l hcontains
      | extern x retSpec capturedEnv =>
          exact False.elim <|
            applyPFnTClosure_ioFree_extern_fails
              ctx st1 st2 p p1 argEtyp argPoison argPred result2
              (Nat.succ fuelBody) x retSpec capturedEnv r happly

private lemma applyPFnTClosure_preserves_memEnv_lookup
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : PFnTClosure) (r : TypeResult)
  (happly :
    applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r) :
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
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextLoc := result2.nextLoc'
              regime := result2.regime' }
          have hpres_body :
              ∀ l qt, bodyCtx.memEnv.lookup l = some qt → result3.memEnv'.lookup l = some qt :=
            typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
              (ctx := bodyCtx) (e := PExpr.toExpr body) (pe := body)
              (fuel := fuelBody) (res := result3)
              (hpe := by simpa using toExpr_toPExpr? body)
              (htc := by simpa [bodyCtx] using htcBody)
          simpa [bodyCtx] using hpres_body l qt hlookup
      | extern x retSpec capturedEnv =>
          exact False.elim <|
            applyPFnTClosure_ioFree_extern_fails
              ctx st1 st2 p p1 argEtyp argPoison argPred result2
              (Nat.succ fuelBody) x retSpec capturedEnv r happly

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

private lemma clean_lookup_origin_of_same_qt
  {R R' : Regime} {Γ Γ' : MemoryTypeEnv} {l : Loc} {qt : QTyp}
  (hlookup_in : Γ.lookup l = some qt)
  (_hlookup_out : Γ'.lookup l = some qt)
  (hmono : Regime.monotoneStep R R') :
  qtypCleanUnder R' qt →
  ∃ qt_in, Γ.lookup l = some qt_in ∧ qtypCleanUnder R qt_in := by
  intro hclean
  exact ⟨qt, hlookup_in, cleanUnder_of_monotone hmono hclean⟩

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

private lemma joinMemEnvsStrong_lookup_cleanUnder_left_or_right
  (env1 env2 : MemoryTypeEnv) (R1 R2 : Regime) (l : Loc) (qt : QTyp)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hclean_join : qtypCleanUnder (joinRegimes R1 R2) qt) :
  (∃ qt1, env1.lookup l = some qt1 ∧ qtypCleanUnder R1 qt1) ∨
  (∃ qt2, env2.lookup l = some qt2 ∧ qtypCleanUnder R2 qt2) := by
  have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
    memEnv_contains_of_lookup_some (joinMemEnvsStrong env1 env2) l qt hlookup_join
  rcases joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join with hcontains1 | hcontains2
  · rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
    left
    cases hclean_join with
    | clean hpoison =>
        have henv1 : env1.lookup l ≠ none := by
          intro hnone
          rw [hlookup1] at hnone
          contradiction
        rcases joinMemEnvsStrong_lookup_clean_left env1 env2 l qt hlookup_join hpoison henv1 with
          ⟨qt1', hlookup1', _hetyp, hpoison1'⟩
        exact ⟨qt1', hlookup1', qtypCleanUnder.clean hpoison1'⟩
    | guard k htag hk hnotfun =>
        have htag1 : qtypGuardTag qt1 = some k :=
          joinMemEnvsStrong_lookup_guardTag_left env1 env2 l qt qt1 k hlookup_join hlookup1 htag
        have hk1 : R1.lookup? k = some true :=
          joinRegimes_lookup_some_left R1 R2 k true hk
        have hnotfun1 : qt1.etyp.isFunctionType = false := by
          rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1]
          native_decide
        exact ⟨qt1, hlookup1, qtypCleanUnder.guard k htag1 hk1 hnotfun1⟩
  · rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
    right
    cases hclean_join with
    | clean hpoison =>
        have henv2 : env2.lookup l ≠ none := by
          intro hnone
          rw [hlookup2] at hnone
          contradiction
        rcases joinMemEnvsStrong_lookup_clean_right env1 env2 l qt hlookup_join hpoison henv2 with
          ⟨qt2', hlookup2', _hetyp, hpoison2'⟩
        exact ⟨qt2', hlookup2', qtypCleanUnder.clean hpoison2'⟩
    | guard k htag hk hnotfun =>
        have htag2 : qtypGuardTag qt2 = some k :=
          joinMemEnvsStrong_lookup_guardTag_right env1 env2 l qt qt2 k hlookup_join hlookup2 htag
        have hk2 : R2.lookup? k = some true :=
          joinRegimes_lookup_some_right R1 R2 k true hk
        have hnotfun2 : qt2.etyp.isFunctionType = false := by
          rw [memEnv_lookup_etyp_int env2 l qt2 hlookup2]
          native_decide
        exact ⟨qt2, hlookup2, qtypCleanUnder.guard k htag2 hk2 hnotfun2⟩

private lemma typecheckExpr_clean_lookup_origin_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr .ioFree ctx e fuel = .ok res)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_out : QTyp),
    res.memEnv'.lookup l = some qt_out →
    qtypCleanUnder res.regime' qt_out →
    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
  classical
  revert ctx e res htc hpc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e res htc hpc l qt_out hlookup_out hclean_out
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
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | bool b =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | unit =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | str s =>
          simp [typecheckExpr] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
      | var x =>
          have htcVar : typecheckVar ctx x = .ok res := by
            simpa [typecheckExpr] using htc
          have hmem : res.memEnv' = ctx.memEnv :=
            typecheckVar_preserves_memEnv ctx x res htcVar
          have hreg : res.regime' = ctx.regime :=
            typecheckVar_preserves_regime ctx x res htcVar
          exact ⟨qt_out, by simpa [hmem] using hlookup_out, by simpa [hreg] using hclean_out⟩
      | fn x st1 body st2 =>
          simp [typecheckExpr, typecheckFn] at htc
          cases htc
          exact ⟨qt_out, hlookup_out, hclean_out⟩
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
              exact ⟨qt_out, hlookup_out, hclean_out⟩
      | op e1 bop e2 =>
          have htcOp : typecheckOp .ioFree ctx e1 e2 fuel' bop = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckOp_structure ctx e1 e2 bop fuel' res htcOp with
            ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
              h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean2 : qtypCleanUnder result2.regime' qt_out := by
            simpa [h_regime] using hclean_out
          have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
            simpa [updateCtxFromResult] using hpc
          rcases ih (fuel' - 1) hltSub
              (updateCtxFromResult ctx result1) e2 result2
              (by simpa [updateCtxFromResult] using htc2)
              hpc2 l qt_out hlookup2 hclean2 with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [updateCtxFromResult] using hlookup_mid)
              (by simpa [updateCtxFromResult] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | unaryop uop e1 =>
          have htcUnary : typecheckUnaryOp .ioFree ctx uop e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckUnaryOp_structure ctx uop e1 fuel' res htcUnary with
            ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, h_regime,
              _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean1 : qtypCleanUnder result1.regime' qt_out := by
            simpa [h_regime] using hclean_out
          exact ih (fuel' - 1) hltSub ctx e1 result1
            (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | deref e1 =>
          have htcDeref : typecheckDeref .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckDeref_structure ctx e1 fuel' res htcDeref with
            ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, h_regime⟩
          have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean1 : qtypCleanUnder result1.regime' qt_out := by
            simpa [h_regime] using hclean_out
          exact ih (fuel' - 1) hltSub ctx e1 result1
            (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | seq e1 e2 =>
          have htcSeq : typecheckSeq .ioFree ctx e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
            ⟨result1, ctx', htc1, hctx', htc2⟩
          have hpc2 : ctx'.pc = true := by
            simpa [hctx', updateCtxFromResult] using hpc
          rcases ih (fuel' - 1) hltSub ctx' e2 res
              (by simpa [hctx'] using htc2) hpc2 l qt_out hlookup_out hclean_out with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [hctx', updateCtxFromResult] using hlookup_mid)
              (by simpa [hctx', updateCtxFromResult] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | vlet x e1 e2 =>
          have htcVlet : typecheckVlet .ioFree ctx x e1 e2 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
            ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc,
              _h_ntag, h_regime, _h_ret_poison, _h_ret_pred⟩
          have hlookup2 : result2.memEnv'.lookup l = some qt_out := by
            simpa [h_mem] using hlookup_out
          have hclean2 : qtypCleanUnder result2.regime' qt_out := by
            simpa [h_regime] using hclean_out
          have hpc2 : ctx'.pc = true := by
            simpa [hctx'] using hpc
          rcases ih (fuel' - 1) hltSub ctx' e2 result2
              (by simpa [hctx'] using htc2) hpc2 l qt_out hlookup2 hclean2 with
            ⟨qt_mid, hlookup_mid, hclean_mid⟩
          rcases ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_mid
              (by simpa [hctx'] using hlookup_mid)
              (by simpa [hctx'] using hclean_mid) with
            ⟨qt_in, hlookup_in, hclean_in⟩
          exact ⟨qt_in, hlookup_in, hclean_in⟩
      | newRef e1 =>
          have htcNew : typecheckNewRef .ioFree ctx e1 fuel' = .ok res := by
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
            exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred rfl rfl) hclean_out)
          · have hlookup1 : result1.memEnv'.lookup l = some qt_out := by
              rw [h_mem] at hlookup_out
              rw [MemoryTypeEnv_lookup_updateMemEnv_ne (l := lfresh) (l' := l)
                    (qt := { etyp := ETyp.int
                             poison := joinPoison ctx.pc result1.qualType.poison
                             pred := if ctx.pc then Predicate.noPred else result1.qualType.pred }) hEq] at hlookup_out
              exact hlookup_out
            have hclean1 : qtypCleanUnder result1.regime' qt_out := by
              simpa [h_regime] using hclean_out
            exact ih (fuel' - 1) hltSub ctx e1 result1
              (by simpa using htc1) hpc l qt_out hlookup1 hclean1
      | assign e1 e2 =>
          have htcAssign : typecheckAssign .ioFree ctx e1 e2 fuel' = .ok res := by
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
                    exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred rfl rfl) hclean_out)
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
                          | none => (accP, accPred)) with hjoined
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
                      simpa using
                        list_fold_joinPoison_first_true result2.memEnv' ls.toList Predicate.noPred
                    have hpred : finalQt.pred = Predicate.noPred := by
                      simp [finalQt, joined, hpc]
                      unfold LocSet.fold
                      rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                      simpa using list_fold_joinPredicates_init_noPred result2.memEnv' ls.toList true
                    exact False.elim ((not_qtypCleanUnder_of_poison_true_noPred hpoison hpred) hclean_out)
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
                simpa [h_mem] using hlookup_out
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
            have hclean2 : qtypCleanUnder result2.regime' qt_out := by
              have hclean_inv : qtypCleanUnder (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) qt_out := by
                simpa [h_regime] using hclean_out
              exact cleanUnder_of_monotone
                (invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls)
                hclean_inv
            have hpc2 : (updateCtxFromResult ctx result1).pc = true := by
              simpa [updateCtxFromResult] using hpc
            rcases ih (fuel' - 1) hltSub
                (updateCtxFromResult ctx result1) e2 result2
                (by simpa [updateCtxFromResult] using htc2)
                hpc2 l qt_out hlookup2 hclean2 with
              ⟨qt_mid, hlookup_mid, hclean_mid⟩
            rcases ih (fuel' - 1) hltSub ctx e1 result1
                (by simpa using htc1) hpc l qt_mid
                (by simpa [updateCtxFromResult] using hlookup_mid)
                (by simpa [updateCtxFromResult] using hclean_mid) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, hlookup_in, hclean_in⟩
      | ite e1 e2 e3 =>
          have htcIf : typecheckIf .ioFree ctx e1 e2 e3 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htcIf with h1 | h2 | h3 | h4
          · rcases h1 with ⟨k, deps, _hmg, _hk, _res1, _htc1, _hBool, res2, htc2, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
            have hpcTrue : ctxTrue.pc = true := by
              simpa [ctxTrue] using hpc
            rcases ih (fuel' - 1) hltSub ctxTrue e2 res2
                (by simpa [ctxTrue] using htc2) hpcTrue l qt_out
                (by simpa [h_mem] using hlookup_out)
                (by simpa [h_regime] using hclean_out) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, by simpa [ctxTrue] using hclean_in⟩
          · rcases h2 with ⟨k, deps, _hmg, _hk, _res1, _htc1, _hBool, res3, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp⟩
            let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
            have hpcFalse : ctxFalse.pc = true := by
              simpa [ctxFalse] using hpc
            rcases ih (fuel' - 1) hltSub ctxFalse e3 res3
                (by simpa [ctxFalse] using htc3) hpcFalse l qt_out
                (by simpa [h_mem] using hlookup_out)
                (by simpa [h_regime] using hclean_out) with
              ⟨qt_in, hlookup_in, hclean_in⟩
            exact ⟨qt_in, by simpa [ctxFalse] using hlookup_in, by simpa [ctxFalse] using hclean_in⟩
          · rcases h3 with ⟨k, deps, _hmg, _hkNone, res1, _htc1, _hBool, res2, htc2, res3, htc3, h_mem,
              _h_tag, _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp, _h_pred⟩
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [h_mem] using hlookup_out
            have hclean_join : qtypCleanUnder (joinRegimes res2.regime' res3.regime') qt_out := by
              simpa [h_regime] using hclean_out
            have hbranch :=
              joinMemEnvsStrong_lookup_cleanUnder_left_or_right
                res2.memEnv' res3.memEnv' res2.regime' res3.regime' l qt_out
                hlookup_join hclean_join
            let branchPc := joinPoison ctx.pc res1.qualType.poison
            let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
            let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
            let ctxFalse' : TypeContext := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            have hpcBranch : branchPc = true := by
              simp [branchPc, hpc, joinPoison]
            have hpcTrue : ctxTrue.pc = true := by
              simp [ctxTrue, hpcBranch]
            have hpcFalse : ctxFalse'.pc = true := by
              simp [ctxFalse', ctxFalse, hpcBranch]
            rcases hbranch with hleft | hright
            · rcases hleft with ⟨qt2, hlookup2, hclean2⟩
              rcases ih (fuel' - 1) hltSub ctxTrue e2 res2
                  (by simpa [ctxTrue, branchPc] using htc2) hpcTrue l qt2 hlookup2 hclean2 with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, by simpa [ctxTrue] using hlookup_in, by simpa [ctxTrue] using hclean_in⟩
            · rcases hright with ⟨qt3, hlookup3, hclean3⟩
              rcases ih (fuel' - 1) hltSub ctxFalse' e3 res3
                  (by simpa [ctxFalse', ctxFalse, branchPc] using htc3) hpcFalse l qt3 hlookup3 hclean3 with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, by simpa [ctxFalse', ctxFalse] using hlookup_in, by simpa [ctxFalse', ctxFalse] using hclean_in⟩
          · rcases h4 with ⟨_herr, res1, htc1, _hBool, res2, htc2, res3, htc3, h_mem, _h_tag,
              _h_nextLoc, _h_nextTag, h_regime, _h_poison, _h_etyp, _h_pred⟩
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [h_mem] using hlookup_out
            have hclean_join : qtypCleanUnder (joinRegimes res2.regime' res3.regime') qt_out := by
              simpa [h_regime] using hclean_out
            have hbranch :=
              joinMemEnvsStrong_lookup_cleanUnder_left_or_right
                res2.memEnv' res3.memEnv' res2.regime' res3.regime' l qt_out
                hlookup_join hclean_join
            let ctx' : TypeContext := ctxAfter ctx res1
            let pc' := joinPoison ctx.pc res1.qualType.poison
            let ctx'' : TypeContext := { ctx' with pc := pc' }
            let ctxForE3 : TypeContext := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            have hpc'' : ctx''.pc = true := by
              simp [ctx'', pc', hpc, joinPoison]
            rcases hbranch with hleft | hright
            · rcases hleft with ⟨qt2, hlookup2, hclean2⟩
              rcases ih (fuel' - 1) hltSub ctx'' e2 res2
                  (by simpa [ctx'', ctx', pc', ctxAfter] using htc2) hpc'' l qt2 hlookup2 hclean2 with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 res1
                  (by simpa using htc1) hpc l qt_mid
                  (by simpa [ctx'', ctx', ctxAfter] using hlookup_mid)
                  (by simpa [ctx'', ctx', ctxAfter] using hclean_mid) with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, hlookup_in, hclean_in⟩
            · rcases hright with ⟨qt3, hlookup3, hclean3⟩
              rcases ih (fuel' - 1) hltSub ctxForE3 e3 res3
                  (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using htc3)
                  (by simp [ctxForE3, ctx'', pc', hpc, joinPoison]) l qt3 hlookup3 hclean3 with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              rcases ih (fuel' - 1) hltSub ctx e1 res1
                  (by simpa using htc1) hpc l qt_mid
                  (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hlookup_mid)
                  (by simpa [ctxForE3, ctx'', ctx', ctxAfter] using hclean_mid) with
                ⟨qt_in, hlookup_in, hclean_in⟩
              exact ⟨qt_in, hlookup_in, hclean_in⟩
      | app e1 e2 =>
          have htcApp : typecheckApp .ioFree ctx e1 e2 fuel' = .ok res := by
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
                  nextTag := result2.nextTag'
                  regime := result2.regime' }
              have hpcFun : ctxFun.pc = true := by
                simpa [ctxFun] using hpc
              have hbackToCtx :
                  ∀ qt_mid,
                    result1.memEnv'.lookup l = some qt_mid →
                    qtypCleanUnder result1.regime' qt_mid →
                    ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                intro qt_mid hlookup_mid hclean_mid
                rcases ih fuelApp (by omega) ctxFun e1 result1
                    (by simpa [ctxFun] using htc1) hpcFun l qt_mid hlookup_mid hclean_mid with
                  ⟨qt_arg, hlookup_arg, hclean_arg⟩
                rcases ih fuelApp (by omega) ctx e2 result2
                    (by simpa using htc2) hpc l qt_arg
                    (by simpa [ctxFun] using hlookup_arg)
                    (by simpa [ctxFun] using hclean_arg) with
                  ⟨qt_in, hlookup_in, hclean_in⟩
                exact ⟨qt_in, hlookup_in, hclean_in⟩
              have hcontains_res : res.memEnv'.contains l := by
                exact memEnv_contains_of_lookup_some res.memEnv' l qt_out hlookup_out
              have hlookup_res_ctx :
                  (ctxAfter ctx res).memEnv.lookup l = some qt_out := by
                simpa [ctxAfter] using hlookup_out
              have hclean_res_ctx :
                  qtypCleanUnder (ctxAfter ctx res).regime qt_out := by
                simpa [ctxAfter] using hclean_out
              cases hcases with
              | inl harrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1,
                      _hnpure, _hnempty, _hsub, hmap, heq_results, h_join⟩ := harrow
                  have hmember_origin :
                      ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                        ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                    intro srcRes hsrc_mem hsrc_contains
                    have hsrc_results : srcRes ∈ results := by
                      simpa [heq_results] using hsrc_mem
                    rcases list_mapM_ok_mem_output_exists_input
                        (f := fun tcl =>
                          applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuelApp)
                        (xs := tcls) (ys := results) (y := srcRes)
                        hmap hsrc_results with
                      ⟨tcl, _htcl_mem, happly_src⟩
                    rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                      ⟨qt_src, hlookup_src⟩
                    have hlookup_src_ctx :
                        (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                      simpa [ctxAfter] using hlookup_src
                    have hclean_src_ctx :
                        qtypCleanUnder (ctxAfter ctx srcRes).regime qt_src := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hclean_res_ctx hlookup_src_ctx
                    cases tcl with
                    | regular x body tenv =>
                        rcases applyFnTClosure_regular_structure
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp x body tenv
                            srcRes happly_src with
                          ⟨fuelBody, hfuelBody⟩
                        have happly_succ :
                            applyFnTClosure .ioFree (FnTClosure.regular x body tenv)
                              st1 st2 p p1 etyp2 p2 pred2 ctx result1 (Nat.succ fuelBody) = .ok srcRes := by
                          simpa [hfuelBody] using happly_src
                        rcases applyFnTClosure_regular_inv
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelBody x body tenv srcRes
                            happly_succ with
                          ⟨result3, htcBody, _hsubBody, hr⟩
                        let bodyCtx : TypeContext :=
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc)
                            memEnv := result1.memEnv'
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                              ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                            tagEnv := result1.tagEnv'
                            nextTag := result1.nextTag'
                            nextLoc := result1.nextLoc'
                            regime := result1.regime' }
                        have hpcBody : bodyCtx.pc = true := by
                          simp [bodyCtx, hpc, joinPoison]
                        have hlookup_result3 : result3.memEnv'.lookup l = some qt_src := by
                          simpa [hr] using hlookup_src
                        have hclean_result3 : qtypCleanUnder result3.regime' qt_src := by
                          simpa [ctxAfter, hr] using hclean_src_ctx
                        rcases ih fuelBody (by omega) bodyCtx body result3
                            (by simpa [bodyCtx] using htcBody)
                            hpcBody l qt_src hlookup_result3 hclean_result3 with
                          ⟨qt_mid, hlookup_mid_body, hclean_mid_body⟩
                        exact
                          hbackToCtx qt_mid
                            (by simpa [bodyCtx] using hlookup_mid_body)
                            (by simpa [bodyCtx] using hclean_mid_body)
                    | extern x retSpec effects capturedEnv =>
                        exact False.elim <|
                          applyFnTClosure_ioFree_extern_fails
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp
                            x retSpec effects capturedEnv srcRes happly_src
                  rcases joinTypeResults_mem_contains_head_or_rest
                      ctx first rest res h_join l hcontains_res with
                    hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                  · exact hmember_origin first (by simp) hhead
                  · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
              | inr hparrow =>
                  obtain ⟨st1, st2, p, p1, tcls, results, first, rest, _hetyp1, _hp1,
                      _hnempty, _hsub, hmap, heq_results, h_join⟩ := hparrow
                  have hmember_origin :
                      ∀ srcRes, srcRes ∈ first :: rest → srcRes.memEnv'.contains l →
                        ∃ qt_in, ctx.memEnv.lookup l = some qt_in ∧ qtypCleanUnder ctx.regime qt_in := by
                    intro srcRes hsrc_mem hsrc_contains
                    have hsrc_results : srcRes ∈ results := by
                      simpa [heq_results] using hsrc_mem
                    rcases list_mapM_ok_mem_output_exists_input
                        (f := fun tcl =>
                          applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuelApp)
                        (xs := tcls) (ys := results) (y := srcRes)
                        hmap hsrc_results with
                      ⟨tcl, _htcl_mem, happly_src⟩
                    rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                      ⟨qt_src, hlookup_src⟩
                    have hlookup_src_ctx :
                        (ctxAfter ctx srcRes).memEnv.lookup l = some qt_src := by
                      simpa [ctxAfter] using hlookup_src
                    have hclean_src_ctx :
                        qtypCleanUnder (ctxAfter ctx srcRes).regime qt_src := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctx) (first := first) (src := srcRes) (rest := rest) (res := res)
                          h_join hsrc_mem l qt_out qt_src hlookup_res_ctx hclean_res_ctx hlookup_src_ctx
                    cases tcl with
                    | regular x pbody tenv =>
                        have hcontains_result1 : result1.memEnv'.contains l := by
                          exact
                            applyPFnTClosure_mem_subset
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (result2 := result1) (fuel := fuelApp)
                              (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                              happly_src l hsrc_contains
                        rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_result1 with
                          ⟨qt_mid, hlookup_mid⟩
                        have hlookup_preserved :
                            srcRes.memEnv'.lookup l = some qt_mid := by
                          exact
                            applyPFnTClosure_preserves_memEnv_lookup
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (result2 := result1) (fuel := fuelApp)
                              (tcl := PFnTClosure.regular x pbody tenv) (r := srcRes)
                              happly_src l qt_mid hlookup_mid
                        have hqt_mid : qt_src = qt_mid := by
                          rw [hlookup_src] at hlookup_preserved
                          exact Option.some.inj hlookup_preserved
                        have hmono_src : Regime.monotoneStep result1.regime' srcRes.regime' := by
                          exact
                            applyPFnTClosure_regime_mono
                              (tcl := PFnTClosure.regular x pbody tenv)
                              (ctx := ctx) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                              (r1 := result1) (r2 := srcRes) (fuel := fuelApp)
                              (IH := fun m _hlt e ctx' res' htc' =>
                                by
                                  simpa [typecheck] using regime_monotone ctx' e m res' htc')
                              happly_src
                        have hclean_mid : qtypCleanUnder result1.regime' qt_mid := by
                          simpa [hqt_mid] using
                            (cleanUnder_of_monotone hmono_src
                              (by simpa [ctxAfter] using hclean_src_ctx) :
                                qtypCleanUnder result1.regime' qt_src)
                        exact hbackToCtx qt_mid hlookup_mid hclean_mid
                    | extern x retSpec capturedEnv =>
                        exact False.elim <|
                          applyPFnTClosure_ioFree_extern_fails
                            ctx st1 st2 p p1 etyp2 p2 pred2 result1 fuelApp
                            x retSpec capturedEnv srcRes happly_src
                  rcases joinTypeResults_mem_contains_head_or_rest
                      ctx first rest res h_join l hcontains_res with
                    hhead | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                  · exact hmember_origin first (by simp) hhead
                  · exact hmember_origin srcRes (List.mem_cons_of_mem _ hsrc_rest) hsrc_contains
      | kwhile e1 e2 =>
          -- Permanently postponed: `kwhile` proofs are out of active scope for this work.
          sorry
      | rand e1 =>
          have htcRand : typecheckRand .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcRand (typecheckRand_ioFree_impossible ctx e1 fuel' res)
      | frand e1 =>
          have htcFrand : typecheckFrand .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcFrand (typecheckFrand_ioFree_impossible ctx e1 fuel' res)
      | printInt e1 =>
          have htcPrint : typecheckPrintInt .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcPrint (typecheckPrintInt_ioFree_impossible ctx e1 fuel' res)
      | printString e1 =>
          have htcPrint : typecheckPrintString .ioFree ctx e1 fuel' = .ok res := by
            simpa [typecheckExpr] using htc
          exact absurd htcPrint (typecheckPrintString_ioFree_impossible ctx e1 fuel' res)
      | externVal typ poison pred =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternVal, heq, bind, Except.bind] at htc
      | externFn arg argTyp retSpec effects =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternFn, heq, bind, Except.bind] at htc
      | externPfn arg argTyp retSpec =>
          have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
            native_decide
          simp [typecheckExpr, typecheckExternPfn, heq, bind, Except.bind] at htc

private lemma typecheckExpr_lookup_clean_back_of_pc_true
  (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
  (htc : typecheckExpr .ioFree ctx e fuel = .ok res)
  (hpc : ctx.pc = true) :
  ∀ (l : Loc) (qt_in qt_out : QTyp),
    ctx.memEnv.lookup l = some qt_in →
    res.memEnv'.lookup l = some qt_out →
    qtypCleanUnder res.regime' qt_out →
    qtypCleanUnder ctx.regime qt_in := by
  intro l qt_in qt_out hlookup_in hlookup_out hclean_out
  rcases typecheckExpr_clean_lookup_origin_of_pc_true
      (ctx := ctx) (e := e) (fuel := fuel) (res := res)
      htc hpc l qt_out hlookup_out hclean_out with
    ⟨qt_in', hlookup_in', hclean_in'⟩
  have hqt : qt_in' = qt_in := by
    rw [hlookup_in] at hlookup_in'
    exact Option.some.inj hlookup_in'.symm
  subst hqt
  exact hclean_in'

private lemma applyFnTClosure_fresh_lookup_not_clean_of_p1_true
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat) (tcl : FnTClosure) (r : TypeResult)
  (h_p1 : p1 = true)
  (l : Loc) (qt : QTyp)
  (hlookup_in : result2.memEnv'.lookup l = none)
  (happly :
    applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = .ok r)
  (hlookup_out : r.memEnv'.lookup l = some qt) :
  ¬ qtypCleanUnder r.regime' qt := by
  intro hclean_out
  cases fuel with
  | zero =>
      simp [applyFnTClosure] at happly
  | succ fuelBody =>
      cases tcl with
      | regular x body capturedEnv =>
          rcases applyFnTClosure_regular_inv
              ctx st1 st2 p p1 argEtyp argPoison argPred result2 fuelBody x body capturedEnv r happly with
            ⟨result3, htcBody, _hsub, hr⟩
          subst hr
          let bodyCtx : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc)
              memEnv := result2.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              tagEnv := result2.tagEnv'
              nextTag := result2.nextTag'
              nextLoc := result2.nextLoc'
              regime := result2.regime' }
          have hpc_body : bodyCtx.pc = true := by
            simp [bodyCtx, h_p1, joinPoison]
          have hlookup_result3 : result3.memEnv'.lookup l = some qt := by
            simpa using hlookup_out
          have hclean_result3 : qtypCleanUnder result3.regime' qt := by
            simpa using hclean_out
          rcases typecheckExpr_clean_lookup_origin_of_pc_true
              (ctx := bodyCtx) (e := body) (fuel := fuelBody) (res := result3)
              (htc := by simpa [bodyCtx] using htcBody)
              hpc_body l qt hlookup_result3 hclean_result3 with
            ⟨qt_in, hlookup_in_body, _hclean_in⟩
          have hlookup_in_result2 : result2.memEnv'.lookup l = some qt_in := by
            simpa [bodyCtx] using hlookup_in_body
          rw [hlookup_in] at hlookup_in_result2
          cases hlookup_in_result2
      | extern x retSpec effects capturedEnv =>
          exact False.elim <|
            applyFnTClosure_ioFree_extern_fails
              ctx st1 st2 p p1 argEtyp argPoison argPred result2
              (Nat.succ fuelBody) x retSpec effects capturedEnv r happly

private lemma joinTypeResults_poison_pred_of_head_true_noPred
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hfirst_poison : first.qualType.poison = true)
  (hfirst_pred : first.qualType.pred = Predicate.noPred) :
  res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred := by
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
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.2.1 = true →
        acc'.2.2.1 = true := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hacc
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
            have hacc1 : acc1.2.2.1 = true := by
              simp [acc1, hacc, joinPoison]
            exact ih (acc := acc1) hfold_tail hacc1
  have h_fold_pred :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.2.2.1 = Predicate.noPred →
        acc'.2.2.2.1 = Predicate.noPred := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hacc
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
            have hacc1 : acc1.2.2.2.1 = Predicate.noPred := by
              simp [acc1, hacc, joinPredicates]
            exact ih (acc := acc1) hfold_tail hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at h_join
      have hpoison : poison = true := by simpa [hqt] using hfirst_poison
      have hpred : pred = Predicate.noPred := by simpa [hqt] using hfirst_pred
      subst hpoison hpred
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
                (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have hpoison_a : a.2.2.1 = true :=
                h_fold_poison
                  rest
                  (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a
                  hfold rfl
              have hpred_a : a.2.2.2.1 = Predicate.noPred :=
                h_fold_pred
                  rest
                  (etyp, first.memEnv', true, Predicate.noPred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a
                  hfold rfl
              constructor
              · simp [joinPoison, hpoison_a]
              · cases a.1 <;> simp [hpred_a]

-- Synchronization helper for app/arrow clean branch.
-- Shape only for now: from clean output agreement on closure values, recover either
-- a shared regular-closure witness (with shared x/body) or explicit dirty-internal fallback.
private lemma stepFR_app_arrow_sync_from_clean
  (predSat : PredSat) (ctx : TypeContext) (res1 : TypeResult)
  (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap)
  (x₀ x₁ : Name) (body₀ body₁ : Expr) (env₀ env₁ : VarEnv)
  (hetyp : res1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
  (hclean : qtypCleanUnder (ctxAfter ctx res1).regime res1.qualType)
  (hagree :
    resultAgreesIfClean predSat (ctxAfter ctx res1).regime
      μ₀ μ₁ θ₀ θ₁ res1.qualType
      (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)) :
  (∃ σcap,
      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
      x₀ = x₁ ∧
      body₀ = body₁ ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁)
  ∨ (¬ internalPoisonClean res1.qualType) := by
  -- Unfold resultAgreesIfClean and apply hclean to get agreeValueUnder
  have h := hagree hclean
  -- Case-split on the agreeValueUnder evidence
  cases h with
  | clean_internal_arrow hci hetyp' htcl hmatch hcap hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ hv₁ hv₂ =>
    -- hetyp'  : res1.qualType.etyp = ETyp.arrow st1✝ st2✝ p✝ tcls✝  (fresh case vars)
    -- hetyp   : res1.qualType.etyp = ETyp.arrow st1  st2  p  tcls
    -- Combine to equate the two arrow types, then extract tcls✝ = tcls
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.arrow.injEq] at hetyp_combined
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hetyp_combined
    -- hv₁ : Value.closure x₀ body₀ env₀ = Value.closure x✝ body✝ ρcap₁✝
    -- hv₂ : Value.closure x₁ body₁ env₁ = Value.closure x✝ body✝ ρcap₂✝
    cases hv₁
    cases hv₂
    -- hmatch : tcl✝ = FnTClosure.regular x₀ body₀ σcap✝
    subst hmatch
    -- htcl : FnTClosure.regular x₀ body₀ σcap✝ ∈ tcls
    left
    exact ⟨_, htcl, rfl, rfl, hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁⟩
  | dirty_internal_arrow hdirty _ _ _ =>
    -- Internal poison is dirty: the right disjunct holds
    right; exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    -- Impossible: arrow is a function type, contradicts hnotfun
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_parrow _ hetyp' _ _ _ _ _ _ _ =>
    -- Impossible: parrow ≠ arrow
    exfalso
    have : ETyp.parrow _ _ _ _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_parrow _ hisParrow _ _ =>
    -- Impossible: arrow type is not isParrow; hisParrow reduces to false = true
    exfalso; simp [ETyp.isParrow, hetyp] at hisParrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ arrow
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    -- Impossible: arrow is a function type
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ arrow
    exfalso
    have : ETyp.ref _ = ETyp.arrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this

-- Synchronization helper for app/parrow clean branch.
-- Same intent as the arrow helper, but for pe-closures.
private lemma stepFR_app_parrow_sync_from_clean
  (predSat : PredSat) (ctx : TypeContext) (res1 : TypeResult)
  (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap)
  (x₀ x₁ : Name) (body₀ body₁ : Expr) (env₀ env₁ : VarEnv)
  (hetyp : res1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
  (hclean : qtypCleanUnder (ctxAfter ctx res1).regime res1.qualType)
  (hagree :
    resultAgreesIfClean predSat (ctxAfter ctx res1).regime
      μ₀ μ₁ θ₀ θ₁ res1.qualType
      (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)) :
  (∃ x pbody σcap,
      Expr.toPExpr? body₀ = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = body₁ ∧
      agreeCapturedEnv predSat (ctxAfter ctx res1).regime μ₀ μ₁ θ₀ θ₁ σcap env₀ env₁ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₀ σcap env₀ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₀ θ₀ σcap env₀ ∧
      MemberVarsRegimeEvidence predSat (ctxAfter ctx res1).regime μ₁ σcap env₁ ∧
      MemberCvcrEvidence predSat (ctxAfter ctx res1).regime μ₁ θ₁ σcap env₁)
  ∨ (¬ internalPoisonClean res1.qualType) := by
  -- Unfold resultAgreesIfClean and apply hclean to get agreeValueUnder
  have h := hagree hclean
  -- Case-split on the agreeValueUnder evidence
  cases h with
  | clean_internal_parrow hci hetyp' htcl hmatch hcap hmv₁ hmc₁ hmv₂ hmc₂ hv₁ hv₂ =>
    -- hetyp'  : res1.qualType.etyp = ETyp.parrow st1✝ st2✝ p✝ tcls✝  (fresh case vars)
    -- hetyp   : res1.qualType.etyp = ETyp.parrow st1  st2  p  tcls
    -- Combine to equate the two parrow types, then extract tcls✝ = tcls
    have hetyp_combined := hetyp'.symm.trans hetyp
    simp only [ETyp.parrow.injEq] at hetyp_combined
    obtain ⟨-, -, -, rfl⟩ := hetyp_combined   -- tcls✝ := tcls
    -- hv₁ : Value.peClosure x₀ body₀ env₀ = Value.peClosure x✝ body✝ ρcap₁✝
    -- hv₂ : Value.peClosure x₁ body₁ env₁ = Value.peClosure x✝ body✝ ρcap₂✝
    cases hv₁
    cases hv₂
    -- hmatch : Expr.toPExpr? body₀ = some pbody✝ ∧ tcl✝ = PFnTClosure.regular x₀ pbody✝ σcap✝
    obtain ⟨htoPExpr, rfl⟩ := hmatch   -- tcl✝ := PFnTClosure.regular x₀ pbody✝ σcap✝
    -- htcl : PFnTClosure.regular x₀ pbody✝ σcap✝ ∈ tcls
    left
    exact ⟨x₀, _, _, htoPExpr, htcl, rfl, rfl, rfl, hcap, hmv₁, hmc₁, hmv₂, hmc₂⟩
  | dirty_internal_parrow hdirty _ _ _ =>
    -- Internal poison is dirty: the right disjunct holds
    right; exact hdirty
  | clean_eq_nonref_nonarrow _ hnotfun _ _ =>
    -- Impossible: parrow is a function type, contradicts hnotfun
    -- After simp, hnotfun reduces to true = false
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | clean_internal_arrow _ hetyp' _ _ _ _ _ _ _ =>
    -- Impossible: arrow ≠ parrow
    exfalso
    have : ETyp.arrow _ _ _ _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | dirty_internal_arrow _ hisArrow _ _ =>
    -- Impossible: parrow type is not isArrow; hisArrow reduces to false = true
    exfalso; simp [ETyp.isArrow, hetyp] at hisArrow
  | clean_ref _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ parrow
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this
  | withPred_true_eq _ _ _ hnotfun _ _ =>
    -- Impossible: parrow is a function type
    exfalso; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow, hetyp] at hnotfun
  | withPred_true_ref _ _ _ hetyp' _ _ _ _ _ =>
    -- Impossible: ref ≠ parrow
    exfalso
    have : ETyp.ref _ = ETyp.parrow st1 st2 p tcls := hetyp'.symm.trans hetyp
    simp at this

private lemma stepFR_app_arrow_extract_shared_member
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List FnTClosure) (results : List TypeResult)
  (x₀ x₁ : Name) (body₀ body₁ : Expr)
  (hmap :
    List.mapM
      (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results)
  (hsync :
    ∃ σcap,
      FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
      x₀ = x₁ ∧
      body₀ = body₁) :
  ∃ σcap fuelBody first result3,
    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
    x₀ = x₁ ∧
    body₀ = body₁ ∧
    applyFnTClosure .ioFree (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
      argEtyp argPoison argPred ctx result1 fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result1.tagEnv'
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' } body₀ fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases hsync with ⟨σcap, hmem, hx, hbody⟩
  rcases applyFnTClosure_regular_inv_of_mapM_mem
      ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuel tcls results x₀ body₀ σcap
      hmap hmem with
    ⟨fuelBody, first, result3, happly, hfuel, htc, hsub, hfirst⟩
  exact ⟨σcap, fuelBody, first, result3, hmem, hx, hbody, happly, hfuel, htc, hsub, hfirst⟩

-- Pure-arrow analog of shared-member extraction.
private lemma stepFR_app_parrow_extract_shared_member
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result1 : TypeResult) (fuel : Nat)
  (tcls : List PFnTClosure) (results : List TypeResult)
  (x₀ x₁ : Name) (body₀ body₁ : Expr)
  (hmap :
    List.mapM
      (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 argEtyp argPoison argPred ctx result1 fuel)
      tcls = .ok results)
  (hsync :
    ∃ x pbody σcap,
      Expr.toPExpr? body₀ = some pbody ∧
      PFnTClosure.regular x pbody σcap ∈ tcls ∧
      x₀ = x ∧
      x₁ = x ∧
      body₀ = body₁) :
  ∃ x pbody σcap fuelBody first result3,
    Expr.toPExpr? body₀ = some pbody ∧
    PFnTClosure.regular x pbody σcap ∈ tcls ∧
    x₀ = x ∧
    x₁ = x ∧
    body₀ = body₁ ∧
    applyPFnTClosure .ioFree (PFnTClosure.regular x pbody σcap) st1 st2 p p1
      argEtyp argPoison argPred ctx result1 fuel = .ok first ∧
    fuel = Nat.succ fuelBody ∧
    typecheckExpr .ioFree
      { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1)
        memEnv := result1.memEnv'
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
        tagEnv := result1.tagEnv'
        pureCtx := true
        nextTag := result1.nextTag'
        nextLoc := result1.nextLoc'
        regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
    isSubtype st2 result3.qualType = true ∧
    first =
      { result3 with
        qualType :=
          normalizeAppResultByProvenance (joinPoison p1 p)
            { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
  rcases hsync with ⟨x, pbody, σcap, htoPExpr, hmem, hx₀, hx₁, hbody⟩
  rcases applyPFnTClosure_regular_inv_of_mapM_mem
      ctx st1 st2 p p1 argEtyp argPoison argPred result1 fuel tcls results x pbody σcap
      hmap hmem with
    ⟨fuelBody, first, result3, happly, hfuel, htc, hsub, hfirst⟩
  exact ⟨x, pbody, σcap, fuelBody, first, result3, htoPExpr, hmem, hx₀, hx₁, hbody,
         happly, hfuel, htc, hsub, hfirst⟩

-- Function application case: reduces to helper lemmas for closure/closure and peClosure branches
lemma stepFR_app
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.app e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.app e1 e2) res predSat tm := by
  -- Phase 1: Typecheck decomposition (typecheck = typecheckExpr; app case reduces to typecheckApp)
  have htcApp : typecheckApp .ioFree ctxᵢ e1 e2 (Nat.succ fuel') = .ok res := by
    rw [← typecheckExpr_app_succ .ioFree ctxᵢ e1 e2 (Nat.succ fuel')]
    simpa [typecheck] using htc
  obtain ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, h_arrow_or_parrow⟩ :=
    typecheckApp_arrow_structure_full ctxᵢ e1 e2 fuel' res htcApp
  cases h_arrow_or_parrow with
  | inl h_arrow =>
    -- Arrow case (closure)
    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, hp1, _hnpure, _hnempty, _hsub,
            hmap, heq_results, h_join⟩ := h_arrow
    have htc2' : typecheck .ioFree ctxᵢ e2 fuel' = .ok result2 := by
      simpa [typecheck] using htc2
    have htc1' : typecheck .ioFree (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
      simp [ctxAfter] at htc1 ⊢
      exact htc1
    intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2 (e1 IH defined after we have hTm2 from e2)
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    have hstruct₀ := terminatesTo_app_inv' e1 e2 cinit₀ cf₀ o₀ ht₀
    have hstruct₁ := terminatesTo_app_inv' e1 e2 cinit₁ cf₁ o₁ ht₁
    -- Handle runtime closure/peClosure splits for the arrow-typed branch.
    rcases hstruct₀ with h_clo₀ | h_peclo₀
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Both runs: closure
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        -- Phase A: Apply IH for e2
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        -- Phase B: Apply IH for e1
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        -- Phase C: Invert closure typing to extract FnTClosure structure
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        have hv₁1_arrow : valueHasETyp θ₁1 (Value.closure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        -- Invert closure typing for both runs
        cases hv₀1_arrow with
        | closure htcl₀ henv₀_typing hcover₀ =>
        cases hv₁1_arrow with
        | closure htcl₁ henv₁_typing hcover₁ =>
        -- Phase D: Extract body typing from applyFnTClosure via mapM membership
        rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₀ body₀ _ hmap htcl₀
          with ⟨fuelBody₀, first₀, result3₀, _happly₀, hfuel₀, htc_body₀, _hsub₀, hfirst₀_eq⟩
        rcases applyFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₁ body₁ _ hmap htcl₁
          with ⟨fuelBody₁, first₁, result3₁, _happly₁, hfuel₁, htc_body₁, _hsub₁, hfirst₁_eq⟩
        have hfirst₀_mem : first₀ ∈ results := by
          rcases applyFnTClosure_ok_of_mem_mapM
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            (FnTClosure.regular x₀ body₀ _) hmap htcl₀ with ⟨r, hr_mem, happly_r⟩
          have heq : r = first₀ := @Except.ok.inj String TypeResult r first₀ (by simpa [happly_r] using _happly₀)
          subst heq
          exact hr_mem
        have hfirst₁_mem : first₁ ∈ results := by
          rcases applyFnTClosure_ok_of_mem_mapM
            ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
            (FnTClosure.regular x₁ body₁ _) hmap htcl₁ with ⟨r, hr_mem, happly_r⟩
          have heq : r = first₁ := @Except.ok.inj String TypeResult r first₁ (by simpa [happly_r] using _happly₁)
          subst heq
          exact hr_mem
        -- Synchronization is used only under a clean-result assumption for `result1`.
        -- Keep it deferred to avoid requiring a global clean fact at this point.
        have _hsync1_of_clean :
              ∀ hclean1_e1 :
                  qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                (∃ σcap,
                    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                    x₀ = x₁ ∧
                    body₀ = body₁ ∧
                    agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory σcap env₀ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory θ₀1 σcap env₀ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory σcap env₁ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory θ₁1 σcap env₁)
                ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          exact
            stepFR_app_arrow_sync_from_clean
              (predSat := predSat)
              (ctx := (ctxAfter ctxᵢ result2))
              (res1 := result1)
              (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
              (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
              (θ₀ := θ₀1) (θ₁ := θ₁1)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              (env₀ := env₀) (env₁ := env₁)
              hetyp1 hclean1_e1 hres_agree1
        have _hextract_shared_of_sync :
            (∃ σcap,
                FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                x₀ = x₁ ∧
                body₀ = body₁) →
              ∃ σcap fuelBody first result3,
                FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                x₀ = x₁ ∧
                body₀ = body₁ ∧
                applyFnTClosure .ioFree (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
                  etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok first ∧
                fuel' = Nat.succ fuelBody ∧
                typecheckExpr .ioFree
                  { ctxᵢ with
                    pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                    memEnv := result1.memEnv'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                    tagEnv := result1.tagEnv'
                    nextTag := result1.nextTag'
                    nextLoc := result1.nextLoc'
                    regime := result1.regime' } body₀ fuelBody = .ok result3 ∧
                isSubtype st2 result3.qualType = true ∧
                first =
                  { result3 with
                    qualType :=
                      normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
          intro hsync
          exact
            stepFR_app_arrow_extract_shared_member
              (ctx := ctxᵢ)
              (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              hmap hsync
        have _sync_extract_of_clean :
            ∀ hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
                (∃ σcap fuelBody firstShared result3Shared,
                    FnTClosure.regular x₀ body₀ σcap ∈ tcls ∧
                    x₀ = x₁ ∧
                    body₀ = body₁ ∧
                    agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory σcap env₀ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₀.memory θ₀1 σcap env₀ ∧
                    MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory σcap env₁ ∧
                    MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      c₁₁.memory θ₁1 σcap env₁ ∧
                    applyFnTClosure .ioFree (FnTClosure.regular x₀ body₀ σcap) st1 st2 p p1
                      etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok firstShared ∧
                  fuel' = Nat.succ fuelBody ∧
                  typecheckExpr .ioFree
                    { ctxᵢ with
                      pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                      memEnv := result1.memEnv'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                      tagEnv := result1.tagEnv'
                      nextTag := result1.nextTag'
                      nextLoc := result1.nextLoc'
                      regime := result1.regime' } body₀ fuelBody = .ok result3Shared ∧
                  isSubtype st2 result3Shared.qualType = true ∧
                  firstShared =
                    { result3Shared with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) } })
              ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          rcases _hsync1_of_clean hclean1_e1 with hsync | hdirty
          · left
            rcases hsync with
              ⟨σcap, hmem, hx, hbody, hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁⟩
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₀ body₀ σcap hmap hmem with
              ⟨fuelBody, firstShared, result3Shared, happly', hfuel', htc', hsub', hfirst'⟩
            exact ⟨σcap, fuelBody, firstShared, result3Shared, hmem, hx, hbody, hcap,
              hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
              happly', hfuel', htc', hsub', hfirst'⟩
          · right
            exact hdirty
        -- htc_body₀ : typecheckExpr bodyCtx body₀ fuelBody₀ = .ok result3₀
        -- hfuel₀ : fuel' = Nat.succ fuelBody₀
        -- Phase E-G: Body IH application and final assembly.
        -- Option 2 (in progress): choose output realization maps before assembling
        -- the existential package, then discharge remaining fields under that choice.
        have hOutMapChoice :
            ∃ (θ₀_out θ₁_out : RealizationMap),
              wfExtendsMap θ₀ θ₀_out ∧
              wfExtendsMap θ₁ θ₁_out ∧
              (valueHasETyp θ₀_out o₀ res.qualType.etyp ∧
               valueHasETyp θ₁_out o₁ res.qualType.etyp ∧
               runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_out ∧
               runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_out ∧
               consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₀.memory cf₀.varEnv θ₀_out ∧
               consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₁.memory cf₁.varEnv θ₁_out ∧
               agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                 cf₀.memory cf₀.varEnv θ₀_out cf₁.memory cf₁.varEnv θ₁_out ∧
               valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                 res.qualType cf₀.memory θ₀_out o₀ ∧
               valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                 res.qualType cf₁.memory θ₁_out o₁ ∧
               resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                 cf₀.memory cf₁.memory θ₀_out θ₁_out res.qualType o₀ o₁) := by
          by_cases hclean1_e1 :
              qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
          · rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
            · rcases hshared with
                ⟨σcap, fuelBody, firstShared, result3Shared,
                  hmem, hx, hbody, hcap,
                  hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                  happly, hfuel, htcBody, hsubBody, hfirstShared⟩
              let bodyCtx : TypeContext :=
                { ctxᵢ with
                  pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                  memEnv := result1.memEnv'
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  tagEnv := result1.tagEnv'
                  nextTag := result1.nextTag'
                  nextLoc := result1.nextLoc'
                  regime := result1.regime' }
              have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
              have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
              have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
                have hfuel_lt' : fuelBody < fuel' := by
                  rw [hfuel]
                  exact Nat.lt_succ_self fuelBody
                exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
                have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                  simpa [hqt2] using (hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
                have hargTm' :
                    ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                      QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                      qtypGuardDesc? qt' = some (k, d) →
                      tm.lookup k = some d :=
                  QTypRespectsTagMeaning_transport_etyp_pred
                    (tm := tm)
                    (qt := ⟨etyp2, p2, pred2⟩)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    hresTm2_arg rfl rfl
                exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
              have hTmBody : wfTagMeaningCtx tm bodyCtx := by
                have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
                have hTmBody' :
                    wfTagMeaningCtx tm
                      { (ctxAfter ctxᵢ result2) with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ } :=
                  wfTagMeaningCtx_closure_body
                    (tm := tm)
                    (ctx := (ctxAfter ctxᵢ result2))
                    (result1 := result1)
                    (qtRes := result1.qualType)
                    (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
                    (xFun := x₀) (body := body₀) (σcap := σcap)
                    (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    hTm1 hresTm1' hetyp1 hmem hargTm
                simpa [bodyCtx, ctxAfter] using hTmBody'
              have htcBody' : typecheck .ioFree bodyCtx body₀ fuelBody = .ok result3Shared := by
                simpa [bodyCtx, typecheck] using htcBody
              have hIH_body :=
                IH fuelBody hfuel_lt body₀ bodyCtx hTmBody result3Shared htcBody'
              have hwfBodyCtx : wfTypeContext bodyCtx := by
                simpa [bodyCtx, ctxAfter, wfTypeContext] using hwf1
              have hric_body₀ :
                  runtimeInstantiatesCtx bodyCtx c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
                let ctxCapBase : TypeContext :=
                  { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
                have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                  simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
                have hric_cap_base :
                    runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) c₁₀.memory env₀ θ₀1 := by
                  constructor
                  · intro l a hlookup
                    exact hric₀1.1 l a hlookup
                  · intro y qt hlookup
                    exact
                      agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y qt hlookup
                have hric_body₀' :
                    runtimeInstantiatesCtx
                      { ctxCapBase with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                      c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                  runtimeInstantiatesCtx_closure_body
                    (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (argVal := v₂₀) (μ := c₁₀.memory) (ρ := env₀) (θ := θ₀1)
                    hric_cap_base harg₀_typed
                    (agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap))
                simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body₀'
              have hric_body₁ :
                  runtimeInstantiatesCtx bodyCtx c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                let ctxCapBase : TypeContext :=
                  { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
                have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                  simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
                have hric_cap_base :
                    runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) c₁₁.memory env₁ θ₁1 := by
                  constructor
                  · intro l a hlookup
                    exact hric₁1.1 l a hlookup
                  · intro y qt hlookup
                    exact
                      agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y qt hlookup
                have hric_body₁' :
                    runtimeInstantiatesCtx
                      { ctxCapBase with
                        memEnv := result1.memEnv'
                        tagEnv := result1.tagEnv'
                        nextLoc := result1.nextLoc'
                        nextTag := result1.nextTag'
                        regime := result1.regime'
                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 :=
                  runtimeInstantiatesCtx_closure_body
                    (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (argVal := v₂₁) (μ := c₁₁.memory) (ρ := env₁) (θ := θ₁1)
                    hric_cap_base harg₁_typed
                    (agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap))
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter, henv_update]
                  using hric_body₁'
              have h_mono1 :
                  Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
                regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
              have htagR_body : regimeConsistentWithCtx bodyCtx := by
                simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
              have hRbound_body : regimeBounded bodyCtx.regime := by
                exact
                  regimeBounded_of_monotoneStep
                    (ctxAfter ctxᵢ result2).regime result1.regime'
                    hRbound2 h_mono1
              have hcwr_body₀ :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
                have hlocs_src₀ :
                    ∀ l qt k,
                      result1.memEnv'.lookup l = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      locsRegime predSat result1.regime' c₁₀.memory θ₀1 (l, qt) := by
                  intro l qt k hlookup hguard hRdef
                  exact hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
                have hvars_cap₀ :
                    ∀ x qt k,
                      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₀.memory env₀ (x, qt) := by
                  intro x qt k hlookup hguard hRdef
                  rcases
                      agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap) x qt hlookup
                    with ⟨v, hlookup_v, _htyp_v⟩
                  exact hmemberVars₀ x qt k v hlookup hlookup_v hguard hRdef
                have hvars_arg₀ :
                    ∀ k,
                      qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₀.memory
                        (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  intro k hguard hRdef
                  have hvalc_arg_e2 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ := by
                    have hvalc₂ :
                        valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                          result2.qualType c₂'₀.memory θ₀2 v₂₀ := by
                      simpa [ctxAfter] using _hvalc₂₀
                    exact
                      valueConsistentWithRegime_transport_pred
                        (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                        (qt := result2.qualType)
                        (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                        (by simp [hqt2]) (hetyp := by simp [hqt2])
                        hvalc₂
                  have hvalc_arg_e1 :
                      valueConsistentWithRegime predSat result1.regime'
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                    valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                  have hlookup_v_body :
                      (env₀.update x₀ v₂₀).lookup x₀ = some v₂₀ := by
                    simp [VarEnv.update, VarEnv.lookup]
                  have hvars_arg_e1R_mem₂ :
                      varsRegime predSat result1.regime' c₂'₀.memory
                        (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                    exact
                      varsRegime_of_valueConsistentWithRegime_active
                        (predSat := predSat) (R := result1.regime')
                        (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                        (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (v := v₂₀) (k := k)
                        hlookup_v_body hguard hRdef hvalc_arg_e1
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                    predSat_mem_noPred_compat hpredlaws θ₀1
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value),
                        qtypPredHolds predSat qt c₂'₀.memory v ↔ qtypPredHolds predSat qt c₁₀.memory v := by
                    intro qt v
                    constructor <;> intro h
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).1 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).1 hs)
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).2 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₀.memory c₁₀.memory v).2 hs)
                  exact
                    varsRegime_transport_predHolds
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (μ' := c₁₀.memory)
                      (ρ := env₀.update x₀ v₂₀)
                      (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                      hqtypPredHolds_mem hvars_arg_e1R_mem₂
                exact
                  consistentWithRegime_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₁₀.memory) (θ := θ₀1) (ρcap := env₀) (vArg := v₂₀)
                    hlocs_src₀ hvars_cap₀ hvars_arg₀
                      hmemberCvcr₀
                    (closureCapturedVarsRegime_transport_μ_θ
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory c₁₀.memory)
                      hθext₀1.1
                      (closureCapturedVarsRegime_monotone h_mono1
                        (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                          (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₀))))
              have hcwr_body₁ :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                have hlocs_src₁ :
                    ∀ l qt k,
                      result1.memEnv'.lookup l = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      locsRegime predSat result1.regime' c₁₁.memory θ₁1 (l, qt) := by
                  intro l qt k hlookup hguard hRdef
                  exact hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
                have hvars_cap₁ :
                    ∀ x qt k,
                      (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                      qtypGuardTag qt = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₁.memory env₁ (x, qt) := by
                  intro x qt k hlookup hguard hRdef
                  rcases
                      agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap) x qt hlookup
                    with ⟨v, hlookup_v, _htyp_v⟩
                  exact hmemberVars₁ x qt k v hlookup hlookup_v hguard hRdef
                have hvars_arg₁ :
                    ∀ k,
                      qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                      result1.regime'.lookup? k ≠ none →
                      varsRegime predSat result1.regime' c₁₁.memory
                        (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  intro k hguard hRdef
                  have hvalc_arg_e2 :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ := by
                    have hvalc₂ :
                        valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                          result2.qualType c₂'₁.memory θ₁2 v₂₁ := by
                      simpa [ctxAfter] using _hvalc₂₁
                    exact
                      valueConsistentWithRegime_transport_pred
                        (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                        (qt := result2.qualType)
                        (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                        (by simp [hqt2]) (hetyp := by simp [hqt2])
                        hvalc₂
                  have hvalc_arg_e1 :
                      valueConsistentWithRegime predSat result1.regime'
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                    valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                  have hlookup_v_body :
                      (env₁.update x₀ v₂₁).lookup x₀ = some v₂₁ := by
                    simp [VarEnv.update, VarEnv.lookup]
                  have hvars_arg_e1R_mem₂ :
                      varsRegime predSat result1.regime' c₂'₁.memory
                        (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                    exact
                      varsRegime_of_valueConsistentWithRegime_active
                        (predSat := predSat) (R := result1.regime')
                        (μ := c₂'₁.memory) (ρ := env₁.update x₀ v₂₁)
                        (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                        (v := v₂₁) (k := k)
                        hlookup_v_body hguard hRdef hvalc_arg_e1
                  have hPredSat_mem :
                      ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                    predSat_mem_noPred_compat hpredlaws θ₁1
                  have hqtypPredHolds_mem :
                      ∀ (qt : QTyp) (v : Value),
                        qtypPredHolds predSat qt c₂'₁.memory v ↔ qtypPredHolds predSat qt c₁₁.memory v := by
                    intro qt v
                    constructor <;> intro h
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).1 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).1 hs)
                    · cases h with
                      | noPred_ok hp =>
                          exact qtypPredHolds.noPred_ok hp
                      | guardClosure_ok hp hs =>
                          exact qtypPredHolds.guardClosure_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).2 hs)
                      | guardOnly_ok hp hs =>
                          exact qtypPredHolds.guardOnly_ok hp
                            ((hPredSat_mem _ c₂'₁.memory c₁₁.memory v).2 hs)
                  exact
                    varsRegime_transport_predHolds
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (μ' := c₁₁.memory)
                      (ρ := env₁.update x₀ v₂₁)
                      (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                      hqtypPredHolds_mem hvars_arg_e1R_mem₂
                have hcwr_body₁' :
                    consistentWithRegime predSat bodyCtx.regime bodyCtx
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                  exact
                    consistentWithRegime_closure_body_start
                      (predSat := predSat)
                      (ctx := ctxᵢ) (result1 := result1)
                      (σcap := σcap) (xArg := x₀)
                      (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₁₁.memory) (θ := θ₁1) (ρcap := env₁) (vArg := v₂₁)
                      hlocs_src₁ hvars_cap₁ hvars_arg₁
                      hmemberCvcr₁
                      (closureCapturedVarsRegime_transport_μ_θ
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory c₁₁.memory)
                        hθext₁1.1
                        (closureCapturedVarsRegime_monotone h_mono1
                          (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                            (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₁))))
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [henv_update] using hcwr_body₁'
              have hagree_body_start :
                  agreeOnClean predSat bodyCtx.regime bodyCtx
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
                have hmem_agree :
                    ∀ l qt,
                      result1.memEnv'.lookup l = some qt →
                      qtypCleanUnder result1.regime' qt →
                      agreeLocUnder predSat result1.regime' c₁₀.memory c₁₁.memory θ₀1 θ₁1 (l, qt) := by
                  intro l qt hlookup hclean
                  exact hagree1.1 l qt (by simpa [ctxAfter] using hlookup) hclean
                have hagree_body_start' :
                    agreeOnClean predSat bodyCtx.regime bodyCtx
                      c₁₀.memory (env₀.update x₀ v₂₀) θ₀1
                      c₁₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                  have harg_agree :
                      qtypCleanUnder result1.regime' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                        agreeValueUnder predSat result1.regime'
                          c₁₀.memory c₁₁.memory θ₀1 θ₁1
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                    intro hclean_arg
                    have hclean_arg_e2 :
                        qtypCleanUnder (ctxAfter ctxᵢ result2).regime
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                      cleanUnder_of_monotone h_mono1 hclean_arg
                    have hclean_res2 :
                        qtypCleanUnder (ctxAfter ctxᵢ result2).regime result2.qualType := by
                      cases hclean_arg_e2 with
                      | clean hpoison =>
                          have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                            simpa using hpoison
                          exact qtypCleanUnder.clean (by simpa [hqt2] using (joinPoison_eq_false hjoin).2)
                      | guard k htag hk hnotfun =>
                          have htag' : qtypGuardTag result2.qualType = some k := by
                            simpa [hqt2, qtypGuardTag] using htag
                          have hnotfun' : result2.qualType.etyp.isFunctionType = false := by
                            simpa [hqt2] using hnotfun
                          exact qtypCleanUnder.guard k htag' hk hnotfun'
                    have hagree_res2 :
                        agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2 result2.qualType v₂₀ v₂₁ :=
                      hres_agree2 hclean_res2
                    have hagree_arg_e2 :
                        agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                      refine agreeValueUnder_transport_clean hclean_arg_e2 ?_ ?_ hagree_res2
                      · simp [hqt2]
                      · intro hpoison
                        have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                          simpa using hpoison
                        exact by simpa [hqt2] using (joinPoison_eq_false hjoin).2
                    have hagree_arg_e2_to_e1 :
                        agreeValueUnder predSat result1.regime'
                          c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                          ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ :=
                      agreeValueUnder_clean_monotoneRegime h_mono1 hclean_arg hagree_arg_e2
                    have hqtypPredHolds_mem_app_arg₀ :
                        ∀ (qt' : QTyp) (v' : Value),
                          qtypPredHolds predSat qt' c₂'₀.memory v' ↔
                            qtypPredHolds predSat qt' c₁₀.memory v' :=
                      qtypPredHolds_mem_compat_of_predSatLaws
                        (hpredlaws := hpredlaws) (θ := θ₀2) (μ := c₂'₀.memory) (μ' := c₁₀.memory)
                    have hqtypPredHolds_mem_app_arg₁ :
                        ∀ (qt' : QTyp) (v' : Value),
                          qtypPredHolds predSat qt' c₂'₁.memory v' ↔
                            qtypPredHolds predSat qt' c₁₁.memory v' :=
                      qtypPredHolds_mem_compat_of_predSatLaws
                        (hpredlaws := hpredlaws) (θ := θ₁2) (μ := c₂'₁.memory) (μ' := c₁₁.memory)
                    exact
                      agreeValueUnder_clean_extends_transport_mem
                        hqtypPredHolds_mem_app_arg₀ hqtypPredHolds_mem_app_arg₁
                        hclean_arg hθext₀1.1 hθext₁1.1 hagree_arg_e2_to_e1
                  exact
                    agreeOnClean_closure_body_start
                      (predSat := predSat)
                      (ctx := ctxᵢ) (result1 := result1)
                      (σcap := σcap) (xArg := x₀)
                      (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
                      (θ₀ := θ₀1) (θ₁ := θ₁1)
                      (ρcap₀ := env₀) (ρcap₁ := env₁)
                      (vArg₀ := v₂₀) (vArg₁ := v₂₁)
                      hmem_agree hcap harg_agree
                have hx' : x₁ = x₀ := by simpa using hx.symm
                have henv_update :
                    env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                  simp [hx']
                simpa [henv_update] using hagree_body_start'
              have hwfcfg_body_init₀ :
                  wfConfig
                    { memory := c₁₀.memory
                      varEnv := env₀.update x₀ v₂₀
                      nextAddr := c₁₀.nextAddr
                      pureMode := false } := by
                have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                  (wfConfig_preserved .ioFree e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
                have hnext₂_to₁ : c₂'₀.nextAddr ≤ c₁₀.nextAddr :=
                  terminatesTo_nextAddr_mono .ioFree e1 c₂'₀ c₁₀ (Value.closure x₀ body₀ env₀) ht₀_e1
                have hv₂₀_wf : wfValue c₁₀.nextAddr v₂₀ :=
                  wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
                have hv₀_closure_wf : wfValue c₁₀.nextAddr (Value.closure x₀ body₀ env₀) :=
                  (wfConfig_preserved .ioFree e1 _ c₁₀ _ ht₀_e1 hwfcf₂₀).2
                have henv₀_wf : wfVarEnv c₁₀.nextAddr env₀ := by
                  cases hv₀_closure_wf with
                  | closure _ _ _ henv => exact henv
                constructor
                · intro a ha
                  exact hwfcf₁₀.1 a ha
                · simpa [VarEnv.update] using (wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf)
              have hwfcfg_body_init₁ :
                  wfConfig
                    { memory := c₁₁.memory
                      varEnv := env₁.update x₁ v₂₁
                      nextAddr := c₁₁.nextAddr
                      pureMode := false } := by
                have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                  (wfConfig_preserved .ioFree e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
                have hnext₂_to₁ : c₂'₁.nextAddr ≤ c₁₁.nextAddr :=
                  terminatesTo_nextAddr_mono .ioFree e1 c₂'₁ c₁₁ (Value.closure x₁ body₁ env₁) ht₁_e1
                have hv₂₁_wf : wfValue c₁₁.nextAddr v₂₁ :=
                  wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
                have hv₁_closure_wf : wfValue c₁₁.nextAddr (Value.closure x₁ body₁ env₁) :=
                  (wfConfig_preserved .ioFree e1 _ c₁₁ _ ht₁_e1 hwfcf₂₁).2
                have henv₁_wf : wfVarEnv c₁₁.nextAddr env₁ := by
                  cases hv₁_closure_wf with
                  | closure _ _ _ henv => exact henv
                constructor
                · intro a ha
                  exact hwfcf₁₁.1 a ha
                · simpa [VarEnv.update] using (wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf)
              have hwfcfg_body_final₀ : wfConfig evalCfg₀ := by
                exact (wfConfig_preserved .ioFree body₀ _ evalCfg₀ o₀ ht₀_body hwfcfg_body_init₀).1
              have hwfcfg_body_final₁ : wfConfig evalCfg₁ := by
                exact (wfConfig_preserved .ioFree body₁ _ evalCfg₁ o₁ ht₁_body hwfcfg_body_init₁).1
              have ht₀_body' :
                  terminatesTo .ioFree body₀
                    { memory := c₁₀.memory
                      varEnv := env₀.update x₀ v₂₀
                      nextAddr := c₁₀.nextAddr
                      pureMode := false } evalCfg₀ o₀ := by
                simpa using ht₀_body
              have ht₁_body' :
                  terminatesTo .ioFree body₀
                    { memory := c₁₁.memory
                      varEnv := env₁.update x₁ v₂₁
                      nextAddr := c₁₁.nextAddr
                      pureMode := false } evalCfg₁ o₁ := by
                simpa [hbody] using ht₁_body
              have hstep_body := hIH_body hpredlaws hTmBody
                c₁₀.memory c₁₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
                evalCfg₀ evalCfg₁ o₀ o₁
                hθ₀1wf hθ₁1wf hwfBodyCtx hric_body₀ hric_body₁ htagR_body hRbound_body
                hcwr_body₀ hcwr_body₁ hagree_body_start
                c₁₀.nextAddr c₁₁.nextAddr false
                hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
              rcases hstep_body with
                ⟨_hresTm_body,
                  ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                    _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after,
                    _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                    _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                    _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                    _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩⟩
              have hAgree_out_body :
                  agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                have hsrc_mem : firstShared ∈ first :: rest := by
                  rcases applyFnTClosure_ok_of_mem_mapM
                      (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result2 := result1) (fuel := fuel')
                      (tcls := tcls) (results := results)
                      (tcl := FnTClosure.regular x₀ body₀ σcap)
                      hmap hmem with
                    ⟨r, hr_mem, happly_r⟩
                  have hr_eq : r = firstShared := by
                    have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                      simpa [happly_r] using happly
                    exact Except.ok.inj hEq
                  subst hr_eq
                  simpa [heq_results] using hr_mem
                have hagree_src :
                    agreeOnClean predSat (ctxAfter ctxᵢ firstShared).regime (ctxAfter ctxᵢ firstShared)
                      cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                  have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                    regime_monotone bodyCtx body₀ fuelBody result3Shared htcBody'
                  have hres1_to_src_mono :
                      Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                        (ctxAfter ctxᵢ firstShared).regime := by
                    simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  constructor
                  · intro l qt hlookup hclean
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hclean_body :
                        qtypCleanUnder (ctxAfter bodyCtx result3Shared).regime qt := by
                      simpa [ctxAfter, hfirstShared] using hclean
                    have hloc_agree_body := hagree_body_after.1 l qt hlookup_body hclean_body
                    cases hloc_agree_body with
                    | both_unrealized _ _ hnone₀ hnone₁ =>
                        exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                    | agree_values _ _ a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                        have hlookup₀' : cf₀.memory.lookup a₀' = some n₀ := by
                          simpa [hmem₀_eq] using hlookup₀
                        have hlookup₁' : cf₁.memory.lookup a₁' = some n₁ := by
                          simpa [hmem₁_eq] using hlookup₁
                        have hagree_val' :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₁.memory θ₀_body θ₁_body qt
                              (Value.num n₀) (Value.num n₁) := by
                          simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hagree_val
                        exact
                          agreeLocUnder.agree_values l qt a₀' a₁' n₀ n₁
                            hreal₀ hreal₁ hlookup₀' hlookup₁' hagree_val'
                  · intro x qt hlookup hclean
                    have hclean_res1 :
                        qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime qt :=
                      cleanUnder_of_monotone hres1_to_src_mono hclean
                    have hvar_agree1 := hagree1.2 x qt hlookup hclean_res1
                    cases hvar_agree1 with
                    | both_none _ _ hnone₀ hnone₁ =>
                        have hnone₀' : cf₀.varEnv.lookup x = none := by
                          simpa [hvar₀_eq] using hnone₀
                        have hnone₁' : cf₁.varEnv.lookup x = none := by
                          simpa [hvar₁_eq] using hnone₁
                        exact agreeVarUnder.both_none x qt hnone₀' hnone₁'
                    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree_val1 =>
                        have hlookup₀' : cf₀.varEnv.lookup x = some v₀ := by
                          simpa [hvar₀_eq] using hlookup₀
                        have hlookup₁' : cf₁.varEnv.lookup x = some v₁ := by
                          simpa [hvar₁_eq] using hlookup₁
                        have hagree_src_regime :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              c₁₀.memory c₁₁.memory θ₀1 θ₁1 qt v₀ v₁ :=
                          agreeValueUnder_clean_monotoneRegime hres1_to_src_mono hclean hagree_val1
                        have hagree_src_final :
                            agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₁.memory θ₀_body θ₁_body qt v₀ v₁ :=
                          by
                            have hqtypPredHolds_mem_app_out₀ :
                                ∀ (qt' : QTyp) (v' : Value),
                                  qtypPredHolds predSat qt' c₁₀.memory v' ↔
                                    qtypPredHolds predSat qt' cf₀.memory v' :=
                              qtypPredHolds_mem_compat_of_predSatLaws
                                (hpredlaws := hpredlaws) (θ := θ₀1)
                                (μ := c₁₀.memory) (μ' := cf₀.memory)
                            have hqtypPredHolds_mem_app_out₁ :
                                ∀ (qt' : QTyp) (v' : Value),
                                  qtypPredHolds predSat qt' c₁₁.memory v' ↔
                                    qtypPredHolds predSat qt' cf₁.memory v' :=
                              qtypPredHolds_mem_compat_of_predSatLaws
                                (hpredlaws := hpredlaws) (θ := θ₁1)
                                (μ := c₁₁.memory) (μ' := cf₁.memory)
                            exact
                              agreeValueUnder_clean_extends_transport_mem
                                hqtypPredHolds_mem_app_out₀ hqtypPredHolds_mem_app_out₁
                                hclean _hθext₀_body.1 _hθext₁_body.1 hagree_src_regime
                        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀' hlookup₁' hagree_src_final
                have h_clean_res_to_src :
                    ∀ qt,
                      qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                      qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt := by
                  intro qt hclean
                  cases hclean with
                  | clean hpoison =>
                      exact qtypCleanUnder.clean hpoison
                  | guard k htag hk hnotfun =>
                      have hk_src :
                          (ctxAfter ctxᵢ firstShared).regime.lookup? k = some true :=
                        joinTypeResults_lookup_member_regime_compat
                          (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                          h_join hsrc_mem k true hk
                      exact qtypCleanUnder.guard k htag hk_src hnotfun
                have h_mem_from_src_or_unrealized :
                    ∀ l qt,
                      (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
                      qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                      ((∃ qt_src,
                          (ctxAfter ctxᵢ firstShared).memEnv.lookup l = some qt_src ∧
                          qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src ∧
                          qt.etyp = qt_src.etyp ∧
                          (qt.poison = false → qt_src.poison = false)) ∨
                        (θ₀_body.lookup l = none ∧ θ₁_body.lookup l = none)) := by
                  intro l qt hlookup hclean
                  by_cases hlookup_src_none : (ctxAfter ctxᵢ firstShared).memEnv.lookup l = none
                  · right
                    have hlookup_body_none :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = none := by
                      simpa [ctxAfter, hfirstShared] using hlookup_src_none
                    have hnot_contains_body :
                        ¬ (ctxAfter bodyCtx result3Shared).memEnv.contains l := by
                      intro hcontains
                      have hmem : l ∈ (ctxAfter bodyCtx result3Shared).memEnv :=
                        (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                      have hlookup_isSome :
                          ((ctxAfter bodyCtx result3Shared).memEnv[l]?).isSome = true :=
                        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                      have hlookup_get_none :
                          (ctxAfter bodyCtx result3Shared).memEnv[l]? = none := by
                        simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup_body_none
                      simp [hlookup_get_none] at hlookup_isSome
                    have htheta₀_none :
                        θ₀_body.lookup l = none :=
                      theta_not_contains_if_not_in_memEnv
                        (ctx := (ctxAfter bodyCtx result3Shared))
                        (μ := evalCfg₀.memory) (ρ := evalCfg₀.varEnv) (θ := θ₀_body)
                        (l := l) _hric_body_final₀ hnot_contains_body
                    have htheta₁_none :
                        θ₁_body.lookup l = none :=
                      theta_not_contains_if_not_in_memEnv
                        (ctx := (ctxAfter bodyCtx result3Shared))
                        (μ := evalCfg₁.memory) (ρ := evalCfg₁.varEnv) (θ := θ₁_body)
                        (l := l) _hric_body_final₁ hnot_contains_body
                    exact ⟨htheta₀_none, htheta₁_none⟩
                  · left
                    rcases Option.ne_none_iff_exists'.1 hlookup_src_none with ⟨qt_src, hlookup_src⟩
                    have hclean_src : qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src :=
                      joinTypeResults_lookup_member_clean_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hclean hlookup_src
                    have hetyp_eq : qt.etyp = qt_src.etyp :=
                      joinTypeResults_lookup_member_etyp_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hlookup_src
                    have hpoison_imp : qt.poison = false → qt_src.poison = false :=
                      joinTypeResults_lookup_member_poison_imp
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem l qt qt_src hlookup hlookup_src
                    exact ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
                have hlookup_back_res_to_src :
                    ∀ k b,
                      (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                      (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b := by
                  intro k b hk
                  exact
                    joinTypeResults_lookup_member_regime_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem k b hk
                exact
                  join_transport_agreeOnClean_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ)
                    (first := first)
                    (src := firstShared)
                    (rest := rest)
                    (res := res)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                    (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                    (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                    h_join hsrc_mem hagree_src h_clean_res_to_src h_mem_from_src_or_unrealized
                    (fun {σcap} {ρcap} h =>
                      memberVarsRegimeEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₀.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberCvcrEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₀.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberVarsRegimeEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₁.memory)
                        hlookup_back_res_to_src h)
                    (fun {σcap} {ρcap} h =>
                      memberCvcrEvidence_transport_lookup_back
                        (predSat := predSat)
                        (R := (ctxAfter ctxᵢ firstShared).regime)
                        (R' := (ctxAfter ctxᵢ res).regime)
                        (μ := cf₁.memory)
                        hlookup_back_res_to_src h)
              have hOutPack_body :
                  valueHasETyp θ₀_body o₀ res.qualType.etyp ∧
                  valueHasETyp θ₁_body o₁ res.qualType.etyp ∧
                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_body ∧
                  runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_body ∧
                  consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body ∧
                  consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₁.memory cf₁.varEnv θ₁_body ∧
                  agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body ∧
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                    res.qualType cf₀.memory θ₀_body o₀ ∧
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                    res.qualType cf₁.memory θ₁_body o₁ ∧
                  resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                    cf₀.memory cf₁.memory θ₀_body θ₁_body res.qualType o₀ o₁ := by
                have hsrc_mem' : firstShared ∈ first :: rest := by
                  rcases applyFnTClosure_ok_of_mem_mapM
                      (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                      (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                      (result2 := result1) (fuel := fuel')
                      (tcls := tcls) (results := results)
                      (tcl := FnTClosure.regular x₀ body₀ σcap)
                      hmap hmem with
                    ⟨r, hr_mem, happly_r⟩
                  have hr_eq : r = firstShared := by
                    have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                      simpa [happly_r] using happly
                    exact Except.ok.inj hEq
                  subst hr_eq
                  simpa [heq_results] using hr_mem
                have hfirstShared_etyp : firstShared.qualType.etyp = result3Shared.qualType.etyp := by
                  rw [hfirstShared]; unfold normalizeAppResultByProvenance; split_ifs <;> rfl
                have hres1_to_src_mono :
                    Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      (ctxAfter ctxᵢ firstShared).regime := by
                  have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                    regime_monotone bodyCtx body₀ fuelBody result3Shared htcBody'
                  simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                have hlookup_back_res1_to_src :
                    ∀ k b,
                      (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
                  intro k b hk_src
                  have hRdef_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k ≠ none := by
                    intro hnone
                    rw [hk_src] at hnone
                    contradiction
                  have hRdef_res1 :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                    hres1_to_src_mono.2.2 k hRdef_src
                  cases hk_res1 : (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
                  | none =>
                      exact False.elim (hRdef_res1 hk_res1)
                  | some b1 =>
                      have hcases := hres1_to_src_mono.2.1 k b1 hk_res1
                      cases hcases with
                      | inl hk_src' =>
                          have hb_eq : b1 = b := by
                            have : some b1 = some b := by
                              calc
                                some b1 = (ctxAfter ctxᵢ firstShared).regime.lookup? k := hk_src'.symm
                                _ = some b := hk_src
                            exact Option.some.inj this
                          simp [hb_eq]
                      | inr hnone_src =>
                          rw [hnone_src] at hk_src
                          cases hk_src
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAgree_out_body, ?_, ?_, ?_⟩
                · -- shared-member valueHasETyp -> joined valueHasETyp (run 0).
                  have hv_src₀ : valueHasETyp θ₀_body o₀ firstShared.qualType.etyp := by
                    rw [hfirstShared_etyp]
                    exact _hv_body₀_typed
                  exact
                    joinTypeResults_transport_valueHasETyp_from_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (θ := θ₀_body) (v := o₀)
                      h_join hsrc_mem' hv_src₀
                · -- shared-member valueHasETyp -> joined valueHasETyp (run 1).
                  have hv_src₁ : valueHasETyp θ₁_body o₁ firstShared.qualType.etyp := by
                    rw [hfirstShared_etyp]
                    exact _hv_body₁_typed
                  exact
                    joinTypeResults_transport_valueHasETyp_from_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (θ := θ₁_body) (v := o₁)
                      h_join hsrc_mem' hv_src₁
                · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hsrc_mem_to_res :
                      ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                    joinTypeResults_mem_contains_of_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem'
                  constructor
                  · intro l a hθ
                    have hloc_src := _hric_body_final₀.1 l a hθ
                    rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                    have hcontains_src : firstShared.memEnv'.contains l := by
                      simpa [ctxAfter, hfirstShared] using hcontains_src_body
                    refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                    simpa [hmem₀_eq] using hmem_contains
                  · intro x qt hlookup
                    have hlookup_ctx :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                      simpa [ctxAfter] using hlookup
                    rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                    refine ⟨v, ?_⟩
                    constructor
                    · simpa [hvar₀_eq] using hlookup_v
                    · exact valueHasETyp_extends _hθext₀_body.1 hv_typ
                · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  have hsrc_mem_to_res :
                      ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                    joinTypeResults_mem_contains_of_member
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem'
                  constructor
                  · intro l a hθ
                    have hloc_src := _hric_body_final₁.1 l a hθ
                    rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                    have hcontains_src : firstShared.memEnv'.contains l := by
                      simpa [ctxAfter, hfirstShared] using hcontains_src_body
                    refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                    simpa [hmem₁_eq] using hmem_contains
                  · intro x qt hlookup
                    have hlookup_ctx :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                      simpa [ctxAfter] using hlookup
                    rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                    refine ⟨v, ?_⟩
                    constructor
                    · simpa [hvar₁_eq] using hlookup_v
                    · exact valueHasETyp_extends _hθext₁_body.1 hv_typ
                · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by
                    simp [heq_cfg₀]
                  have hpred_compat₀ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₀.memory v' ↔
                          qtypPredHolds predSat qt' cf₀.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₀1)
                      (μ := c₁₀.memory) (μ' := cf₀.memory)
                  have hcwr_src₀ :
                      consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        (ctxAfter ctxᵢ firstShared) cf₀.memory cf₀.varEnv θ₀_body := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro l qt k hlookup hguard hRdef
                      have hlookup_body :
                          (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                        simpa [ctxAfter, hfirstShared] using hlookup
                      have hguard_body : qtypGuardTag qt = some k := by
                        simpa [ctxAfter, hfirstShared] using hguard
                      have hRdef_body :
                          (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                        simpa [ctxAfter, hfirstShared] using hRdef
                      have hloc_body :=
                        _hcwr_body_final₀.1 l qt k hlookup_body hguard_body hRdef_body
                      simpa [ctxAfter, hfirstShared, hmem₀_eq] using hloc_body
                    · intro x qt k hlookup hguard hRdef
                      cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                      | none =>
                          exact False.elim (hRdef hk_src)
                      | some b =>
                          have hRdef_res1 :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                            intro hnone
                            have hk_back := hlookup_back_res1_to_src k b hk_src
                            rw [hk_back] at hnone
                            contradiction
                          have hlookup_res1_ctx :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                            simpa [ctxAfter] using hlookup
                          have hvar_res1 :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                c₁₀.memory c₁₀.varEnv (x, qt) :=
                            hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                          have hvar_res1_mem :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                cf₀.memory c₁₀.varEnv (x, qt) :=
                            varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                          have hvar_src :
                              varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                                cf₀.memory c₁₀.varEnv (x, qt) :=
                            varsRegime_transport_active_lookup_back
                              (predSat := predSat)
                              (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                              (R' := (ctxAfter ctxᵢ firstShared).regime)
                              (μ := cf₀.memory) (ρ := c₁₀.varEnv) (entry := (x, qt))
                              hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                          simpa [hvar₀_eq] using hvar_src
                    · intro x qt v hlookup hlookup_v
                      have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                        (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                      exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ _hθext₀_body.1
                        (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                  exact
                    joinTypeResults_transport_consistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                      h_join hsrc_mem' hcwr_src₀
                · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by
                    simp [heq_cfg₁]
                  have hpred_compat₁ :
                      ∀ (qt' : QTyp) (v' : Value),
                        qtypPredHolds predSat qt' c₁₁.memory v' ↔
                          qtypPredHolds predSat qt' cf₁.memory v' :=
                    qtypPredHolds_mem_compat_of_predSatLaws
                      (hpredlaws := hpredlaws) (θ := θ₁1)
                      (μ := c₁₁.memory) (μ' := cf₁.memory)
                  have hcwr_src₁ :
                      consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        (ctxAfter ctxᵢ firstShared) cf₁.memory cf₁.varEnv θ₁_body := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro l qt k hlookup hguard hRdef
                      have hlookup_body :
                          (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                        simpa [ctxAfter, hfirstShared] using hlookup
                      have hguard_body : qtypGuardTag qt = some k := by
                        simpa [ctxAfter, hfirstShared] using hguard
                      have hRdef_body :
                          (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                        simpa [ctxAfter, hfirstShared] using hRdef
                      have hloc_body :=
                        _hcwr_body_final₁.1 l qt k hlookup_body hguard_body hRdef_body
                      simpa [ctxAfter, hfirstShared, hmem₁_eq] using hloc_body
                    · intro x qt k hlookup hguard hRdef
                      cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                      | none =>
                          exact False.elim (hRdef hk_src)
                      | some b =>
                          have hRdef_res1 :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                            intro hnone
                            have hk_back := hlookup_back_res1_to_src k b hk_src
                            rw [hk_back] at hnone
                            contradiction
                          have hlookup_res1_ctx :
                              (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                            simpa [ctxAfter] using hlookup
                          have hvar_res1 :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                c₁₁.memory c₁₁.varEnv (x, qt) :=
                            hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                          have hvar_res1_mem :
                              varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                                cf₁.memory c₁₁.varEnv (x, qt) :=
                            varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                          have hvar_src :
                              varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                                cf₁.memory c₁₁.varEnv (x, qt) :=
                            varsRegime_transport_active_lookup_back
                              (predSat := predSat)
                              (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                              (R' := (ctxAfter ctxᵢ firstShared).regime)
                              (μ := cf₁.memory) (ρ := c₁₁.varEnv) (entry := (x, qt))
                              hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                          simpa [hvar₁_eq] using hvar_src
                    · intro x qt v hlookup hlookup_v
                      have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                        (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                      exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ _hθext₁_body.1
                        (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                  exact
                    joinTypeResults_transport_consistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                      h_join hsrc_mem' hcwr_src₁
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hval_src₀ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        firstShared.qualType cf₀.memory θ₀_body o₀ := by
                    have hval_first :
                        valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          evalCfg₀.memory θ₀_body o₀ :=
                      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) _hvalc_body₀
                    simpa [ctxAfter, hfirstShared, hmem₀_eq] using hval_first
                  exact
                    joinTypeResults_transport_valueConsistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                      h_join hsrc_mem' hval_src₀
                · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hval_src₁ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                        firstShared.qualType cf₁.memory θ₁_body o₁ := by
                    have hval_first :
                        valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          evalCfg₁.memory θ₁_body o₁ :=
                      valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) _hvalc_body₁
                    simpa [ctxAfter, hfirstShared, hmem₁_eq] using hval_first
                  exact
                    joinTypeResults_transport_valueConsistentWithRegime_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                      h_join hsrc_mem' hval_src₁
                · -- shared-member resultAgreesIfClean -> joined result qualType.
                  have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
                    simp [heq_cfg₀]
                  have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
                    simp [heq_cfg₁]
                  have hres_agree_src :
                      resultAgreesIfClean predSat (ctxAfter ctxᵢ firstShared).regime
                        cf₀.memory cf₁.memory θ₀_body θ₁_body firstShared.qualType o₀ o₁ := by
                    have hres_agree_first :
                        resultAgreesIfClean predSat (ctxAfter bodyCtx result3Shared).regime
                          evalCfg₀.memory evalCfg₁.memory θ₀_body θ₁_body
                          (normalizeAppResultByProvenance (joinPoison p1 p)
                            { result3Shared.qualType with
                              poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                          o₀ o₁ :=
                      resultAgreesIfClean_transport_normalizeAppResultByProvenance
                        (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                        (p := p) (p1 := p1) (qt := result3Shared.qualType)
                        (μ₀ := evalCfg₀.memory) (μ₁ := evalCfg₁.memory)
                        (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                        _hres_agree_body
                    simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hres_agree_first
                  exact
                    joinTypeResults_transport_resultAgreesIfClean_from_member
                      (predSat := predSat)
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      (μ₀ := cf₀.memory) (μ₁ := cf₁.memory) (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                      (o₀ := o₀) (o₁ := o₁)
                      h_join hsrc_mem' hres_agree_src
              exact ⟨θ₀_body, θ₁_body,
                wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 _hθext₀_body),
                wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 _hθext₁_body),
                hOutPack_body⟩
            · -- Fallback: no shared closure (¬ internalPoisonClean). Unary member-evidence helper still needed for full pack.
              exact ⟨θ₀1, θ₁1, wfExtendsMap_trans hθext₀2 hθext₀1, wfExtendsMap_trans hθext₁2 hθext₁1, by sorry⟩
          · -- Fallback: ¬ qtypCleanUnder result1.qualType. resultAgreesIfClean is vacuous (arrow ⇒ p1=true ⇒ res poison/noPred); rest needs unary member-evidence helper.
            have hpoison1_true : result1.qualType.poison = true := by
              by_contra hfalse
              have hpoison_false : result1.qualType.poison = false := Bool.eq_false_iff.mpr hfalse
              have hclean : qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType :=
                qtypCleanUnder.clean hpoison_false
              exact hclean1_e1 hclean
            have hp1_true : p1 = true := by
              rw [← hp1]
              exact hpoison1_true
            rcases list_mapM_ok_mem_output_exists_input
                (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
                (xs := tcls) (ys := results) (y := first) hmap (by simp [heq_results])
              with ⟨tcl, _htcl_mem, happly_first⟩
            have hfirst_pack :
                first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
              applyFnTClosure_ok_poison_pred_of_p1_true
                (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                (result2 := result1) (fuel := fuel') (tcl := tcl) (r := first)
                hp1_true happly_first
            have hres_pack :
                res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred :=
              joinTypeResults_poison_pred_of_head_true_noPred
                (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join hfirst_pack.1 hfirst_pack.2
            -- ===== Per-run body IH for ¬ qtypCleanUnder (p1=true) =====
            -- Extract σcap from closureCapturedVarsRegime for each run.
            -- This avoids the σcap matching problem between valueHasETyp.closure
            -- and closureCapturedVarsRegime.
            have ⟨σcapA₀, hσcapA₀_mem, hσcapA₀_regime, hσcapA₀_typing, hσcapA₀_rec⟩ :=
              closureCapturedVarsRegime_closure_extract hetyp1
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
            have ⟨σcapA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
              closureCapturedVarsRegime_closure_extract hetyp1
                (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
            -- Get body typing for σcapA₀ and σcapA₁ from applyFnTClosure
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₀ body₀ σcapA₀ hmap hσcapA₀_mem with
              ⟨fuelBodyA₀, firstA₀, result3A₀, happlyA₀, hfuelA₀,
                htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
            rcases applyFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x₁ body₁ σcapA₁ hmap hσcapA₁_mem with
              ⟨fuelBodyA₁, firstA₁, result3A₁, happlyA₁, hfuelA₁,
                htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
            -- Get membership in first :: rest (for join transport)
            have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
              rcases list_mapM_ok_mem_input_exists_output
                  (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  hmap hσcapA₀_mem with ⟨y, hy_mem, hy_eq⟩
              rw [← heq_results]
              have : y = firstA₀ := Except.ok.inj (hy_eq.symm.trans happlyA₀)
              rwa [this] at hy_mem
            have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
              rcases list_mapM_ok_mem_input_exists_output
                  (fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  hmap hσcapA₁_mem with ⟨y, hy_mem, hy_eq⟩
              rw [← heq_results]
              have : y = firstA₁ := Except.ok.inj (hy_eq.symm.trans happlyA₁)
              rwa [this] at hy_mem
            -- Define body contexts
            let bodyCtxA₀ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            let bodyCtxA₁ : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison p1 ctxᵢ.pc)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            -- Common setup
            have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
            have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
            have h_mono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
              regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            -- Fuel bounds
            have hfuel_ltA₀ : fuelBodyA₀ < Nat.succ (Nat.succ fuel') := by
              have : fuelBodyA₀ < fuel' := by rw [hfuelA₀]; exact Nat.lt_succ_self _
              exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            have hfuel_ltA₁ : fuelBodyA₁ < Nat.succ (Nat.succ fuel') := by
              have : fuelBodyA₁ < fuel' := by rw [hfuelA₁]; exact Nat.lt_succ_self _
              exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            -- ===== Run 0: StepFR_single_run =====
            have hTmBodyA₀ : wfTagMeaningCtx tm bodyCtxA₀ := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (hqt2 ▸ hresTm2) rfl rfl
              simpa [bodyCtxA₀, ctxAfter] using
                wfTagMeaningCtx_closure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x₀) (body := body₀) (σcap := σcapA₀)
                  (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hTm1 hresTm1' hetyp1 hσcapA₀_mem hargTm
            have htcBodyA₀' : typecheck .ioFree bodyCtxA₀ body₀ fuelBodyA₀ = .ok result3A₀ := by
              simpa [bodyCtxA₀, typecheck] using htc_bodyA₀
            have hIH_bodyA₀ :=
              IH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀ result3A₀ htcBodyA₀'
            have hwfBodyCtxA₀ : wfTypeContext bodyCtxA₀ := by
              simpa [bodyCtxA₀, ctxAfter, wfTypeContext] using hwf1
            have hric_bodyA₀ :
                runtimeInstantiatesCtx bodyCtxA₀ c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
              let ctxCapBaseA₀ : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₀ }
              have hric_cap_baseA₀ :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₀ result1)
                    c₁₀.memory env₀ θ₀1 := by
                constructor
                · intro l a hlookup
                  exact hric₀1.1 l a hlookup
                · intro y qt hlookup
                  have hlookup_list :=
                    list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                  rcases hσcapA₀_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hlookup_list hv⟩
              have hric_bodyA₀' :
                  runtimeInstantiatesCtx
                    { ctxCapBaseA₀ with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBaseA₀) (result2 := result1) (x := x₀)
                  (tenv := σcapA₀)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₀) (μ := c₁₀.memory) (ρ := env₀) (θ := θ₀1)
                  hric_cap_baseA₀ harg₀_typed
                  (fun y qt hlookup => by
                    have hl := list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                    rcases hσcapA₀_typing.2.1 y qt hl with ⟨v, hv⟩
                    exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hl hv⟩)
              simpa [runtimeInstantiatesCtx, bodyCtxA₀, ctxCapBaseA₀, ctxAfter]
                using hric_bodyA₀'
            have htagR_bodyA₀ : regimeConsistentWithCtx bodyCtxA₀ := by
              simpa [bodyCtxA₀, ctxAfter, regimeConsistentWithCtx] using htagR1
            have hRbound_bodyA₀ : regimeBounded bodyCtxA₀.regime :=
              regimeBounded_of_monotoneStep _ _ hRbound2 h_mono1
            have hcwr_bodyA₀ :
                consistentWithRegime predSat bodyCtxA₀.regime bodyCtxA₀
                  c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have hlocs_src₀ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' c₁₀.memory θ₀1 (l, qt) :=
                fun l qt k hlookup hguard hRdef =>
                  hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_capA₀ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₀.memory env₀ (x, qt) :=
                fun x qt k hlookup hguard hRdef =>
                  hσcapA₀_regime x qt k
                    (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hguard hRdef
              have hvars_argA₀ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                  valueConsistentWithRegime_transport_pred
                    (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                    (qt := result2.qualType)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                    (by simp [hqt2]) (hetyp := by simp [hqt2])
                    (by simpa [ctxAfter] using _hvalc₂₀)
                have hvalc_arg_e1 :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                exact
                  varsRegime_transport_predHolds
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                      c₂'₀.memory c₁₀.memory)
                    (varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₀) (k := k)
                      (by simp [VarEnv.update, VarEnv.lookup])
                      hguard hRdef hvalc_arg_e1)
              have h_cap_cvcrA₀ :
                  ∀ x qt v,
                    (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                    env₀.lookup x = some v →
                    closureCapturedVarsRegime predSat result1.regime' qt
                      c₁₀.memory θ₀1 v :=
                fun x qt v hlookup hv =>
                  hσcapA₀_rec x qt v
                    (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hv
              exact
                consistentWithRegime_closure_body_start
                  predSat ctxᵢ result1
                  σcapA₀ x₀ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  c₁₀.memory θ₀1 env₀ v₂₀
                  hlocs_src₀ hvars_capA₀ hvars_argA₀ h_cap_cvcrA₀
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                      c₂'₀.memory c₁₀.memory)
                    hθext₀1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime
                          _hvalc₂₀))))
            have hwfcfg_body_initA₀ :
                wfConfig
                  { memory := c₁₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := c₁₀.nextAddr
                    pureMode := false } := by
              have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                (wfConfig_preserved .ioFree e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
              have hnext₂_to₁ : c₂'₀.nextAddr ≤ c₁₀.nextAddr :=
                terminatesTo_nextAddr_mono .ioFree e1 c₂'₀ c₁₀
                  (Value.closure x₀ body₀ env₀) ht₀_e1
              have hv₂₀_wf : wfValue c₁₀.nextAddr v₂₀ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
              have henv₀_wf : wfVarEnv c₁₀.nextAddr env₀ := by
                cases (wfConfig_preserved .ioFree e1 _ c₁₀ _ ht₀_e1 hwfcf₂₀).2 with
                | closure _ _ _ henv => exact henv
              constructor
              · intro a ha; exact hwfcf₁₀.1 a ha
              · simpa [VarEnv.update] using wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf
            have hsr₀ :=
              StepFR_single_run hIH_bodyA₀ hpredlaws hTmBodyA₀
                c₁₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
                hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀ hRbound_bodyA₀
                hcwr_bodyA₀ c₁₀.nextAddr false hwfcfg_body_initA₀ ht₀_body
            rcases hsr₀ with
              ⟨_, θ₀_body, hθext₀_body, hv₀_body_typed,
                _hTm_bodyA₀_after, _hwf_bodyA₀_after, _hwfcf_bodyA₀,
                hric_bodyA₀_final, _htagR_bodyA₀_final,
                hcwr_bodyA₀_final, hvalc_bodyA₀, _hpres₀⟩
            -- ===== Run 1: StepFR_single_run =====
            have hTmBodyA₁ : wfTagMeaningCtx tm bodyCtxA₁ := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := hresTm1
              have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (hqt2 ▸ hresTm2) rfl rfl
              simpa [bodyCtxA₁, ctxAfter] using
                wfTagMeaningCtx_closure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x₁) (body := body₁) (σcap := σcapA₁)
                  (xArg := x₁) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hTm1 hresTm1' hetyp1 hσcapA₁_mem hargTm
            have htcBodyA₁' : typecheck .ioFree bodyCtxA₁ body₁ fuelBodyA₁ = .ok result3A₁ := by
              simpa [bodyCtxA₁, typecheck] using htc_bodyA₁
            have hIH_bodyA₁ :=
              IH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁ result3A₁ htcBodyA₁'
            have hwfBodyCtxA₁ : wfTypeContext bodyCtxA₁ := by
              simpa [bodyCtxA₁, ctxAfter, wfTypeContext] using hwf1
            have hric_bodyA₁ :
                runtimeInstantiatesCtx bodyCtxA₁ c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
              let ctxCapBaseA₁ : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₁ }
              have hric_cap_baseA₁ :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₁ result1)
                    c₁₁.memory env₁ θ₁1 := by
                constructor
                · intro l a hlookup
                  exact hric₁1.1 l a hlookup
                · intro y qt hlookup
                  have hlookup_list :=
                    list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                  rcases hσcapA₁_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hlookup_list hv⟩
              have hric_bodyA₁' :
                  runtimeInstantiatesCtx
                    { ctxCapBaseA₁ with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBaseA₁) (result2 := result1) (x := x₁)
                  (tenv := σcapA₁)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₁) (μ := c₁₁.memory) (ρ := env₁) (θ := θ₁1)
                  hric_cap_baseA₁ harg₁_typed
                  (fun y qt hlookup => by
                    have hl := list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                    rcases hσcapA₁_typing.2.1 y qt hl with ⟨v, hv⟩
                    exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hl hv⟩)
              simpa [runtimeInstantiatesCtx, bodyCtxA₁, ctxCapBaseA₁, ctxAfter]
                using hric_bodyA₁'
            have htagR_bodyA₁ : regimeConsistentWithCtx bodyCtxA₁ := by
              simpa [bodyCtxA₁, ctxAfter, regimeConsistentWithCtx] using htagR1
            have hRbound_bodyA₁ : regimeBounded bodyCtxA₁.regime :=
              regimeBounded_of_monotoneStep _ _ hRbound2 h_mono1
            have hcwr_bodyA₁ :
                consistentWithRegime predSat bodyCtxA₁.regime bodyCtxA₁
                  c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hlocs_src₁ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' c₁₁.memory θ₁1 (l, qt) :=
                fun l qt k hlookup hguard hRdef =>
                  hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_capA₁ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₁.memory env₁ (x, qt) :=
                fun x qt k hlookup hguard hRdef =>
                  hσcapA₁_regime x qt k
                    (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hguard hRdef
              have hvars_argA₁ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' c₁₁.memory
                      (env₁.update x₁ v₂₁) (x₁, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                  valueConsistentWithRegime_transport_pred
                    (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                    (qt := result2.qualType)
                    (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                    (by simp [hqt2]) (hetyp := by simp [hqt2])
                    (by simpa [ctxAfter] using _hvalc₂₁)
                have hvalc_arg_e1 :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                exact
                  varsRegime_transport_predHolds
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                      c₂'₁.memory c₁₁.memory)
                    (varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (ρ := env₁.update x₁ v₂₁)
                      (x := x₁) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₁) (k := k)
                      (by simp [VarEnv.update, VarEnv.lookup])
                      hguard hRdef hvalc_arg_e1)
              have h_cap_cvcrA₁ :
                  ∀ x qt v,
                    (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                    env₁.lookup x = some v →
                    closureCapturedVarsRegime predSat result1.regime' qt
                      c₁₁.memory θ₁1 v :=
                fun x qt v hlookup hv =>
                  hσcapA₁_rec x qt v
                    (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hv
              exact
                consistentWithRegime_closure_body_start
                  predSat ctxᵢ result1
                  σcapA₁ x₁ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                  c₁₁.memory θ₁1 env₁ v₂₁
                  hlocs_src₁ hvars_capA₁ hvars_argA₁ h_cap_cvcrA₁
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                      c₂'₁.memory c₁₁.memory)
                    hθext₁1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime
                          _hvalc₂₁))))
            have hwfcfg_body_initA₁ :
                wfConfig
                  { memory := c₁₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := c₁₁.nextAddr
                    pureMode := false } := by
              have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                (wfConfig_preserved .ioFree e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
              have hnext₂_to₁ : c₂'₁.nextAddr ≤ c₁₁.nextAddr :=
                terminatesTo_nextAddr_mono .ioFree e1 c₂'₁ c₁₁
                  (Value.closure x₁ body₁ env₁) ht₁_e1
              have hv₂₁_wf : wfValue c₁₁.nextAddr v₂₁ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
              have henv₁_wf : wfVarEnv c₁₁.nextAddr env₁ := by
                cases (wfConfig_preserved .ioFree e1 _ c₁₁ _ ht₁_e1 hwfcf₂₁).2 with
                | closure _ _ _ henv => exact henv
              constructor
              · intro a ha; exact hwfcf₁₁.1 a ha
              · simpa [VarEnv.update] using wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf
            have hsr₁ :=
              StepFR_single_run hIH_bodyA₁ hpredlaws hTmBodyA₁
                c₁₁.memory (env₁.update x₁ v₂₁) θ₁1 evalCfg₁ o₁
                hθ₁1wf hwfBodyCtxA₁ hric_bodyA₁ htagR_bodyA₁ hRbound_bodyA₁
                hcwr_bodyA₁ c₁₁.nextAddr false hwfcfg_body_initA₁ ht₁_body
            rcases hsr₁ with
              ⟨_, θ₁_body, hθext₁_body, hv₁_body_typed,
                _hTm_bodyA₁_after, _hwf_bodyA₁_after, _hwfcf_bodyA₁,
                hric_bodyA₁_final, _htagR_bodyA₁_final,
                hcwr_bodyA₁_final, hvalc_bodyA₁, _hpres₁⟩
            -- ===== Transport to joined result and pack =====
            -- etyp agreement: body result etyp = firstA etyp (normalizeAppResultByProvenance preserves etyp)
            have hfirstA₀_etyp : firstA₀.qualType.etyp = result3A₀.qualType.etyp := by
              rw [hfirstA₀_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
            have hfirstA₁_etyp : firstA₁.qualType.etyp = result3A₁.qualType.etyp := by
              rw [hfirstA₁_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
            -- regime monotonicity from result1 to body results
            have h_mono_bodyA₀ : Regime.monotoneStep bodyCtxA₀.regime result3A₀.regime' :=
              regime_monotone bodyCtxA₀ body₀ fuelBodyA₀ result3A₀ htcBodyA₀'
            have h_mono_bodyA₁ : Regime.monotoneStep bodyCtxA₁.regime result3A₁.regime' :=
              regime_monotone bodyCtxA₁ body₁ fuelBodyA₁ result3A₁ htcBodyA₁'
            have hres1_to_firstA₀_mono :
                Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                  (ctxAfter ctxᵢ firstA₀).regime := by
              simpa [bodyCtxA₀, ctxAfter, hfirstA₀_eq] using h_mono_bodyA₀
            have hres1_to_firstA₁_mono :
                Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                  (ctxAfter ctxᵢ firstA₁).regime := by
              simpa [bodyCtxA₁, ctxAfter, hfirstA₁_eq] using h_mono_bodyA₁
            -- lookup-back for regime: firstA₀.regime' → result1.regime'
            have hlookup_back_res1_to_A₀ :
                ∀ k b,
                  (ctxAfter ctxᵢ firstA₀).regime.lookup? k = some b →
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
              intro k b hk_src
              have hRdef_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k ≠ none := by
                intro hnone; rw [hk_src] at hnone; contradiction
              have hRdef_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                hres1_to_firstA₀_mono.2.2 k hRdef_src
              cases hk_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
              | none => exact False.elim (hRdef_res1 hk_res1)
              | some b1 =>
                  rcases hres1_to_firstA₀_mono.2.1 k b1 hk_res1 with hk_src' | hnone_src
                  · have : some b1 = some b := hk_src'.symm.trans hk_src
                    simp [Option.some.inj this]
                  · rw [hnone_src] at hk_src; cases hk_src
            have hlookup_back_res1_to_A₁ :
                ∀ k b,
                  (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
              intro k b hk_src
              have hRdef_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k ≠ none := by
                intro hnone; rw [hk_src] at hnone; contradiction
              have hRdef_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                hres1_to_firstA₁_mono.2.2 k hRdef_src
              cases hk_res1 :
                  (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
              | none => exact False.elim (hRdef_res1 hk_res1)
              | some b1 =>
                  rcases hres1_to_firstA₁_mono.2.1 k b1 hk_res1 with hk_src' | hnone_src
                  · have : some b1 = some b := hk_src'.symm.trans hk_src
                    simp [Option.some.inj this]
                  · rw [hnone_src] at hk_src; cases hk_src
            -- Memory/varEnv equalities
            have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by simp [heq_cfg₀]
            have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by simp [heq_cfg₁]
            have hvar₀_eq : cf₀.varEnv = c₁₀.varEnv := by simp [heq_cfg₀]
            have hvar₁_eq : cf₁.varEnv = c₁₁.varEnv := by simp [heq_cfg₁]
            -- predSat compat for memory transport
            have hpred_compat₀ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' c₁₀.memory v' ↔
                    qtypPredHolds predSat qt' cf₀.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₀1) (μ := c₁₀.memory) (μ' := cf₀.memory)
            have hpred_compat₁ :
                ∀ (qt' : QTyp) (v' : Value),
                  qtypPredHolds predSat qt' c₁₁.memory v' ↔
                    qtypPredHolds predSat qt' cf₁.memory v' :=
              qtypPredHolds_mem_compat_of_predSatLaws
                (hpredlaws := hpredlaws) (θ := θ₁1) (μ := c₁₁.memory) (μ' := cf₁.memory)
            exact ⟨θ₀_body, θ₁_body,
              wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 hθext₀_body),
              wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 hθext₁_body),
              -- valueHasETyp run 0
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                (θ := θ₀_body) (v := o₀)
                h_join hfirstA₀_mem' (hfirstA₀_etyp ▸ hv₀_body_typed),
              -- valueHasETyp run 1
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                (θ := θ₁_body) (v := o₁)
                h_join hfirstA₁_mem' (hfirstA₁_etyp ▸ hv₁_body_typed),
              -- runtimeInstantiatesCtx run 0
              by
                have hmem_to_res₀ :
                    ∀ l, firstA₀.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest)
                    (res := res) h_join hfirstA₀_mem'
                constructor
                · intro l a hθ
                  have hloc := hric_bodyA₀_final.1 l a hθ
                  rcases hloc with ⟨hcontains_body, hmem_contains⟩
                  have hcontains_src : firstA₀.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstA₀_eq] using hcontains_body
                  exact ⟨hmem_to_res₀ l hcontains_src, by simpa [hmem₀_eq] using hmem_contains⟩
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  exact ⟨v, by simpa [hvar₀_eq] using hlookup_v,
                    valueHasETyp_extends hθext₀_body.1 hv_typ⟩,
              -- runtimeInstantiatesCtx run 1
              by
                have hmem_to_res₁ :
                    ∀ l, firstA₁.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest)
                    (res := res) h_join hfirstA₁_mem'
                constructor
                · intro l a hθ
                  have hloc := hric_bodyA₁_final.1 l a hθ
                  rcases hloc with ⟨hcontains_body, hmem_contains⟩
                  have hcontains_src : firstA₁.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstA₁_eq] using hcontains_body
                  exact ⟨hmem_to_res₁ l hcontains_src, by simpa [hmem₁_eq] using hmem_contains⟩
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  exact ⟨v, by simpa [hvar₁_eq] using hlookup_v,
                    valueHasETyp_extends hθext₁_body.1 hv_typ⟩,
              -- consistentWithRegime run 0
              by
                have hcwr_src₀ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                      (ctxAfter ctxᵢ firstA₀) cf₀.memory cf₀.varEnv θ₀_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtxA₀ result3A₀).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstA₀_eq] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstA₀_eq] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtxA₀ result3A₀).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstA₀_eq] using hRdef
                    simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using
                      hcwr_bodyA₀_final.1 l qt k hlookup_body hguard_body hRdef_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k with
                    | none => exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_A₀ k b hk_src
                          rw [hk_back] at hnone; contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                              some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :=
                          hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :=
                          varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                        simpa [hvar₀_eq] using
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstA₀).regime)
                            (μ := cf₀.memory) (ρ := c₁₀.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_A₀ hguard hk_src hvar_res1_mem
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ hθext₀_body.1
                      (closureCapturedVarsRegime_transport_lookup_back
                        hlookup_back_res1_to_A₀ hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                    h_join hfirstA₀_mem' hcwr_src₀,
              -- consistentWithRegime run 1
              by
                have hcwr_src₁ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                      (ctxAfter ctxᵢ firstA₁) cf₁.memory cf₁.varEnv θ₁_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtxA₁ result3A₁).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstA₁_eq] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstA₁_eq] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtxA₁ result3A₁).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstA₁_eq] using hRdef
                    simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using
                      hcwr_bodyA₁_final.1 l qt k hlookup_body hguard_body hRdef_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k with
                    | none => exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_A₁ k b hk_src
                          rw [hk_back] at hnone; contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                              some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :=
                          hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :=
                          varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                        simpa [hvar₁_eq] using
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstA₁).regime)
                            (μ := cf₁.memory) (ρ := c₁₁.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_A₁ hguard hk_src hvar_res1_mem
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ hθext₁_body.1
                      (closureCapturedVarsRegime_transport_lookup_back
                        hlookup_back_res1_to_A₁ hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                    h_join hfirstA₁_mem' hcwr_src₁,
              -- agreeOnClean for ¬qtypCleanUnder (p1=true, different closure bodies)
              by
                -- Regime monotonicity: result1.regime' → res.regime' (through the join)
                have h_all_members_mono :
                    ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                  apply List.mapM_Except_preserves_property
                    (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                      ctxᵢ result1 fuel')
                    (P := fun x => Regime.monotoneStep result1.regime' x.regime')
                  · intro tcl result _htcl
                    exact applyFnTClosure_regime_mono tcl ctxᵢ st1 st2 p p1 etyp2 p2 pred2
                      result1 result fuel'
                      (fun m _hlt e ctx' res' htc =>
                        by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                      _htcl
                  · rw [← heq_results]; exact hmap
                have h_mono_res : Regime.monotoneStep result1.regime' res.regime' :=
                  joinTypeResults_regime_monotone ctxᵢ first rest res result1.regime'
                    (h_all_members_mono first (by simp))
                    (fun x hx => h_all_members_mono x (List.mem_cons_of_mem _ hx))
                    h_join
                -- Clean transfer: qtypCleanUnder res → qtypCleanUnder result1
                have h_clean_res_to_pre :
                    ∀ qt, qtypCleanUnder res.regime' qt →
                      qtypCleanUnder result1.regime' qt :=
                  fun qt hc => cleanUnder_of_monotone h_mono_res hc
                constructor
                · -- Locations conjunct
                  intro l qt hlookup hclean
                  have hclean_res : qtypCleanUnder res.regime' qt := by
                    simpa [ctxAfter] using hclean
                  have hlookup_res : res.memEnv'.lookup l = some qt := by
                    simpa [ctxAfter] using hlookup
                  -- Case split: is l inherited from result1.memEnv'?
                  cases hlookup_body : (result1.memEnv'.lookup l) with
                  | none =>
                    exfalso
                    have hcontains_res : res.memEnv'.contains l := by
                      exact memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
                    rcases joinTypeResults_mem_contains_head_or_rest
                        ctxᵢ first rest res h_join l hcontains_res with
                      hsrc_head | ⟨srcRes, hsrc_rest, hsrc_contains⟩
                    · have hsrc_results : first ∈ results := by
                        simp [heq_results]
                      rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          (xs := tcls) (ys := results) (y := first) hmap hsrc_results with
                        ⟨tcl, _htcl_mem, happly_src⟩
                      rcases memEnv_lookup_some_of_contains first.memEnv' l hsrc_head with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctxᵢ first).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have hclean_src :
                          qtypCleanUnder (ctxAfter ctxᵢ first).regime qt_src := by
                        exact
                          joinTypeResults_lookup_member_clean_compat
                            (ctx := ctxᵢ) (first := first) (src := first) (rest := rest) (res := res)
                            h_join (by simp) l qt qt_src hlookup hclean hlookup_src_ctx
                      exact
                        applyFnTClosure_fresh_lookup_not_clean_of_p1_true
                          (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                          (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                          (result2 := result1) (fuel := fuel') (tcl := tcl) (r := first)
                          hp1_true l qt_src hlookup_body happly_src hlookup_src hclean_src
                    · have hsrc_mem : srcRes ∈ first :: rest := by
                        exact List.mem_cons_of_mem first hsrc_rest
                      have hsrc_results : srcRes ∈ results := by
                        simpa [heq_results] using hsrc_mem
                      rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyFnTClosure .ioFree tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          (xs := tcls) (ys := results) (y := srcRes) hmap hsrc_results with
                        ⟨tcl, _htcl_mem, happly_src⟩
                      rcases memEnv_lookup_some_of_contains srcRes.memEnv' l hsrc_contains with
                        ⟨qt_src, hlookup_src⟩
                      have hlookup_src_ctx :
                          (ctxAfter ctxᵢ srcRes).memEnv.lookup l = some qt_src := by
                        simpa [ctxAfter] using hlookup_src
                      have hclean_src :
                          qtypCleanUnder (ctxAfter ctxᵢ srcRes).regime qt_src := by
                        exact
                          joinTypeResults_lookup_member_clean_compat
                            (ctx := ctxᵢ) (first := first) (src := srcRes) (rest := rest) (res := res)
                            h_join hsrc_mem l qt qt_src hlookup hclean hlookup_src_ctx
                      exact
                        applyFnTClosure_fresh_lookup_not_clean_of_p1_true
                          (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                          (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                          (result2 := result1) (fuel := fuel') (tcl := tcl) (r := srcRes)
                          hp1_true l qt_src hlookup_body happly_src hlookup_src hclean_src
                  | some qt' =>
                    -- Inherited location: l is in result1.memEnv' with type qt'
                    have hetyp_qt : qt.etyp = ETyp.int :=
                      memEnv_lookup_etyp_int res.memEnv' l qt hlookup_res
                    have hetyp_qt' : qt'.etyp = ETyp.int :=
                      memEnv_lookup_etyp_int result1.memEnv' l qt' hlookup_body
                    have hcontains_body : result1.memEnv'.contains l := by
                      exact
                        memEnv_contains_of_lookup_some
                          (env := result1.memEnv') (l := l) (qt := qt') hlookup_body
                    have hcontains_A₀ : firstA₀.memEnv'.contains l := by
                      have hcontains_result3A₀ : result3A₀.memEnv'.contains l := by
                        exact
                          typecheckExpr_mem_contains_preserved
                            (ctx := bodyCtxA₀) (e := body₀) (fuel := fuelBodyA₀) (res := result3A₀)
                            htc_bodyA₀ l (by simpa [bodyCtxA₀] using hcontains_body)
                      simpa [hfirstA₀_eq] using hcontains_result3A₀
                    have hcontains_A₁ : firstA₁.memEnv'.contains l := by
                      have hcontains_result3A₁ : result3A₁.memEnv'.contains l := by
                        exact
                          typecheckExpr_mem_contains_preserved
                            (ctx := bodyCtxA₁) (e := body₁) (fuel := fuelBodyA₁) (res := result3A₁)
                            htc_bodyA₁ l (by simpa [bodyCtxA₁] using hcontains_body)
                      simpa [hfirstA₁_eq] using hcontains_result3A₁
                    rcases memEnv_lookup_some_of_contains firstA₀.memEnv' l hcontains_A₀ with
                      ⟨qt_A₀, hlookup_A₀⟩
                    rcases memEnv_lookup_some_of_contains firstA₁.memEnv' l hcontains_A₁ with
                      ⟨qt_A₁, hlookup_A₁⟩
                    have hlookup_A₀_ctx :
                        (ctxAfter ctxᵢ firstA₀).memEnv.lookup l = some qt_A₀ := by
                      simpa [ctxAfter] using hlookup_A₀
                    have hlookup_A₁_ctx :
                        (ctxAfter ctxᵢ firstA₁).memEnv.lookup l = some qt_A₁ := by
                      simpa [ctxAfter] using hlookup_A₁
                    have hclean_A₀ :
                        qtypCleanUnder (ctxAfter ctxᵢ firstA₀).regime qt_A₀ := by
                      exact
                        joinTypeResults_lookup_member_clean_compat
                          (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                          h_join hfirstA₀_mem' l qt qt_A₀ hlookup hclean hlookup_A₀_ctx
                    -- Establish qt' cleanness under result1.regime'
                    -- (bodies may change the type at l; qt' ≠ qt is possible)
                    have hclean_pre' : qtypCleanUnder result1.regime' qt' := by
                      have hlookup_result3A₀ : result3A₀.memEnv'.lookup l = some qt_A₀ := by
                        simpa [hfirstA₀_eq] using hlookup_A₀
                      have hclean_result3A₀ : qtypCleanUnder result3A₀.regime' qt_A₀ := by
                        simpa [ctxAfter, hfirstA₀_eq] using hclean_A₀
                      have hpc_bodyA₀ : bodyCtxA₀.pc = true := by
                        simp [bodyCtxA₀, hp1_true, joinPoison]
                      exact
                        typecheckExpr_lookup_clean_back_of_pc_true
                          (ctx := bodyCtxA₀) (e := body₀) (fuel := fuelBodyA₀) (res := result3A₀)
                          htc_bodyA₀ hpc_bodyA₀ l qt' qt_A₀
                          (by simpa [bodyCtxA₀] using hlookup_body)
                          hlookup_result3A₀ hclean_result3A₀
                    -- Use qt' cleanness to prove agreeLocUnder
                    have hlookup_pre :
                        (ctxAfter (ctxAfter ctxᵢ result2) result1).memEnv.lookup l =
                          some qt' := by
                      simpa [ctxAfter] using hlookup_body
                    have hloc_pre := hagree1.1 l qt' hlookup_pre hclean_pre'
                    -- Per-run preservation
                    rcases _hpres₀ with ⟨hpres₀_fn⟩
                    have hpres_l₀ := hpres₀_fn l qt'
                      (by simp only [bodyCtxA₀]; exact hlookup_body) hclean_pre'
                    rcases _hpres₁ with ⟨hpres₁_fn⟩
                    have hpres_l₁ := hpres₁_fn l qt'
                      (by simp only [bodyCtxA₁]; exact hlookup_body) hclean_pre'
                    -- Case split on pre-body loc agreement × run preservation
                    cases hloc_pre with
                    | both_unrealized _ _ hθ₀_none hθ₁_none =>
                      cases hpres_l₀ with
                      | both_unrealized _ hout₀ =>
                        cases hpres_l₁ with
                        | both_unrealized _ hout₁ =>
                          exact agreeLocUnder.both_unrealized l qt hout₀ hout₁
                        | preserve_value a n hin _ _ _ =>
                          exact absurd (hθ₁_none ▸ hin) (by exact Option.noConfusion)
                      | preserve_value a n hin _ _ _ =>
                        exact absurd (hθ₀_none ▸ hin) (by exact Option.noConfusion)
                    | agree_values _ _ a₀ a₁ n₀ n₁ hθ₀_in hθ₁_in hm₀_in hm₁_in
                        hagree_val =>
                      cases hpres_l₀ with
                      | both_unrealized hin₀ _ =>
                        exact absurd (hin₀ ▸ hθ₀_in) (by exact Option.noConfusion)
                      | preserve_value a₀' n₀' hθ₀_in' hm₀_in' hθ₀_out hm₀_out =>
                        cases hpres_l₁ with
                        | both_unrealized hin₁ _ =>
                          exact absurd (hin₁ ▸ hθ₁_in) (by exact Option.noConfusion)
                        | preserve_value a₁' n₁' hθ₁_in' hm₁_in' hθ₁_out hm₁_out =>
                          -- Equate addresses via unique θ lookups
                          have ha₀ : a₀' = a₀ :=
                            Option.some.inj (hθ₀_in'.symm.trans hθ₀_in)
                          have ha₁ : a₁' = a₁ :=
                            Option.some.inj (hθ₁_in'.symm.trans hθ₁_in)
                          -- Equate values via unique memory lookups
                          have hn₀ : n₀' = n₀ := by
                            rw [ha₀] at hm₀_in'
                            exact Option.some.inj (hm₀_in'.symm.trans hm₀_in)
                          have hn₁ : n₁' = n₁ := by
                            rw [ha₁] at hm₁_in'
                            exact Option.some.inj (hm₁_in'.symm.trans hm₁_in)
                          -- Pre-body value equality (clean ints must agree)
                          have heq_pre : n₀ = n₁ := by
                            cases hagree_val with
                            | clean_eq_nonref_nonarrow _ _ _ hEq =>
                              exact Value.num.inj hEq
                            | withPred_true_eq _ _ _ _ _ hEq =>
                              exact Value.num.inj hEq
                            | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | dirty_internal_arrow _ hisA htyp₀ _ =>
                              simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                            | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                              cases hv₀
                            | dirty_internal_parrow _ hisP htyp₀ _ =>
                              simp [valueHasETyp_num_etyp htyp₀, ETyp.isParrow] at hisP
                            | clean_ref _ _ _ _ hv₀ _ _ => cases hv₀
                            | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ => cases hv₀
                          have heq_post : n₀' = n₁' := by
                            rw [hn₀, hn₁, heq_pre]
                          -- Construct post-body agreeLocUnder
                          refine agreeLocUnder.agree_values l qt a₀' a₁'
                            n₀' n₁' hθ₀_out hθ₁_out
                            (by rw [hmem₀_eq]; exact hm₀_out)
                            (by rw [hmem₁_eq]; exact hm₁_out) ?_
                          rw [heq_post]
                          cases hclean_res with
                          | clean hpoison =>
                            exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison
                              (by simp [hetyp_qt, ETyp.isFunctionType, ETyp.isArrow,
                                        ETyp.isParrow])
                              (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                          | guard k htag hregime hnotfun =>
                            exact agreeValueUnder.withPred_true_eq k htag
                              (by simpa [ctxAfter] using hregime) hnotfun
                              (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                · -- Variables conjunct
                  intro x qt hlookup hclean
                  have hlookup_pre :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  have hclean_pre : qtypCleanUnder result1.regime' qt :=
                    h_clean_res_to_pre qt (by simpa [ctxAfter] using hclean)
                  cases hagree1.2 x qt hlookup_pre hclean_pre with
                  | agree_values x qt v₀ v₁ hv₀_pre hv₁_pre hagree_val =>
                    refine agreeVarUnder.agree_values x qt v₀ v₁
                      (by rwa [hvar₀_eq]) (by rwa [hvar₁_eq]) ?_
                    -- Transport agreeValueUnder:
                    -- 1. Extend memory/θ (result1 context → body output context)
                    have hagree_ext :=
                      agreeValueUnder_clean_extends
                        hpred_compat₀ hpred_compat₁ hclean_pre hθext₀_body.1 hθext₁_body.1
                        hagree_val
                    -- 2. Change regime (result1 → res)
                    exact agreeValueUnder_clean_monotoneRegime h_mono_res
                      (by simpa [ctxAfter] using hclean) hagree_ext
                  | both_none x qt hv₀_pre hv₁_pre =>
                    exact agreeVarUnder.both_none x qt
                      (by rwa [hvar₀_eq]) (by rwa [hvar₁_eq]),
              -- valueConsistentWithRegime run 0
              by
                have hfirstA₀_eq_regime : firstA₀.regime' = result3A₀.regime' := by
                  simp [hfirstA₀_eq]
                have hval_src₀ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                      firstA₀.qualType cf₀.memory θ₀_body o₀ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtxA₀ result3A₀).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3A₀.qualType with
                            poison := joinPoison p1 (joinPoison p result3A₀.qualType.poison) })
                        evalCfg₀.memory θ₀_body o₀ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtxA₀ result3A₀).regime)
                      (p := p) (p1 := p1) (qt := result3A₀.qualType)
                      (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) hvalc_bodyA₀
                  simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                    (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                    h_join hfirstA₀_mem' hval_src₀,
              -- valueConsistentWithRegime run 1
              by
                have hval_src₁ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                      firstA₁.qualType cf₁.memory θ₁_body o₁ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtxA₁ result3A₁).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3A₁.qualType with
                            poison := joinPoison p1 (joinPoison p result3A₁.qualType.poison) })
                        evalCfg₁.memory θ₁_body o₁ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtxA₁ result3A₁).regime)
                      (p := p) (p1 := p1) (qt := result3A₁.qualType)
                      (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) hvalc_bodyA₁
                  simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                    (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                    h_join hfirstA₁_mem' hval_src₁,
              -- resultAgreesIfClean (vacuously true since poison=true ∧ pred=noPred)
              resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
        rcases hOutMapChoice with ⟨θ₀_out, θ₁_out, hθext_out₀, hθext_out₁, hOutPack⟩
        rcases hOutPack with
          ⟨hv_out₀, hv_out₁, hric_out₀, hric_out₁,
            hcwr_out₀, hcwr_out₁, hAgree_out, hvalc_out₀, hvalc_out₁, hres_agree_out⟩
        have hwf_result1 : wfTypeResult result1 := by
          simp only [ctxAfter, wfTypeContext, wfTypeResult] at hwf1 ⊢
          exact hwf1
        have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := hqt2 ▸ hresTm2
        have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
          QTypRespectsTagMeaning_transport_etyp_pred
            (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
            (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
            hresTm2_arg rfl rfl
        have hresults_wf :
            ∀ r, r ∈ results → wfTypeResult r :=
          mapM_applyFnTClosure_forall_wfTypeResult
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            hwf_result1
            (tcls := tcls) (results := results) hmap
        have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctxᵢ result1) := by
          simpa [ctxAfter] using hTm1
        have hresults_tm :
            ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctxᵢ r) :=
          mapM_applyFnTClosure_forall_wfTagMeaningCtx
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx hresTm1 hetyp1 hresTm2_arg hmap
        have hresults_regime :
            ∀ r, r ∈ results →
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          have htagR1_ctx :
              regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
            simpa [ctxAfter] using htagR1
          exact
            mapM_applyFnTClosure_forall_regimeConsistentWithCtx
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              htagR1_ctx hmap
        have hresults_qtm :
            ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
          mapM_applyFnTClosure_forall_QTypRespectsTagMeaning
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx hresTm1 hetyp1 hresTm2_arg hmap
        have hfirst_in_results : first ∈ results := by
          simp [heq_results]
        have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
        have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctxᵢ first) := hresults_tm first hfirst_in_results
        have h_first_regime :
            regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
          hresults_regime first hfirst_in_results
        have h_first_qtm : QTypRespectsTagMeaning tm first.qualType :=
          by
            intro qt' k d hinq hqd
            exact hresults_qtm first hfirst_in_results hinq hqd
        have h_rest_wf : ∀ r ∈ rest, wfTypeResult r := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_wf r hmem_results
        have h_rest_regime :
            ∀ r ∈ rest,
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_regime r hmem_results
        have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          intro qt' k d hinq hqd
          exact hresults_qtm r hmem_results hinq hqd
        have h_mem_join :
            ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l :=
          joinTypeResults_mem_contains_head_or_rest
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_regime_bound_le_join : res.regime'.bound ≤ first.regime'.bound :=
          joinTypeResults_regime_bound_le_head
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_tag_join :
            tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv (ctxAfter ctxᵢ res).regime :=
          joinTypeResults_tagEnvConsistentWithRegime
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
            h_join h_first_regime h_rest_regime
        refine ⟨?_, θ₀_out, θ₁_out,
          ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- QTypRespectsTagMeaning tm res.qualType
          exact
            joinTypeResults_QTypRespectsTagMeaning
              (tm := tm)
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_first_qtm h_rest_qtm
        · -- wfExtendsMap θ₀ θ₀'
          exact hθext_out₀
        · -- wfExtendsMap θ₁ θ₁'
          exact hθext_out₁
        · -- valueHasETyp θ₀1 o₀ res.qualType.etyp
          exact hv_out₀
        · -- valueHasETyp θ₁1 o₁ res.qualType.etyp
          exact hv_out₁
        · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
          exact
            join_transport_wfTagMeaningCtx
              (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_first_tm
        · -- wfTypeContext (ctxAfter ctxᵢ res)
          exact
            join_transport_wfTypeContext
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_mem_join
              (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf)
              h_rest_wf
        · -- wfConfig cf₀
          exact (wfConfig_preserved .ioFree (Expr.app e1 e2) _ cf₀ o₀ ht₀ hwfcfg₀).1
        · -- wfConfig cf₁
          exact (wfConfig_preserved .ioFree (Expr.app e1 e2) _ cf₁ o₁ ht₁ hwfcfg₁).1
        · -- runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀1
          exact hric_out₀
        · -- runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁1
          exact hric_out₁
        · -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
          exact
            join_transport_regimeConsistentWithCtx
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join h_regime_bound_le_join h_tag_join h_first_regime
        · -- consistentWithRegime ... cf₀
          exact hcwr_out₀
        · -- consistentWithRegime ... cf₁
          exact hcwr_out₁
        · -- agreeOnClean ...
          exact hAgree_out
        · -- valueConsistentWithRegime ... cf₀.memory o₀
          exact hvalc_out₀
        · -- valueConsistentWithRegime ... cf₁.memory o₁
          exact hvalc_out₁
        · -- resultAgreesIfClean ...
          exact hres_agree_out
      · -- Run 1: peClosure (mixed case, impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₁1_arrow : valueHasETyp θ₁1 (Value.peClosure x₁ body₁ env₁) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        cases hv₁1_arrow
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Run 0: peClosure, Run 1: closure (mixed case, impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_arrow
      · -- Run 0: peClosure, Run 1: peClosure (impossible under arrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_arrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.arrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_arrow
  | inr h_parrow =>
    -- Pure arrow case (peClosure)
    obtain ⟨st1, st2, p, p1, tcls, results, first, rest, hetyp1, hp1, _hnempty, _hsub,
            hmap, heq_results, h_join⟩ := h_parrow
    have htc2' : typecheck .ioFree ctxᵢ e2 fuel' = .ok result2 := by
      simpa [typecheck] using htc2
    have htc1' : typecheck .ioFree (ctxAfter ctxᵢ result2) e1 fuel' = .ok result1 := by
      simp [ctxAfter] at htc1 ⊢
      exact htc1
    intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
    -- Phase 2: IH for e2
    have hIH_e2 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e2 ctxᵢ hwfTm result2 htc2'
    -- Phase 3: Runtime evaluation inversion
    let cinit₀ : Config := { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm }
    let cinit₁ : Config := { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm }
    have hstruct₀ := terminatesTo_app_inv' e1 e2 cinit₀ cf₀ o₀ ht₀
    have hstruct₁ := terminatesTo_app_inv' e1 e2 cinit₁ cf₁ o₁ ht₁
    -- Handle runtime closure/peClosure splits for the parrow-typed branch.
    rcases hstruct₀ with h_clo₀ | h_peclo₀
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Both runs: closure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_parrow
      · -- Run 0: closure, Run 1: peClosure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, hpm1₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_clo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.closure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.closure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        cases hv₀1_parrow
    · rcases hstruct₁ with h_clo₁ | h_peclo₁
      · -- Run 0: peClosure, Run 1: closure (impossible under parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, hpm1₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_clo₁
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hv₂₀, _hv₂₁, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.closure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        have hv₁1_parrow : valueHasETyp θ₁1 (Value.closure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        cases hv₁1_parrow
      · -- Both runs: peClosure (the real case for parrow typing)
        obtain ⟨c₂'₀, v₂₀, c₁₀, x₀, body₀, env₀, evalCfg₀, ht₀_e2, ht₀_e1, htoP₀, ht₀_body, heq_cfg₀, hpm_e2₀, _⟩ := h_peclo₀
        obtain ⟨c₂'₁, v₂₁, c₁₁, x₁, body₁, env₁, evalCfg₁, ht₁_e2, ht₁_e1, htoP₁, ht₁_body, heq_cfg₁, hpm_e2₁, _⟩ := h_peclo₁
        -- Phase A: Apply IH for e2
        have hstep_e2 := hIH_e2 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ c₂'₀ c₂'₁ v₂₀ v₂₁
          hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e2 ht₁_e2
        rcases hstep_e2 with ⟨_hresTm2, ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hv₂₀_typed, hv₂₁_typed, hTm2, hwf2, hwfcf₂₀, hwfcf₂₁,
          hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₂₀, _hvalc₂₁, hres_agree2⟩⟩
        -- Phase B: Apply IH for e1
        have hIH_e1 := IH fuel' (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) e1 (ctxAfter ctxᵢ result2) hTm2 result1 htc1'
        have hθ₀2wf : wfRealizationMap θ₀2 := hθext₀2.2 hθ₀
        have hθ₁2wf : wfRealizationMap θ₁2 := hθext₁2.2 hθ₁
        have h_mono2 : Regime.monotoneStep ctxᵢ.regime result2.regime' := regime_monotone ctxᵢ e2 fuel' result2 htc2'
        have hRbound2 : regimeBounded (ctxAfter ctxᵢ result2).regime := by
          simp only [ctxAfter]
          exact regimeBounded_of_monotoneStep ctxᵢ.regime result2.regime' hRbound h_mono2
        have hpm₀ : c₂'₀.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₀ c₂'₀ v₂₀ ht₀_e2).trans rfl
        have hpm₁ : c₂'₁.pureMode = pm := (terminatesTo_IOFree_preserves_pureMode e2 cinit₁ c₂'₁ v₂₁ ht₁_e2).trans rfl
        have heq_cfg₀' : c₂'₀ = { memory := c₂'₀.memory, varEnv := c₂'₀.varEnv, nextAddr := c₂'₀.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₀.pureMode from hpm₀.symm]
        have heq_cfg₁' : c₂'₁ = { memory := c₂'₁.memory, varEnv := c₂'₁.varEnv, nextAddr := c₂'₁.nextAddr, pureMode := pm } := by
          rw [show pm = c₂'₁.pureMode from hpm₁.symm]
        have hstep_e1 := hIH_e1 hpredlaws hTm2
          c₂'₀.memory c₂'₁.memory c₂'₀.varEnv c₂'₁.varEnv θ₀2 θ₁2
          c₁₀ c₁₁ (Value.peClosure x₀ body₀ env₀) (Value.peClosure x₁ body₁ env₁)
          hθ₀2wf hθ₁2wf hwf2 hric₀2 hric₁2 htagR2 hRbound2 hcwr₀2 hcwr₁2 hagree2
          c₂'₀.nextAddr c₂'₁.nextAddr pm hwfcf₂₀ hwfcf₂₁
          (heq_cfg₀' ▸ ht₀_e1) (heq_cfg₁' ▸ ht₁_e1)
        rcases hstep_e1 with ⟨_hresTm1, ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, hv₀1_typed, hv₁1_typed, _hTm1, hwf1, hwfcf₁₀, hwfcf₁₁,
          hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₁₀, _hvalc₁₁, hres_agree1⟩⟩
        -- Phase C: Invert peClosure typing to extract closure structure
        have hv₀1_parrow : valueHasETyp θ₀1 (Value.peClosure x₀ body₀ env₀) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₀1_typed
        have hv₁1_parrow : valueHasETyp θ₁1 (Value.peClosure x₁ body₁ env₁) (ETyp.parrow st1 st2 p tcls) := hetyp1.symm ▸ hv₁1_typed
        -- Invert peClosure typing for both runs
        cases hv₀1_parrow with
        | peClosure hpure₀ htcl₀ henv₀_typing hcover₀ =>
        cases hv₁1_parrow with
        | peClosure hpure₁ htcl₁ henv₁_typing hcover₁ =>
        -- Phase D: Extract body typing from applyPFnTClosure via mapM membership
        rcases applyPFnTClosure_regular_inv_of_mapM_mem
          ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
          x₀ _ _ hmap htcl₀
          with ⟨fuelBody₀, first₀, result3₀, _happly₀, hfuel₀, htc_body₀, _hsub₀, hfirst₀_eq⟩
        -- Synchronization is used only under a clean-result assumption for `result1`.
        -- Keep it deferred to avoid requiring a global clean fact at this point.
        have _hsync1_of_clean :
            ∀ hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
              (∃ x pbody σcap,
                  Expr.toPExpr? body₀ = some pbody ∧
                  PFnTClosure.regular x pbody σcap ∈ tcls ∧
                  x₀ = x ∧
                  x₁ = x ∧
                  body₀ = body₁ ∧
                  agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory σcap env₀ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory θ₀1 σcap env₀ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory σcap env₁ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory θ₁1 σcap env₁)
              ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          exact
            stepFR_app_parrow_sync_from_clean
              (predSat := predSat)
              (ctx := (ctxAfter ctxᵢ result2))
              (res1 := result1)
              (st1 := st1) (st2 := st2) (p := p) (tcls := tcls)
              (μ₀ := c₁₀.memory) (μ₁ := c₁₁.memory)
              (θ₀ := θ₀1) (θ₁ := θ₁1)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              (env₀ := env₀) (env₁ := env₁)
              hetyp1 hclean1_e1 hres_agree1
        have _hextract_shared_of_sync :
            (∃ x pbody σcap,
                Expr.toPExpr? body₀ = some pbody ∧
                PFnTClosure.regular x pbody σcap ∈ tcls ∧
                x₀ = x ∧
                x₁ = x ∧
                body₀ = body₁) →
              ∃ x pbody σcap fuelBody first result3,
                Expr.toPExpr? body₀ = some pbody ∧
                PFnTClosure.regular x pbody σcap ∈ tcls ∧
                x₀ = x ∧
                x₁ = x ∧
                body₀ = body₁ ∧
                applyPFnTClosure .ioFree (PFnTClosure.regular x pbody σcap) st1 st2 p p1
                  etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok first ∧
                fuel' = Nat.succ fuelBody ∧
                typecheckExpr .ioFree
                  { ctxᵢ with
                    pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                    memEnv := result1.memEnv'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                    tagEnv := result1.tagEnv'
                    pureCtx := true
                    nextTag := result1.nextTag'
                    nextLoc := result1.nextLoc'
                    regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3 ∧
                isSubtype st2 result3.qualType = true ∧
                first =
                  { result3 with
                    qualType :=
                      normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3.qualType with poison := joinPoison p1 (joinPoison p result3.qualType.poison) } } := by
          intro hsync
          exact
            stepFR_app_parrow_extract_shared_member
              (ctx := ctxᵢ)
              (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              (x₀ := x₀) (x₁ := x₁)
              (body₀ := body₀) (body₁ := body₁)
              hmap hsync
        have _sync_extract_of_clean :
            ∀ hclean1_e1 :
                qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType,
              (∃ x pbody σcap fuelBody firstShared result3Shared,
                  Expr.toPExpr? body₀ = some pbody ∧
                  PFnTClosure.regular x pbody σcap ∈ tcls ∧
                  x₀ = x ∧
                  x₁ = x ∧
                  body₀ = body₁ ∧
                  agreeCapturedEnv predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory c₁₁.memory θ₀1 θ₁1 σcap env₀ env₁ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory σcap env₀ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₀.memory θ₀1 σcap env₀ ∧
                  MemberVarsRegimeEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory σcap env₁ ∧
                  MemberCvcrEvidence predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    c₁₁.memory θ₁1 σcap env₁ ∧
                  applyPFnTClosure .ioFree (PFnTClosure.regular x pbody σcap) st1 st2 p p1
                    etyp2 p2 pred2 ctxᵢ result1 fuel' = .ok firstShared ∧
                  fuel' = Nat.succ fuelBody ∧
                  typecheckExpr .ioFree
                    { ctxᵢ with
                      pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                      memEnv := result1.memEnv'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                      tagEnv := result1.tagEnv'
                      pureCtx := true
                      nextTag := result1.nextTag'
                      nextLoc := result1.nextLoc'
                      regime := result1.regime' } (PExpr.toExpr pbody) fuelBody = .ok result3Shared ∧
                  isSubtype st2 result3Shared.qualType = true ∧
                  firstShared =
                    { result3Shared with
                      qualType :=
                        normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) } })
              ∨ (¬ internalPoisonClean result1.qualType) := by
          intro hclean1_e1
          rcases _hsync1_of_clean hclean1_e1 with hsync | hdirty
          · left
            rcases hsync with ⟨x, pbody, σcap, htoPExpr, hmem, hx₀, hx₁, hbody, hcap, hmv₀, hmc₀, hmv₁, hmc₁⟩
            rcases applyPFnTClosure_regular_inv_of_mapM_mem
                ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
                x pbody σcap hmap hmem with
              ⟨fuelBody, firstShared, result3Shared, happly', hfuel', htc', hsub', hfirst'⟩
            exact ⟨x, pbody, σcap, fuelBody, firstShared, result3Shared, htoPExpr,
              hmem, hx₀, hx₁, hbody, hcap, hmv₀, hmc₀, hmv₁, hmc₁, happly', hfuel', htc', hsub', hfirst'⟩
          · right
            exact hdirty
        -- htc_body₀ : typecheckExpr bodyCtx (PExpr.toExpr pbody₀) fuelBody₀ = .ok result3₀
        -- hfuel₀ : fuel' = Nat.succ fuelBody₀
        -- Phase E: Simplify using cf₀ = c₁₀, cf₁ = c₁₁ (pure closure config preservation)
        subst heq_cfg₀ heq_cfg₁
        -- Phase F: Per-member preservation via mapM transport
        have hwf_result1 : wfTypeResult result1 := by
          simp only [ctxAfter, wfTypeContext, wfTypeResult] at hwf1 ⊢
          exact hwf1
        have hresults_wf :
            ∀ r, r ∈ results → wfTypeResult r :=
          mapM_applyPFnTClosure_forall_wfTypeResult'
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            hwf_result1
            (tcls := tcls) (results := results) hmap
        have hTm1_ctx : wfTagMeaningCtx tm (ctxAfter ctxᵢ result1) := by
          simpa [ctxAfter] using _hTm1
        have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
          simpa [hqt2] using (_hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
        have hresults_tm :
            ∀ r, r ∈ results → wfTagMeaningCtx tm (ctxAfter ctxᵢ r) :=
          mapM_applyPFnTClosure_forall_wfTagMeaningCtx
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx _hresTm1 hetyp1 hresTm2_arg hmap
        have hresults_regime :
            ∀ r, r ∈ results →
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          have htagR1_ctx :
              regimeConsistentWithCtx (ctxAfter ctxᵢ result1) := by
            simpa [ctxAfter] using htagR1
          exact
            mapM_applyPFnTClosure_forall_regimeConsistentWithCtx
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result1 := result1) (fuel := fuel')
              (tcls := tcls) (results := results)
              htagR1_ctx hmap
        have hresults_qtm :
            ∀ r, r ∈ results → QTypRespectsTagMeaning tm r.qualType :=
          mapM_applyPFnTClosure_forall_QTypRespectsTagMeaning
            (tm := tm)
            (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
            (tcls := tcls)
            (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
            (result1 := result1) (fuel := fuel')
            (results := results)
            hTm1_ctx _hresTm1 hetyp1 hresTm2_arg hmap
        have hfirst_in_results : first ∈ results := by
          simp [heq_results]
        have h_first_wf : wfTypeResult first := hresults_wf first hfirst_in_results
        have h_first_tm : wfTagMeaningCtx tm (ctxAfter ctxᵢ first) := hresults_tm first hfirst_in_results
        have h_first_regime :
            regimeConsistentWithCtx (ctxAfter ctxᵢ first) :=
          hresults_regime first hfirst_in_results
        have h_first_qtm : QTypRespectsTagMeaning tm first.qualType := by
          intro qt' k d hinq hqd
          exact hresults_qtm first hfirst_in_results hinq hqd
        have h_rest_wf : ∀ r ∈ rest, wfTypeResult r := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_wf r hmem_results
        have h_rest_regime :
            ∀ r ∈ rest,
              regimeConsistentWithCtx (ctxAfter ctxᵢ r) := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          exact hresults_regime r hmem_results
        have h_rest_qtm : ∀ r ∈ rest, QTypRespectsTagMeaning tm r.qualType := by
          intro r hr
          have hmem_results : r ∈ results := by
            have : r ∈ first :: rest := by simp [hr]
            simpa [heq_results] using this
          intro qt' k d hinq hqd
          exact hresults_qtm r hmem_results hinq hqd
        have h_mem_join :
            ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l :=
          joinTypeResults_mem_contains_head_or_rest
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_regime_bound_le_join : res.regime'.bound ≤ first.regime'.bound :=
          joinTypeResults_regime_bound_le_head
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res) h_join
        have h_tag_join :
            tagEnvConsistentWithRegime (ctxAfter ctxᵢ res).tagEnv (ctxAfter ctxᵢ res).regime :=
          joinTypeResults_tagEnvConsistentWithRegime
            (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
            h_join h_first_regime h_rest_regime
        -- Case split: clean vs not-clean for result1
        by_cases hclean1_e1 :
            qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType
        · -- Clean case: shared pure-body IH (TODO: fill later)
          rcases _sync_extract_of_clean hclean1_e1 with hshared | hdirty
          · rcases hshared with
              ⟨x, pbody, σcap, fuelBody, firstShared, result3Shared,
                htoPExpr, hmem, hx₀, hx₁, hbody,
                hcap, hmemberVars₀, hmemberCvcr₀, hmemberVars₁, hmemberCvcr₁,
                happly, hfuel, htcBody, hsubBody, hfirstShared⟩
            -- Phase 1: Define bodyCtx (parrow: pureCtx := true, pc order swapped vs arrow)
            let bodyCtx : TypeContext :=
              { ctxᵢ with
                pc := joinPoison p (joinPoison ctxᵢ.pc p1)
                memEnv := result1.memEnv'
                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                  ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                tagEnv := result1.tagEnv'
                pureCtx := true
                nextTag := result1.nextTag'
                nextLoc := result1.nextLoc'
                regime := result1.regime' }
            have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
            have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
            have hfuel_lt : fuelBody < Nat.succ (Nat.succ fuel') := by
              have hfuel_lt' : fuelBody < fuel' := by
                rw [hfuel]
                exact Nat.lt_succ_self fuelBody
              exact Nat.lt_trans hfuel_lt' (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ := by
              have hresTm2_arg : QTypRespectsTagMeaning tm ⟨etyp2, p2, pred2⟩ := by
                simpa [hqt2] using (_hresTm2 : QTypRespectsTagMeaning tm result2.qualType)
              have hargTm' :
                  ∀ {qt' : QTyp} {k : Tag} {d : GuardDesc},
                    QTypInQTyp qt' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                    qtypGuardDesc? qt' = some (k, d) →
                    tm.lookup k = some d :=
                QTypRespectsTagMeaning_transport_etyp_pred
                  (tm := tm)
                  (qt := ⟨etyp2, p2, pred2⟩)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  hresTm2_arg rfl rfl
              exact fun {qt'} {k} {d} hinq hqd => hargTm' hinq hqd
            have hTmBody : wfTagMeaningCtx tm bodyCtx := by
              have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
              have hTmBody' :=
                wfTagMeaningCtx_pclosure_body
                  (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                  (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                  (p := p) (tcls := tcls)
                  (xFun := x) (pbody := pbody) (σcap := σcap)
                  (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  _hTm1 hresTm1' hetyp1 hmem hargTm
              simp only [wfTagMeaningCtx, bodyCtx] at hTmBody' ⊢
              exact hTmBody'
            have htcBody' : typecheck .ioFree bodyCtx (PExpr.toExpr pbody) fuelBody = .ok result3Shared := by
              simp only [bodyCtx, typecheck, hx₀]
              exact htcBody
            have hIH_body :=
              IH fuelBody hfuel_lt (PExpr.toExpr pbody) bodyCtx hTmBody result3Shared htcBody'
            have hwfBodyCtx : wfTypeContext bodyCtx := by
              simpa [bodyCtx, ctxAfter, wfTypeContext] using hwf1
            -- Phase 2: runtimeInstantiatesCtx for both runs
            have hric_body₀ :
                runtimeInstantiatesCtx bodyCtx cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              let ctxCapBase : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
              have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
              have hric_cap_base :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) cf₀.memory env₀ θ₀1 := by
                constructor
                · intro l a hlookup
                  exact hric₀1.1 l a hlookup
                · intro y qt hlookup
                  exact
                    agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt hlookup
              have hric_body₀' :
                  runtimeInstantiatesCtx
                    { ctxCapBase with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    cf₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₀) (μ := cf₀.memory) (ρ := env₀) (θ := θ₀1)
                  hric_cap_base harg₀_typed
                  (agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap))
              simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter] using hric_body₀'
            have hric_body₁ :
                runtimeInstantiatesCtx bodyCtx cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              let ctxCapBase : TypeContext :=
                { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcap }
              have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
                simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
              have hric_cap_base :
                  runtimeInstantiatesCtx (ctxAfter ctxCapBase result1) cf₁.memory env₁ θ₁1 := by
                constructor
                · intro l a hlookup
                  exact hric₁1.1 l a hlookup
                · intro y qt hlookup
                  exact
                    agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt hlookup
              have hric_body₁' :
                  runtimeInstantiatesCtx
                    { ctxCapBase with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime'
                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x₀
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 :=
                runtimeInstantiatesCtx_closure_body
                  (ctx := ctxCapBase) (result2 := result1) (x := x₀) (tenv := σcap)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (argVal := v₂₁) (μ := cf₁.memory) (ρ := env₁) (θ := θ₁1)
                  hric_cap_base harg₁_typed
                  (agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap))
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [runtimeInstantiatesCtx, bodyCtx, ctxCapBase, ctxAfter, henv_update]
                using hric_body₁'
            -- Phase 3: regime infrastructure
            have h_mono1 :
                Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
              regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
            have htagR_body : regimeConsistentWithCtx bodyCtx := by
              simpa [bodyCtx, ctxAfter, regimeConsistentWithCtx] using htagR1
            have hRbound_body : regimeBounded bodyCtx.regime := by
              exact
                regimeBounded_of_monotoneStep
                  (ctxAfter ctxᵢ result2).regime result1.regime'
                  hRbound2 h_mono1
            -- Phase 4: consistentWithRegime for both runs
            have hcwr_body₀ :
                consistentWithRegime predSat bodyCtx.regime bodyCtx
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
              have hlocs_src₀ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' cf₀.memory θ₀1 (l, qt) := by
                intro l qt k hlookup hguard hRdef
                exact hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_cap₀ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₀.memory env₀ (x, qt) := by
                intro x qt k hlookup hguard hRdef
                rcases
                    agreeCapturedEnv_ofCaptured_lookup_typed_left (hcap := hcap) x qt hlookup
                  with ⟨v, hlookup_v, _htyp_v⟩
                exact hmemberVars₀ x qt k v hlookup hlookup_v hguard hRdef
              have hvars_arg₀ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ := by
                  have hvalc₂ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        result2.qualType c₂'₀.memory θ₀2 v₂₀ := by
                    simpa [ctxAfter] using _hvalc₂₀
                  exact
                    valueConsistentWithRegime_transport_pred
                      (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                      (qt := result2.qualType)
                      (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                      (by simp [hqt2]) (hetyp := by simp [hqt2])
                      hvalc₂
                have hvalc_arg_e1 :
                    valueConsistentWithRegime predSat result1.regime'
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                have hlookup_v_body :
                    (env₀.update x₀ v₂₀).lookup x₀ = some v₂₀ := by
                  simp [VarEnv.update, VarEnv.lookup]
                have hvars_arg_e1R_mem₂ :
                    varsRegime predSat result1.regime' c₂'₀.memory
                      (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  exact
                    varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₀) (k := k)
                      hlookup_v_body hguard hRdef hvalc_arg_e1
                have hPredSat_mem :
                    ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                  predSat_mem_noPred_compat hpredlaws θ₀1
                have hqtypPredHolds_mem :
                    ∀ (qt : QTyp) (v : Value),
                      qtypPredHolds predSat qt c₂'₀.memory v ↔ qtypPredHolds predSat qt cf₀.memory v := by
                  intro qt v
                  constructor <;> intro h
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).1 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).1 hs)
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).2 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₀.memory cf₀.memory v).2 hs)
                exact
                  varsRegime_transport_predHolds
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₀.memory) (μ' := cf₀.memory)
                    (ρ := env₀.update x₀ v₂₀)
                    (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                    hqtypPredHolds_mem hvars_arg_e1R_mem₂
              exact
                consistentWithRegime_closure_body_start
                  (predSat := predSat)
                  (ctx := ctxᵢ) (result1 := result1)
                  (σcap := σcap) (xArg := x₀)
                  (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := cf₀.memory) (θ := θ₀1) (ρcap := env₀) (vArg := v₂₀)
                  hlocs_src₀ hvars_cap₀ hvars_arg₀
                    hmemberCvcr₀
                  (closureCapturedVarsRegime_transport_μ_θ
                    (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory cf₀.memory)
                    hθext₀1.1
                    (closureCapturedVarsRegime_monotone h_mono1
                      (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                        (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₀))))
            have hcwr_body₁ :
                consistentWithRegime predSat bodyCtx.regime bodyCtx
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hlocs_src₁ :
                  ∀ l qt k,
                    result1.memEnv'.lookup l = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    locsRegime predSat result1.regime' cf₁.memory θ₁1 (l, qt) := by
                intro l qt k hlookup hguard hRdef
                exact hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
              have hvars_cap₁ :
                  ∀ x qt k,
                    (VarTypeEnv.ofCaptured σcap).lookup x = some qt →
                    qtypGuardTag qt = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₁.memory env₁ (x, qt) := by
                intro x qt k hlookup hguard hRdef
                rcases
                    agreeCapturedEnv_ofCaptured_lookup_typed_right (hcap := hcap) x qt hlookup
                  with ⟨v, hlookup_v, _htyp_v⟩
                exact hmemberVars₁ x qt k v hlookup hlookup_v hguard hRdef
              have hvars_arg₁ :
                  ∀ k,
                    qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                    result1.regime'.lookup? k ≠ none →
                    varsRegime predSat result1.regime' cf₁.memory
                      (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                intro k hguard hRdef
                have hvalc_arg_e2 :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ := by
                  have hvalc₂ :
                      valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                        result2.qualType c₂'₁.memory θ₁2 v₂₁ := by
                    simpa [ctxAfter] using _hvalc₂₁
                  exact
                    valueConsistentWithRegime_transport_pred
                      (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                      (qt := result2.qualType)
                      (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                      (by simp [hqt2]) (hetyp := by simp [hqt2])
                      hvalc₂
                have hvalc_arg_e1 :
                    valueConsistentWithRegime predSat result1.regime'
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                  valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
                have hlookup_v_body :
                    (env₁.update x₀ v₂₁).lookup x₀ = some v₂₁ := by
                  simp [VarEnv.update, VarEnv.lookup]
                have hvars_arg_e1R_mem₂ :
                    varsRegime predSat result1.regime' c₂'₁.memory
                      (env₁.update x₀ v₂₁) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
                  exact
                    varsRegime_of_valueConsistentWithRegime_active
                      (predSat := predSat) (R := result1.regime')
                      (μ := c₂'₁.memory) (ρ := env₁.update x₀ v₂₁)
                      (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                      (v := v₂₁) (k := k)
                      hlookup_v_body hguard hRdef hvalc_arg_e1
                have hPredSat_mem :
                    ∀ (k : Tag) (μ μ' : Memory) (v : Value), predSat k μ v ↔ predSat k μ' v :=
                  predSat_mem_noPred_compat hpredlaws θ₁1
                have hqtypPredHolds_mem :
                    ∀ (qt : QTyp) (v : Value),
                      qtypPredHolds predSat qt c₂'₁.memory v ↔ qtypPredHolds predSat qt cf₁.memory v := by
                  intro qt v
                  constructor <;> intro h
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).1 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).1 hs)
                  · cases h with
                    | noPred_ok hp =>
                        exact qtypPredHolds.noPred_ok hp
                    | guardClosure_ok hp hs =>
                        exact qtypPredHolds.guardClosure_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).2 hs)
                    | guardOnly_ok hp hs =>
                        exact qtypPredHolds.guardOnly_ok hp
                          ((hPredSat_mem _ c₂'₁.memory cf₁.memory v).2 hs)
                exact
                  varsRegime_transport_predHolds
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₁.memory) (μ' := cf₁.memory)
                    (ρ := env₁.update x₀ v₂₁)
                    (entry := (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩))
                    hqtypPredHolds_mem hvars_arg_e1R_mem₂
              have hcwr_body₁' :
                  consistentWithRegime predSat bodyCtx.regime bodyCtx
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                exact
                  consistentWithRegime_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ := cf₁.memory) (θ := θ₁1) (ρcap := env₁) (vArg := v₂₁)
                    hlocs_src₁ hvars_cap₁ hvars_arg₁
                    hmemberCvcr₁
                    (closureCapturedVarsRegime_transport_μ_θ
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory cf₁.memory)
                      hθext₁1.1
                      (closureCapturedVarsRegime_monotone h_mono1
                        (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                          (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₂₁))))
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [henv_update] using hcwr_body₁'
            -- Phase 5: agreeOnClean for body start
            have hagree_body_start :
                agreeOnClean predSat bodyCtx.regime bodyCtx
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
              have hmem_agree :
                  ∀ l qt,
                    result1.memEnv'.lookup l = some qt →
                    qtypCleanUnder result1.regime' qt →
                    agreeLocUnder predSat result1.regime' cf₀.memory cf₁.memory θ₀1 θ₁1 (l, qt) := by
                intro l qt hlookup hclean
                exact hagree1.1 l qt (by simpa [ctxAfter] using hlookup) hclean
              have hagree_body_start' :
                  agreeOnClean predSat bodyCtx.regime bodyCtx
                    cf₀.memory (env₀.update x₀ v₂₀) θ₀1
                    cf₁.memory (env₁.update x₀ v₂₁) θ₁1 := by
                have harg_agree :
                    qtypCleanUnder result1.regime' ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ →
                      agreeValueUnder predSat result1.regime'
                        cf₀.memory cf₁.memory θ₀1 θ₁1
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                  intro hclean_arg
                  have hclean_arg_e2 :
                      qtypCleanUnder (ctxAfter ctxᵢ result2).regime
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
                    cleanUnder_of_monotone h_mono1 hclean_arg
                  have hclean_res2 :
                      qtypCleanUnder (ctxAfter ctxᵢ result2).regime result2.qualType := by
                    cases hclean_arg_e2 with
                    | clean hpoison =>
                        have hp2_false : p2 = false := (joinPoison_eq_false hpoison).2
                        have hqt2_poison : result2.qualType.poison = false := by
                          simp [hqt2, hp2_false]
                        exact qtypCleanUnder.clean hqt2_poison
                    | guard k htag hk hnotfun =>
                        have htag_orig : qtypGuardTag result2.qualType = some k := by
                          simp [qtypGuardTag] at htag
                          simp [hqt2, qtypGuardTag, htag]
                        have hnotfun' : result2.qualType.etyp.isFunctionType = false := by
                          simpa [hqt2] using hnotfun
                        exact qtypCleanUnder.guard k htag_orig hk hnotfun'
                  have hval_agree_e2 :
                      agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        result2.qualType v₂₀ v₂₁ :=
                    hres_agree2 hclean_res2
                  have hagree_arg_e2 :
                      agreeValueUnder predSat (ctxAfter ctxᵢ result2).regime
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ := by
                    refine agreeValueUnder_transport_clean hclean_arg_e2 ?_ ?_ hval_agree_e2
                    · simp [hqt2]
                    · intro hpoison
                      have hjoin : joinPoison ctxᵢ.pc p2 = false := by
                        simpa using hpoison
                      exact by simpa [hqt2] using (joinPoison_eq_false hjoin).2
                  have hagree_arg_e2_to_e1 :
                      agreeValueUnder predSat result1.regime'
                        c₂'₀.memory c₂'₁.memory θ₀2 θ₁2
                        ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ v₂₀ v₂₁ :=
                    agreeValueUnder_clean_monotoneRegime h_mono1 hclean_arg hagree_arg_e2
                  exact
                    agreeValueUnder_clean_extends_transport_mem
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 c₂'₀.memory cf₀.memory)
                      (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 c₂'₁.memory cf₁.memory)
                      hclean_arg hθext₀1.1 hθext₁1.1 hagree_arg_e2_to_e1
                exact
                  agreeOnClean_closure_body_start
                    (predSat := predSat)
                    (ctx := ctxᵢ) (result1 := result1)
                    (σcap := σcap) (xArg := x₀)
                    (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                    (θ₀ := θ₀1) (θ₁ := θ₁1)
                    (ρcap₀ := env₀) (ρcap₁ := env₁)
                    (vArg₀ := v₂₀) (vArg₁ := v₂₁)
                    hmem_agree hcap harg_agree
              have hx' : x₁ = x₀ := hx₁.trans hx₀.symm
              have henv_update :
                  env₁.update x₀ v₂₁ = env₁.update x₁ v₂₁ := by
                simp [hx']
              simpa [henv_update] using hagree_body_start'
            -- Phase 6: wfConfig for body init
            have hwfcfg_body_init₀ :
                wfConfig
                  { memory := cf₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := cf₀.nextAddr
                    pureMode := true } := by
              have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
                (wfConfig_preserved .ioFree e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
              have hnext₂_to₁ : c₂'₀.nextAddr ≤ cf₀.nextAddr :=
                terminatesTo_nextAddr_mono .ioFree e1 c₂'₀ cf₀ (Value.peClosure x₀ body₀ env₀) ht₀_e1
              have hv₂₀_wf : wfValue cf₀.nextAddr v₂₀ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
              have hv₀_closure_wf : wfValue cf₀.nextAddr (Value.peClosure x₀ body₀ env₀) :=
                (wfConfig_preserved .ioFree e1 _ cf₀ _ ht₀_e1 hwfcf₂₀).2
              have henv₀_wf : wfVarEnv cf₀.nextAddr env₀ := by
                cases hv₀_closure_wf with
                | peClosure _ _ _ henv => exact henv
              constructor
              · intro a ha
                exact hwfcf₁₀.1 a ha
              · simpa [VarEnv.update] using (wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf)
            have hwfcfg_body_init₁ :
                wfConfig
                  { memory := cf₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := cf₁.nextAddr
                    pureMode := true } := by
              have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
                (wfConfig_preserved .ioFree e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
              have hnext₂_to₁ : c₂'₁.nextAddr ≤ cf₁.nextAddr :=
                terminatesTo_nextAddr_mono .ioFree e1 c₂'₁ cf₁ (Value.peClosure x₁ body₁ env₁) ht₁_e1
              have hv₂₁_wf : wfValue cf₁.nextAddr v₂₁ :=
                wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
              have hv₁_closure_wf : wfValue cf₁.nextAddr (Value.peClosure x₁ body₁ env₁) :=
                (wfConfig_preserved .ioFree e1 _ cf₁ _ ht₁_e1 hwfcf₂₁).2
              have henv₁_wf : wfVarEnv cf₁.nextAddr env₁ := by
                cases hv₁_closure_wf with
                | peClosure _ _ _ henv => exact henv
              constructor
              · intro a ha
                exact hwfcf₁₁.1 a ha
              · simpa [VarEnv.update] using (wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf)
            -- Phase 7: terminatesTo for body (pureMode := true)
            have ht₀_body' :
                terminatesTo .ioFree (PExpr.toExpr pbody)
                  { memory := cf₀.memory
                    varEnv := env₀.update x₀ v₂₀
                    nextAddr := cf₀.nextAddr
                    pureMode := true } evalCfg₀ o₀ := by
              have hbody_eq : PExpr.toExpr pbody = body₀ :=
                PExpr_toExpr_of_toPExpr?_some body₀ pbody htoPExpr
              rw [hbody_eq]
              exact ht₀_body
            have ht₁_body' :
                terminatesTo .ioFree (PExpr.toExpr pbody)
                  { memory := cf₁.memory
                    varEnv := env₁.update x₁ v₂₁
                    nextAddr := cf₁.nextAddr
                    pureMode := true } evalCfg₁ o₁ := by
              have hbody_eq : PExpr.toExpr pbody = body₀ :=
                PExpr_toExpr_of_toPExpr?_some body₀ pbody htoPExpr
              rw [hbody_eq, hbody]
              exact ht₁_body
            -- Phase 8: Apply body IH
            have hstep_body := hIH_body hpredlaws hTmBody
              cf₀.memory cf₁.memory (env₀.update x₀ v₂₀) (env₁.update x₁ v₂₁) θ₀1 θ₁1
              evalCfg₀ evalCfg₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwfBodyCtx hric_body₀ hric_body₁ htagR_body hRbound_body
              hcwr_body₀ hcwr_body₁ hagree_body_start
              cf₀.nextAddr cf₁.nextAddr true
              hwfcfg_body_init₀ hwfcfg_body_init₁ ht₀_body' ht₁_body'
            rcases hstep_body with
              ⟨_hresTm_body,
                ⟨θ₀_body, θ₁_body, _hθext₀_body, _hθext₁_body,
                  _hv_body₀_typed, _hv_body₁_typed, _hTm_body, _hwf_body_after,
                  _hwfcfg_body_final₀, _hwfcfg_body_final₁,
                  _hric_body_final₀, _hric_body_final₁, _htagR_body_final,
                  _hcwr_body_final₀, _hcwr_body_final₁, hagree_body_after,
                  _hvalc_body₀, _hvalc_body₁, _hres_agree_body⟩⟩
            -- Pure body preserves memory: cf₀.memory = evalCfg₀.memory
            have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
              obtain ⟨fuel_b₀, verbose_b₀, hbeval_b₀⟩ := ht₀_body'
              have hworld₀ := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval_b₀
              exact (beval_pure_memory_eq .ioFree (PExpr.toExpr pbody) fuel_b₀ _ evalCfg₀ o₀ verbose_b₀
                LeanProofs.defaultWorld LeanProofs.defaultWorld pbody
                (toExpr_toPExpr? pbody) rfl hworld₀).symm
            have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
              obtain ⟨fuel_b₁, verbose_b₁, hbeval_b₁⟩ := ht₁_body'
              have hworld₁ := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval_b₁
              exact (beval_pure_memory_eq .ioFree (PExpr.toExpr pbody) fuel_b₁ _ evalCfg₁ o₁ verbose_b₁
                LeanProofs.defaultWorld LeanProofs.defaultWorld pbody
                (toExpr_toPExpr? pbody) rfl hworld₁).symm
            -- Phase 9: Transport agreeOnClean from shared body result to joined res
            have hAgree_out_body :
                agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
              have hsrc_mem : firstShared ∈ first :: rest := by
                rcases applyPFnTClosure_ok_of_mem_mapM
                    (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                    (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                    (result2 := result1) (fuel := fuel')
                    (tcls := tcls) (results := results)
                    (tcl := PFnTClosure.regular x pbody σcap)
                    hmap hmem with
                  ⟨r, hr_mem, happly_r⟩
                have hr_eq : r = firstShared := by
                  have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                    simpa [happly_r] using happly
                  exact Except.ok.inj hEq
                subst hr_eq
                simpa [heq_results] using hr_mem
              have hagree_src :
                  agreeOnClean predSat (ctxAfter ctxᵢ firstShared).regime (ctxAfter ctxᵢ firstShared)
                    cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body := by
                have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                  regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3Shared htcBody'
                have hres1_to_src_mono :
                    Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                      (ctxAfter ctxᵢ firstShared).regime := by
                  simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                constructor
                · intro l qt hlookup hclean
                  have hlookup_body :
                      (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstShared] using hlookup
                  have hclean_body :
                      qtypCleanUnder (ctxAfter bodyCtx result3Shared).regime qt := by
                    simpa [ctxAfter, hfirstShared] using hclean
                  have hloc_agree_body := hagree_body_after.1 l qt hlookup_body hclean_body
                  cases hloc_agree_body with
                  | both_unrealized _ _ hnone₀ hnone₁ =>
                      exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                  | agree_values _ _ a₀' a₁' n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree_val =>
                      have hlookup₀' : cf₀.memory.lookup a₀' = some n₀ := by
                        simpa [hmem₀_eq] using hlookup₀
                      have hlookup₁' : cf₁.memory.lookup a₁' = some n₁ := by
                        simpa [hmem₁_eq] using hlookup₁
                      have hagree_val' :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀_body θ₁_body qt
                            (Value.num n₀) (Value.num n₁) := by
                        simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hagree_val
                      exact
                        agreeLocUnder.agree_values l qt a₀' a₁' n₀ n₁
                          hreal₀ hreal₁ hlookup₀' hlookup₁' hagree_val'
                · intro x qt hlookup hclean
                  have hclean_res1 :
                      qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime qt :=
                    cleanUnder_of_monotone hres1_to_src_mono hclean
                  have hvar_agree1 := hagree1.2 x qt hlookup hclean_res1
                  cases hvar_agree1 with
                  | both_none _ _ hnone₀ hnone₁ =>
                      have hnone₀' : cf₀.varEnv.lookup x = none := by
                        simpa [hvar₀_eq] using hnone₀
                      have hnone₁' : cf₁.varEnv.lookup x = none := by
                        simpa [hvar₁_eq] using hnone₁
                      exact agreeVarUnder.both_none x qt hnone₀' hnone₁'
                  | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree_val1 =>
                      have hlookup₀' : cf₀.varEnv.lookup x = some v₀ := by
                        simpa [hvar₀_eq] using hlookup₀
                      have hlookup₁' : cf₁.varEnv.lookup x = some v₁ := by
                        simpa [hvar₁_eq] using hlookup₁
                      have hagree_src_regime :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀1 θ₁1 qt v₀ v₁ :=
                        agreeValueUnder_clean_monotoneRegime hres1_to_src_mono hclean hagree_val1
                      have hagree_src_final :
                          agreeValueUnder predSat (ctxAfter ctxᵢ firstShared).regime
                            cf₀.memory cf₁.memory θ₀_body θ₁_body qt v₀ v₁ :=
                        by
                          have hqtypPredHolds_mem_app_out₀ :
                              ∀ (qt' : QTyp) (v' : Value),
                                qtypPredHolds predSat qt' cf₀.memory v' ↔
                                  qtypPredHolds predSat qt' cf₀.memory v' :=
                            qtypPredHolds_mem_compat_of_predSatLaws
                              (hpredlaws := hpredlaws) (θ := θ₀1)
                              (μ := cf₀.memory) (μ' := cf₀.memory)
                          have hqtypPredHolds_mem_app_out₁ :
                              ∀ (qt' : QTyp) (v' : Value),
                                qtypPredHolds predSat qt' cf₁.memory v' ↔
                                  qtypPredHolds predSat qt' cf₁.memory v' :=
                            qtypPredHolds_mem_compat_of_predSatLaws
                              (hpredlaws := hpredlaws) (θ := θ₁1)
                              (μ := cf₁.memory) (μ' := cf₁.memory)
                          exact
                            agreeValueUnder_clean_extends_transport_mem
                              hqtypPredHolds_mem_app_out₀ hqtypPredHolds_mem_app_out₁
                              hclean _hθext₀_body.1 _hθext₁_body.1 hagree_src_regime
                      exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀' hlookup₁' hagree_src_final
              have h_clean_res_to_src :
                  ∀ qt,
                    qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                    qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt := by
                intro qt hclean
                cases hclean with
                | clean hpoison =>
                    exact qtypCleanUnder.clean hpoison
                | guard k htag hk hnotfun =>
                    have hk_src :
                        (ctxAfter ctxᵢ firstShared).regime.lookup? k = some true :=
                      joinTypeResults_lookup_member_regime_compat
                        (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                        h_join hsrc_mem k true hk
                    exact qtypCleanUnder.guard k htag hk_src hnotfun
              have h_mem_from_src_or_unrealized :
                  ∀ l qt,
                    (ctxAfter ctxᵢ res).memEnv.lookup l = some qt →
                    qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                    ((∃ qt_src,
                        (ctxAfter ctxᵢ firstShared).memEnv.lookup l = some qt_src ∧
                        qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src ∧
                        qt.etyp = qt_src.etyp ∧
                        (qt.poison = false → qt_src.poison = false)) ∨
                      (θ₀_body.lookup l = none ∧ θ₁_body.lookup l = none)) := by
                intro l qt hlookup hclean
                by_cases hlookup_src_none : (ctxAfter ctxᵢ firstShared).memEnv.lookup l = none
                · right
                  have hlookup_body_none :
                      (ctxAfter bodyCtx result3Shared).memEnv.lookup l = none := by
                    simpa [ctxAfter, hfirstShared] using hlookup_src_none
                  have hnot_contains_body :
                      ¬ (ctxAfter bodyCtx result3Shared).memEnv.contains l := by
                    intro hcontains
                    have hmem' : l ∈ (ctxAfter bodyCtx result3Shared).memEnv :=
                      (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                    have hlookup_isSome :
                        ((ctxAfter bodyCtx result3Shared).memEnv[l]?).isSome = true :=
                      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem'
                    have hlookup_get_none :
                        (ctxAfter bodyCtx result3Shared).memEnv[l]? = none := by
                      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup_body_none
                    simp [hlookup_get_none] at hlookup_isSome
                  have htheta₀_none :
                      θ₀_body.lookup l = none :=
                    theta_not_contains_if_not_in_memEnv
                      (ctx := (ctxAfter bodyCtx result3Shared))
                      (μ := evalCfg₀.memory) (ρ := evalCfg₀.varEnv) (θ := θ₀_body)
                      (l := l) _hric_body_final₀ hnot_contains_body
                  have htheta₁_none :
                      θ₁_body.lookup l = none :=
                    theta_not_contains_if_not_in_memEnv
                      (ctx := (ctxAfter bodyCtx result3Shared))
                      (μ := evalCfg₁.memory) (ρ := evalCfg₁.varEnv) (θ := θ₁_body)
                      (l := l) _hric_body_final₁ hnot_contains_body
                  exact ⟨htheta₀_none, htheta₁_none⟩
                · left
                  rcases Option.ne_none_iff_exists'.1 hlookup_src_none with ⟨qt_src, hlookup_src⟩
                  have hclean_src : qtypCleanUnder (ctxAfter ctxᵢ firstShared).regime qt_src :=
                    joinTypeResults_lookup_member_clean_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hclean hlookup_src
                  have hetyp_eq : qt.etyp = qt_src.etyp :=
                    joinTypeResults_lookup_member_etyp_compat
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hlookup_src
                  have hpoison_imp : qt.poison = false → qt_src.poison = false :=
                    joinTypeResults_lookup_member_poison_imp
                      (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                      h_join hsrc_mem l qt qt_src hlookup hlookup_src
                  exact ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
              have hlookup_back_res_to_src :
                  ∀ k b,
                    (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                    (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b := by
                intro k b hk
                exact
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem k b hk
              exact
                join_transport_agreeOnClean_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ)
                  (first := first)
                  (src := firstShared)
                  (rest := rest)
                  (res := res)
                  (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                  (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                  (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                  h_join hsrc_mem hagree_src h_clean_res_to_src h_mem_from_src_or_unrealized
                  (fun {σcap} {ρcap} h =>
                    memberVarsRegimeEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₀.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberCvcrEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₀.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberVarsRegimeEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₁.memory)
                      hlookup_back_res_to_src h)
                  (fun {σcap} {ρcap} h =>
                    memberCvcrEvidence_transport_lookup_back
                      (predSat := predSat)
                      (R := (ctxAfter ctxᵢ firstShared).regime)
                      (R' := (ctxAfter ctxᵢ res).regime)
                      (μ := cf₁.memory)
                      hlookup_back_res_to_src h)
            -- Phase 10: Pack elements (mirroring arrow case lines 24871-25234)
            have hOutPack_body :
                valueHasETyp θ₀_body o₀ res.qualType.etyp ∧
                valueHasETyp θ₁_body o₁ res.qualType.etyp ∧
                wfTagMeaningCtx tm (ctxAfter ctxᵢ res) ∧
                wfTypeContext (ctxAfter ctxᵢ res) ∧
                wfConfig cf₀ ∧
                wfConfig cf₁ ∧
                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀_body ∧
                runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁_body ∧
                regimeConsistentWithCtx (ctxAfter ctxᵢ res) ∧
                consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body ∧
                consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₁.memory cf₁.varEnv θ₁_body ∧
                agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
                  cf₀.memory cf₀.varEnv θ₀_body cf₁.memory cf₁.varEnv θ₁_body ∧
                valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                  res.qualType cf₀.memory θ₀_body o₀ ∧
                valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
                  res.qualType cf₁.memory θ₁_body o₁ ∧
                resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
                  cf₀.memory cf₁.memory θ₀_body θ₁_body res.qualType o₀ o₁ := by
              have hsrc_mem' : firstShared ∈ first :: rest := by
                rcases applyPFnTClosure_ok_of_mem_mapM
                    (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
                    (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
                    (result2 := result1) (fuel := fuel')
                    (tcls := tcls) (results := results)
                    (tcl := PFnTClosure.regular x pbody σcap)
                    hmap hmem with
                  ⟨r, hr_mem, happly_r⟩
                have hr_eq : r = firstShared := by
                  have hEq : (Except.ok r : Except String TypeResult) = Except.ok firstShared := by
                    simpa [happly_r] using happly
                  exact Except.ok.inj hEq
                subst hr_eq
                simpa [heq_results] using hr_mem
              have hfirstShared_etyp : firstShared.qualType.etyp = result3Shared.qualType.etyp := by
                rw [hfirstShared, normalizeAppResultByProvenance_etyp]
              have hres1_to_src_mono :
                  Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                    (ctxAfter ctxᵢ firstShared).regime := by
                have h_mono_body : Regime.monotoneStep bodyCtx.regime result3Shared.regime' :=
                  regime_monotone bodyCtx (PExpr.toExpr pbody) fuelBody result3Shared htcBody'
                simpa [bodyCtx, ctxAfter, hfirstShared] using h_mono_body
              have hlookup_back_res1_to_src :
                  ∀ k b,
                    (ctxAfter ctxᵢ firstShared).regime.lookup? k = some b →
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
                intro k b hk_src
                have hRdef_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k ≠ none := by
                  intro hnone
                  rw [hk_src] at hnone
                  contradiction
                have hRdef_res1 :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
                  hres1_to_src_mono.2.2 k hRdef_src
                cases hk_res1 : (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
                | none =>
                    exact False.elim (hRdef_res1 hk_res1)
                | some b1 =>
                    have hcases := hres1_to_src_mono.2.1 k b1 hk_res1
                    cases hcases with
                    | inl hk_src' =>
                        have hb_eq : b1 = b := by
                          have : some b1 = some b := by
                            calc
                              some b1 = (ctxAfter ctxᵢ firstShared).regime.lookup? k := hk_src'.symm
                              _ = some b := hk_src
                          exact Option.some.inj this
                        simp [hb_eq]
                    | inr hnone_src =>
                        rw [hnone_src] at hk_src
                        cases hk_src
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hAgree_out_body, ?_, ?_, ?_⟩
              · -- shared-member valueHasETyp -> joined valueHasETyp (run 0).
                have hv_src₀ : valueHasETyp θ₀_body o₀ firstShared.qualType.etyp := by
                  rw [hfirstShared_etyp]
                  exact _hv_body₀_typed
                exact
                  joinTypeResults_transport_valueHasETyp_from_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (θ := θ₀_body) (v := o₀)
                    h_join hsrc_mem' hv_src₀
              · -- shared-member valueHasETyp -> joined valueHasETyp (run 1).
                have hv_src₁ : valueHasETyp θ₁_body o₁ firstShared.qualType.etyp := by
                  rw [hfirstShared_etyp]
                  exact _hv_body₁_typed
                exact
                  joinTypeResults_transport_valueHasETyp_from_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (θ := θ₁_body) (v := o₁)
                    h_join hsrc_mem' hv_src₁
              · -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
                exact
                  join_transport_wfTagMeaningCtx
                    (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_first_tm
              · -- wfTypeContext (ctxAfter ctxᵢ res)
                exact
                  join_transport_wfTypeContext
                    (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_mem_join
                    (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf)
                    h_rest_wf
              · -- wfConfig cf₀ (= c₁₀ after subst)
                exact hwfcf₁₀
              · -- wfConfig cf₁ (= c₁₁ after subst)
                exact hwfcf₁₁
              · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hsrc_mem_to_res :
                    ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem'
                constructor
                · intro l a hθ
                  have hloc_src := _hric_body_final₀.1 l a hθ
                  rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                  have hcontains_src : firstShared.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstShared] using hcontains_src_body
                  refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                  simpa [hmem₀_eq] using hmem_contains
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  refine ⟨v, ?_⟩
                  constructor
                  · simpa [hvar₀_eq] using hlookup_v
                  · exact valueHasETyp_extends _hθext₀_body.1 hv_typ
              · -- shared-member runtimeInstantiatesCtx -> joined runtimeInstantiatesCtx (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                have hsrc_mem_to_res :
                    ∀ l, firstShared.memEnv'.contains l → res.memEnv'.contains l :=
                  joinTypeResults_mem_contains_of_member
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    h_join hsrc_mem'
                constructor
                · intro l a hθ
                  have hloc_src := _hric_body_final₁.1 l a hθ
                  rcases hloc_src with ⟨hcontains_src_body, hmem_contains⟩
                  have hcontains_src : firstShared.memEnv'.contains l := by
                    simpa [ctxAfter, hfirstShared] using hcontains_src_body
                  refine ⟨hsrc_mem_to_res l hcontains_src, ?_⟩
                  simpa [hmem₁_eq] using hmem_contains
                · intro x qt hlookup
                  have hlookup_ctx :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                    simpa [ctxAfter] using hlookup
                  rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                  refine ⟨v, ?_⟩
                  constructor
                  · simpa [hvar₁_eq] using hlookup_v
                  · exact valueHasETyp_extends _hθext₁_body.1 hv_typ
              · -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
                exact
                  join_transport_regimeConsistentWithCtx
                    (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                    h_join h_regime_bound_le_join h_tag_join h_first_regime
              · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hvar₀_eq : cf₀.varEnv = cf₀.varEnv := rfl
                have hpred_compat₀ :
                    ∀ (qt' : QTyp) (v' : Value),
                      qtypPredHolds predSat qt' cf₀.memory v' ↔
                        qtypPredHolds predSat qt' cf₀.memory v' :=
                  qtypPredHolds_mem_compat_of_predSatLaws
                    (hpredlaws := hpredlaws) (θ := θ₀1)
                    (μ := cf₀.memory) (μ' := cf₀.memory)
                have hcwr_src₀ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      (ctxAfter ctxᵢ firstShared) cf₀.memory cf₀.varEnv θ₀_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstShared] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstShared] using hRdef
                    have hloc_body :=
                      _hcwr_body_final₀.1 l qt k hlookup_body hguard_body hRdef_body
                    simpa [ctxAfter, hfirstShared, hmem₀_eq] using hloc_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                    | none =>
                        exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_src k b hk_src
                          rw [hk_back] at hnone
                          contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                        have hvar_src :
                            varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₀.memory cf₀.varEnv (x, qt) :=
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstShared).regime)
                            (μ := cf₀.memory) (ρ := cf₀.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                        simpa [hvar₀_eq] using hvar_src
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₀_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ _hθext₀_body.1
                      (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                    h_join hsrc_mem' hcwr_src₀
              · -- shared-member consistentWithRegime -> joined consistentWithRegime (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hvar₁_eq : cf₁.varEnv = cf₁.varEnv := rfl
                have hpred_compat₁ :
                    ∀ (qt' : QTyp) (v' : Value),
                      qtypPredHolds predSat qt' cf₁.memory v' ↔
                        qtypPredHolds predSat qt' cf₁.memory v' :=
                  qtypPredHolds_mem_compat_of_predSatLaws
                    (hpredlaws := hpredlaws) (θ := θ₁1)
                    (μ := cf₁.memory) (μ' := cf₁.memory)
                have hcwr_src₁ :
                    consistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      (ctxAfter ctxᵢ firstShared) cf₁.memory cf₁.varEnv θ₁_body := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro l qt k hlookup hguard hRdef
                    have hlookup_body :
                        (ctxAfter bodyCtx result3Shared).memEnv.lookup l = some qt := by
                      simpa [ctxAfter, hfirstShared] using hlookup
                    have hguard_body : qtypGuardTag qt = some k := by
                      simpa [ctxAfter, hfirstShared] using hguard
                    have hRdef_body :
                        (ctxAfter bodyCtx result3Shared).regime.lookup? k ≠ none := by
                      simpa [ctxAfter, hfirstShared] using hRdef
                    have hloc_body :=
                      _hcwr_body_final₁.1 l qt k hlookup_body hguard_body hRdef_body
                    simpa [ctxAfter, hfirstShared, hmem₁_eq] using hloc_body
                  · intro x qt k hlookup hguard hRdef
                    cases hk_src : (ctxAfter ctxᵢ firstShared).regime.lookup? k with
                    | none =>
                        exact False.elim (hRdef hk_src)
                    | some b =>
                        have hRdef_res1 :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                          intro hnone
                          have hk_back := hlookup_back_res1_to_src k b hk_src
                          rw [hk_back] at hnone
                          contradiction
                        have hlookup_res1_ctx :
                            (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                          simpa [ctxAfter] using hlookup
                        have hvar_res1 :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                        have hvar_res1_mem :
                            varsRegime predSat (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                        have hvar_src :
                            varsRegime predSat (ctxAfter ctxᵢ firstShared).regime
                              cf₁.memory cf₁.varEnv (x, qt) :=
                          varsRegime_transport_active_lookup_back
                            (predSat := predSat)
                            (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                            (R' := (ctxAfter ctxᵢ firstShared).regime)
                            (μ := cf₁.memory) (ρ := cf₁.varEnv) (entry := (x, qt))
                            hlookup_back_res1_to_src hguard hk_src hvar_res1_mem
                        simpa [hvar₁_eq] using hvar_src
                  · intro x qt v hlookup hlookup_v
                    have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                      (by rw [hvar₁_eq] at hlookup_v; exact hlookup_v)
                    exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ _hθext₁_body.1
                      (closureCapturedVarsRegime_transport_lookup_back hlookup_back_res1_to_src hcvcr)
                exact
                  joinTypeResults_transport_consistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                    h_join hsrc_mem' hcwr_src₁
              · -- shared-member valueConsistentWithRegime -> joined result qualType (run 0).
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hval_src₀ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      firstShared.qualType cf₀.memory θ₀_body o₀ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        evalCfg₀.memory θ₀_body o₀ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) _hvalc_body₀
                  simpa [ctxAfter, hfirstShared, hmem₀_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                    h_join hsrc_mem' hval_src₀
              · -- shared-member valueConsistentWithRegime -> joined result qualType (run 1).
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hval_src₁ :
                    valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstShared).regime
                      firstShared.qualType cf₁.memory θ₁_body o₁ := by
                  have hval_first :
                      valueConsistentWithRegime predSat (ctxAfter bodyCtx result3Shared).regime
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        evalCfg₁.memory θ₁_body o₁ :=
                    valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) _hvalc_body₁
                  simpa [ctxAfter, hfirstShared, hmem₁_eq] using hval_first
                exact
                  joinTypeResults_transport_valueConsistentWithRegime_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                    h_join hsrc_mem' hval_src₁
              · -- shared-member resultAgreesIfClean -> joined result qualType.
                have hmem₀_eq : cf₀.memory = evalCfg₀.memory := hmem₀_eq
                have hmem₁_eq : cf₁.memory = evalCfg₁.memory := hmem₁_eq
                have hres_agree_src :
                    resultAgreesIfClean predSat (ctxAfter ctxᵢ firstShared).regime
                      cf₀.memory cf₁.memory θ₀_body θ₁_body firstShared.qualType o₀ o₁ := by
                  have hres_agree_first :
                      resultAgreesIfClean predSat (ctxAfter bodyCtx result3Shared).regime
                        evalCfg₀.memory evalCfg₁.memory θ₀_body θ₁_body
                        (normalizeAppResultByProvenance (joinPoison p1 p)
                          { result3Shared.qualType with
                            poison := joinPoison p1 (joinPoison p result3Shared.qualType.poison) })
                        o₀ o₁ :=
                    resultAgreesIfClean_transport_normalizeAppResultByProvenance
                      (predSat := predSat) (R := (ctxAfter bodyCtx result3Shared).regime)
                      (p := p) (p1 := p1) (qt := result3Shared.qualType)
                      (μ₀ := evalCfg₀.memory) (μ₁ := evalCfg₁.memory)
                      (θ₀ := θ₀_body) (θ₁ := θ₁_body) (o₀ := o₀) (o₁ := o₁)
                      _hres_agree_body
                  simpa [ctxAfter, hfirstShared, hmem₀_eq, hmem₁_eq] using hres_agree_first
                exact
                  joinTypeResults_transport_resultAgreesIfClean_from_member
                    (predSat := predSat)
                    (ctx := ctxᵢ) (first := first) (src := firstShared) (rest := rest) (res := res)
                    (μ₀ := cf₀.memory) (μ₁ := cf₁.memory) (θ₀ := θ₀_body) (θ₁ := θ₁_body)
                    (o₀ := o₀) (o₁ := o₁)
                    h_join hsrc_mem' hres_agree_src
            have hResTm_res : QTypRespectsTagMeaning tm res.qualType :=
              joinTypeResults_QTypRespectsTagMeaning
                (tm := tm) (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
                h_join h_first_qtm h_rest_qtm
            exact ⟨hResTm_res, θ₀_body, θ₁_body,
              wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 _hθext₀_body),
              wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 _hθext₁_body),
              hOutPack_body⟩
          · -- dirty-internal fallback branch (p = true, p1 = false).
            -- Blocked: needs per-run body IH (~700 lines, same structure as not-clean
            -- branch below). Unlike the not-clean branch where p1=true forces
            -- normalizeAppResultByProvenance to set pred=noPred (making
            -- resultAgreesIfClean vacuous via resultAgreesIfClean_of_poison_noPred),
            -- here p1=false preserves pred, so resultAgreesIfClean also needs a sorry.
            -- Both resultAgreesIfClean and agreeOnClean require dual-run body IH.
            sorry
        · -- ===== Fallback: not qtypCleanUnder result1.qualType =====
          -- resultAgreesIfClean is vacuous (parrow => p1=true => res poison/noPred);
          -- rest needs unary member-evidence helper.
          have hpoison1_true : result1.qualType.poison = true := by
            by_contra hfalse
            have hpoison_false : result1.qualType.poison = false := Bool.eq_false_iff.mpr hfalse
            have hclean : qtypCleanUnder (ctxAfter (ctxAfter ctxᵢ result2) result1).regime result1.qualType :=
              qtypCleanUnder.clean hpoison_false
            exact hclean1_e1 hclean
          have hp1_true : p1 = true := by
            rw [← hp1]
            exact hpoison1_true
          rcases list_mapM_ok_mem_output_exists_input
              (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2 ctxᵢ result1 fuel')
              (xs := tcls) (ys := results) (y := first) hmap (by simp [heq_results])
            with ⟨tcl, _htcl_mem, happly_first⟩
          have hfirst_pack :
              first.qualType.poison = true ∧ first.qualType.pred = Predicate.noPred :=
            applyPFnTClosure_ok_poison_pred_of_p1_true
              (ctx := ctxᵢ) (st1 := st1) (st2 := st2) (p := p) (p1 := p1)
              (argEtyp := etyp2) (argPoison := p2) (argPred := pred2)
              (result2 := result1) (fuel := fuel') (tcl := tcl) (r := first)
              hp1_true happly_first
          have hres_pack :
              res.qualType.poison = true ∧ res.qualType.pred = Predicate.noPred :=
            joinTypeResults_poison_pred_of_head_true_noPred
              (ctx := ctxᵢ) (first := first) (rest := rest) (res := res)
              h_join hfirst_pack.1 hfirst_pack.2
          -- ===== Per-run body IH for not qtypCleanUnder (p1=true) =====
          -- Extract σcap + pbody from closureCapturedVarsRegime for each run.
          have ⟨σcapA₀, pbodyA₀, htoPExprA₀, hσcapA₀_mem, hσcapA₀_regime, hσcapA₀_typing, hσcapA₀_rec⟩ :=
            closureCapturedVarsRegime_peClosure_extract hetyp1
              (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₀)
          have ⟨σcapA₁, pbodyA₁, htoPExprA₁, hσcapA₁_mem, hσcapA₁_regime, hσcapA₁_typing, hσcapA₁_rec⟩ :=
            closureCapturedVarsRegime_peClosure_extract hetyp1
              (valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁₁)
          -- body₀ = PExpr.toExpr pbodyA₀ (and similarly for body₁)
          have hbody₀_eq : PExpr.toExpr pbodyA₀ = body₀ :=
            PExpr_toExpr_of_toPExpr?_some body₀ pbodyA₀ htoPExprA₀
          have hbody₁_eq : PExpr.toExpr pbodyA₁ = body₁ :=
            PExpr_toExpr_of_toPExpr?_some body₁ pbodyA₁ htoPExprA₁
          -- Get body typing for σcapA₀ and σcapA₁ from applyPFnTClosure
          rcases applyPFnTClosure_regular_inv_of_mapM_mem
              ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
              x₀ pbodyA₀ σcapA₀ hmap hσcapA₀_mem with
            ⟨fuelBodyA₀, firstA₀, result3A₀, happlyA₀, hfuelA₀,
              htc_bodyA₀, _hsubA₀, hfirstA₀_eq⟩
          rcases applyPFnTClosure_regular_inv_of_mapM_mem
              ctxᵢ st1 st2 p p1 etyp2 p2 pred2 result1 fuel' tcls results
              x₁ pbodyA₁ σcapA₁ hmap hσcapA₁_mem with
            ⟨fuelBodyA₁, firstA₁, result3A₁, happlyA₁, hfuelA₁,
              htc_bodyA₁, _hsubA₁, hfirstA₁_eq⟩
          -- Get membership in first :: rest (for join transport)
          have hfirstA₀_mem' : firstA₀ ∈ first :: rest := by
            rcases list_mapM_ok_mem_input_exists_output
                (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                  ctxᵢ result1 fuel')
                hmap hσcapA₀_mem with ⟨y, hy_mem, hy_eq⟩
            rw [← heq_results]
            have : y = firstA₀ := Except.ok.inj (hy_eq.symm.trans happlyA₀)
            rwa [this] at hy_mem
          have hfirstA₁_mem' : firstA₁ ∈ first :: rest := by
            rcases list_mapM_ok_mem_input_exists_output
                (fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                  ctxᵢ result1 fuel')
                hmap hσcapA₁_mem with ⟨y, hy_mem, hy_eq⟩
            rw [← heq_results]
            have : y = firstA₁ := Except.ok.inj (hy_eq.symm.trans happlyA₁)
            rwa [this] at hy_mem
          -- Define body contexts (parrow: pc has ctxᵢ.pc before p1, pureCtx := true)
          let bodyCtxA₀ : TypeContext :=
            { ctxᵢ with
              pc := joinPoison p (joinPoison ctxᵢ.pc p1)
              memEnv := result1.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
              tagEnv := result1.tagEnv'
              pureCtx := true
              nextTag := result1.nextTag'
              nextLoc := result1.nextLoc'
              regime := result1.regime' }
          let bodyCtxA₁ : TypeContext :=
            { ctxᵢ with
              pc := joinPoison p (joinPoison ctxᵢ.pc p1)
              memEnv := result1.memEnv'
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
              tagEnv := result1.tagEnv'
              pureCtx := true
              nextTag := result1.nextTag'
              nextLoc := result1.nextLoc'
              regime := result1.regime' }
          -- Common setup
          have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀2wf
          have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁2wf
          have h_mono1 : Regime.monotoneStep (ctxAfter ctxᵢ result2).regime result1.regime' :=
            regime_monotone (ctxAfter ctxᵢ result2) e1 fuel' result1 htc1'
          -- Fuel bounds
          have hfuel_ltA₀ : fuelBodyA₀ < Nat.succ (Nat.succ fuel') := by
            have : fuelBodyA₀ < fuel' := by rw [hfuelA₀]; exact Nat.lt_succ_self _
            exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          have hfuel_ltA₁ : fuelBodyA₁ < Nat.succ (Nat.succ fuel') := by
            have : fuelBodyA₁ < fuel' := by rw [hfuelA₁]; exact Nat.lt_succ_self _
            exact Nat.lt_trans this (Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
          -- ===== Run 0: StepFR_single_run =====
          have hTmBodyA₀ : wfTagMeaningCtx tm bodyCtxA₀ := by
            have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
              QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (hqt2 ▸ _hresTm2) rfl rfl
            simpa [bodyCtxA₀, ctxAfter] using
              wfTagMeaningCtx_pclosure_body
                (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                (p := p) (tcls := tcls)
                (xFun := x₀) (pbody := pbodyA₀) (σcap := σcapA₀)
                (xArg := x₀) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                _hTm1 hresTm1' hetyp1 hσcapA₀_mem hargTm
          have htcBodyA₀' : typecheck .ioFree bodyCtxA₀ (PExpr.toExpr pbodyA₀) fuelBodyA₀ = .ok result3A₀ := by
            simpa [bodyCtxA₀, typecheck] using htc_bodyA₀
          -- Rewrite body typecheck target to body₀ for IH compatibility
          have htcBodyA₀_body₀ : typecheck .ioFree bodyCtxA₀ body₀ fuelBodyA₀ = .ok result3A₀ := by
            rw [← hbody₀_eq]; exact htcBodyA₀'
          have hIH_bodyA₀ :=
            IH fuelBodyA₀ hfuel_ltA₀ body₀ bodyCtxA₀ hTmBodyA₀ result3A₀ htcBodyA₀_body₀
          have hwfBodyCtxA₀ : wfTypeContext bodyCtxA₀ := by
            simpa [bodyCtxA₀, ctxAfter, wfTypeContext] using hwf1
          have hric_bodyA₀ :
              runtimeInstantiatesCtx bodyCtxA₀ cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
            have harg₀_typed : valueHasETyp θ₀1 v₂₀ etyp2 := by
              simpa [hqt2] using valueHasETyp_extends hθext₀1.1 hv₂₀_typed
            let ctxCapBaseA₀ : TypeContext :=
              { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₀ }
            have hric_cap_baseA₀ :
                runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₀ result1)
                  cf₀.memory env₀ θ₀1 := by
              constructor
              · intro l a hlookup
                exact hric₀1.1 l a hlookup
              · intro y qt hlookup
                have hlookup_list :=
                  list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                rcases hσcapA₀_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hlookup_list hv⟩
            have hric_bodyA₀' :
                runtimeInstantiatesCtx
                  { ctxCapBaseA₀ with
                    memEnv := result1.memEnv'
                    tagEnv := result1.tagEnv'
                    nextLoc := result1.nextLoc'
                    nextTag := result1.nextTag'
                    regime := result1.regime'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₀) x₀
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                  cf₀.memory (env₀.update x₀ v₂₀) θ₀1 :=
              runtimeInstantiatesCtx_closure_body
                (ctx := ctxCapBaseA₀) (result2 := result1) (x := x₀)
                (tenv := σcapA₀)
                (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (argVal := v₂₀) (μ := cf₀.memory) (ρ := env₀) (θ := θ₀1)
                hric_cap_baseA₀ harg₀_typed
                (fun y qt hlookup => by
                  have hl := list_lookup_of_ofCaptured_lookup σcapA₀ y qt hlookup
                  rcases hσcapA₀_typing.2.1 y qt hl with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₀_typing.2.2 y qt v hl hv⟩)
            simpa [runtimeInstantiatesCtx, bodyCtxA₀, ctxCapBaseA₀, ctxAfter]
              using hric_bodyA₀'
          have htagR_bodyA₀ : regimeConsistentWithCtx bodyCtxA₀ := by
            simpa [bodyCtxA₀, ctxAfter, regimeConsistentWithCtx] using htagR1
          have hRbound_bodyA₀ : regimeBounded bodyCtxA₀.regime :=
            regimeBounded_of_monotoneStep _ _ hRbound2 h_mono1
          have hcwr_bodyA₀ :
              consistentWithRegime predSat bodyCtxA₀.regime bodyCtxA₀
                cf₀.memory (env₀.update x₀ v₂₀) θ₀1 := by
            have hlocs_src₀ :
                ∀ l qt k,
                  result1.memEnv'.lookup l = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  locsRegime predSat result1.regime' cf₀.memory θ₀1 (l, qt) :=
              fun l qt k hlookup hguard hRdef =>
                hcwr₀1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
            have hvars_capA₀ :
                ∀ x qt k,
                  (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₀.memory env₀ (x, qt) :=
              fun x qt k hlookup hguard hRdef =>
                hσcapA₀_regime x qt k
                  (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hguard hRdef
            have hvars_argA₀ :
                ∀ k,
                  qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₀.memory
                    (env₀.update x₀ v₂₀) (x₀, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
              intro k hguard hRdef
              have hvalc_arg_e2 :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₀.memory θ₀2 v₂₀ :=
                valueConsistentWithRegime_transport_pred
                  (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                  (qt := result2.qualType)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := c₂'₀.memory) (θ := θ₀2) (v := v₂₀)
                  (by simp [hqt2]) (hetyp := by simp [hqt2])
                  (by simpa [ctxAfter] using _hvalc₂₀)
              have hvalc_arg_e1 :=
                valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
              exact
                varsRegime_transport_predHolds
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                    c₂'₀.memory cf₀.memory)
                  (varsRegime_of_valueConsistentWithRegime_active
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₀.memory) (ρ := env₀.update x₀ v₂₀)
                    (x := x₀) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (v := v₂₀) (k := k)
                    (by simp [VarEnv.update, VarEnv.lookup])
                    hguard hRdef hvalc_arg_e1)
            have h_cap_cvcrA₀ :
                ∀ x qt v,
                  (VarTypeEnv.ofCaptured σcapA₀).lookup x = some qt →
                  env₀.lookup x = some v →
                  closureCapturedVarsRegime predSat result1.regime' qt
                    cf₀.memory θ₀1 v :=
              fun x qt v hlookup hv =>
                hσcapA₀_rec x qt v
                  (list_lookup_of_ofCaptured_lookup σcapA₀ x qt hlookup) hv
            exact
              consistentWithRegime_closure_body_start
                predSat ctxᵢ result1
                σcapA₀ x₀ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                cf₀.memory θ₀1 env₀ v₂₀
                hlocs_src₀ hvars_capA₀ hvars_argA₀ h_cap_cvcrA₀
                (closureCapturedVarsRegime_transport_μ_θ
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1
                    c₂'₀.memory cf₀.memory)
                  hθext₀1.1
                  (closureCapturedVarsRegime_monotone h_mono1
                    (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                      (valueConsistentWithRegime_closureCapturedVarsRegime
                        _hvalc₂₀))))
          have hwfcfg_body_initA₀ :
              wfConfig
                { memory := cf₀.memory
                  varEnv := env₀.update x₀ v₂₀
                  nextAddr := cf₀.nextAddr
                  pureMode := true } := by
            have hv₂₀_wf_e2 : wfValue c₂'₀.nextAddr v₂₀ :=
              (wfConfig_preserved .ioFree e2 _ c₂'₀ _ ht₀_e2 hwfcfg₀).2
            have hnext₂_to₁ : c₂'₀.nextAddr ≤ cf₀.nextAddr :=
              terminatesTo_nextAddr_mono .ioFree e1 c₂'₀ cf₀
                (Value.peClosure x₀ body₀ env₀) ht₀_e1
            have hv₂₀_wf : wfValue cf₀.nextAddr v₂₀ :=
              wfValue_mono_of_le_nextAddr hnext₂_to₁ x₀ v₂₀ hv₂₀_wf_e2
            have henv₀_wf : wfVarEnv cf₀.nextAddr env₀ := by
              cases (wfConfig_preserved .ioFree e1 _ cf₀ _ ht₀_e1 hwfcf₂₀).2 with
              | peClosure _ _ _ henv => exact henv
            constructor
            · intro a ha; exact hwfcf₁₀.1 a ha
            · simpa [VarEnv.update] using wfVarEnv.cons x₀ v₂₀ env₀ hv₂₀_wf henv₀_wf
          -- The body terminatesTo uses body₀, but init config has pureMode := true
          have ht₀_body' : terminatesTo .ioFree body₀
              { memory := cf₀.memory, varEnv := env₀.update x₀ v₂₀,
                nextAddr := cf₀.nextAddr, pureMode := true } evalCfg₀ o₀ := ht₀_body
          have hsr₀ :=
            StepFR_single_run hIH_bodyA₀ hpredlaws hTmBodyA₀
              cf₀.memory (env₀.update x₀ v₂₀) θ₀1 evalCfg₀ o₀
              hθ₀1wf hwfBodyCtxA₀ hric_bodyA₀ htagR_bodyA₀ hRbound_bodyA₀
              hcwr_bodyA₀ cf₀.nextAddr true hwfcfg_body_initA₀ ht₀_body'
          rcases hsr₀ with
            ⟨_, θ₀_body, hθext₀_body, hv₀_body_typed,
              _hTm_bodyA₀_after, _hwf_bodyA₀_after, _hwfcf_bodyA₀,
              hric_bodyA₀_final, _htagR_bodyA₀_final,
              hcwr_bodyA₀_final, hvalc_bodyA₀, hpres₀⟩
          -- ===== Run 1: StepFR_single_run =====
          have hTmBodyA₁ : wfTagMeaningCtx tm bodyCtxA₁ := by
            have hresTm1' : QTypRespectsTagMeaning tm result1.qualType := _hresTm1
            have hargTm : QTypRespectsTagMeaning tm ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ :=
              QTypRespectsTagMeaning_transport_etyp_pred
                (tm := tm) (qt := ⟨etyp2, p2, pred2⟩)
                (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (hqt2 ▸ _hresTm2) rfl rfl
            simpa [bodyCtxA₁, ctxAfter] using
              wfTagMeaningCtx_pclosure_body
                (tm := tm) (ctx := ctxAfter ctxᵢ result2) (result1 := result1)
                (qtRes := result1.qualType) (st1 := st1) (st2 := st2)
                (p := p) (tcls := tcls)
                (xFun := x₁) (pbody := pbodyA₁) (σcap := σcapA₁)
                (xArg := x₁) (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                _hTm1 hresTm1' hetyp1 hσcapA₁_mem hargTm
          have htcBodyA₁' : typecheck .ioFree bodyCtxA₁ (PExpr.toExpr pbodyA₁) fuelBodyA₁ = .ok result3A₁ := by
            simpa [bodyCtxA₁, typecheck] using htc_bodyA₁
          have htcBodyA₁_body₁ : typecheck .ioFree bodyCtxA₁ body₁ fuelBodyA₁ = .ok result3A₁ := by
            rw [← hbody₁_eq]; exact htcBodyA₁'
          have hIH_bodyA₁ :=
            IH fuelBodyA₁ hfuel_ltA₁ body₁ bodyCtxA₁ hTmBodyA₁ result3A₁ htcBodyA₁_body₁
          have hwfBodyCtxA₁ : wfTypeContext bodyCtxA₁ := by
            simpa [bodyCtxA₁, ctxAfter, wfTypeContext] using hwf1
          have hric_bodyA₁ :
              runtimeInstantiatesCtx bodyCtxA₁ cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
            have harg₁_typed : valueHasETyp θ₁1 v₂₁ etyp2 := by
              simpa [hqt2] using valueHasETyp_extends hθext₁1.1 hv₂₁_typed
            let ctxCapBaseA₁ : TypeContext :=
              { (ctxAfter ctxᵢ result2) with varEnv := VarTypeEnv.ofCaptured σcapA₁ }
            have hric_cap_baseA₁ :
                runtimeInstantiatesCtx (ctxAfter ctxCapBaseA₁ result1)
                  cf₁.memory env₁ θ₁1 := by
              constructor
              · intro l a hlookup
                exact hric₁1.1 l a hlookup
              · intro y qt hlookup
                have hlookup_list :=
                  list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                rcases hσcapA₁_typing.2.1 y qt hlookup_list with ⟨v, hv⟩
                exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hlookup_list hv⟩
            have hric_bodyA₁' :
                runtimeInstantiatesCtx
                  { ctxCapBaseA₁ with
                    memEnv := result1.memEnv'
                    tagEnv := result1.tagEnv'
                    nextLoc := result1.nextLoc'
                    nextTag := result1.nextTag'
                    regime := result1.regime'
                    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcapA₁) x₁
                      ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ }
                  cf₁.memory (env₁.update x₁ v₂₁) θ₁1 :=
              runtimeInstantiatesCtx_closure_body
                (ctx := ctxCapBaseA₁) (result2 := result1) (x := x₁)
                (tenv := σcapA₁)
                (argQt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                (argVal := v₂₁) (μ := cf₁.memory) (ρ := env₁) (θ := θ₁1)
                hric_cap_baseA₁ harg₁_typed
                (fun y qt hlookup => by
                  have hl := list_lookup_of_ofCaptured_lookup σcapA₁ y qt hlookup
                  rcases hσcapA₁_typing.2.1 y qt hl with ⟨v, hv⟩
                  exact ⟨v, hv, hσcapA₁_typing.2.2 y qt v hl hv⟩)
            simpa [runtimeInstantiatesCtx, bodyCtxA₁, ctxCapBaseA₁, ctxAfter]
              using hric_bodyA₁'
          have htagR_bodyA₁ : regimeConsistentWithCtx bodyCtxA₁ := by
            simpa [bodyCtxA₁, ctxAfter, regimeConsistentWithCtx] using htagR1
          have hRbound_bodyA₁ : regimeBounded bodyCtxA₁.regime :=
            regimeBounded_of_monotoneStep _ _ hRbound2 h_mono1
          have hcwr_bodyA₁ :
              consistentWithRegime predSat bodyCtxA₁.regime bodyCtxA₁
                cf₁.memory (env₁.update x₁ v₂₁) θ₁1 := by
            have hlocs_src₁ :
                ∀ l qt k,
                  result1.memEnv'.lookup l = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  locsRegime predSat result1.regime' cf₁.memory θ₁1 (l, qt) :=
              fun l qt k hlookup hguard hRdef =>
                hcwr₁1.1 l qt k (by simpa [ctxAfter] using hlookup) hguard hRdef
            have hvars_capA₁ :
                ∀ x qt k,
                  (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                  qtypGuardTag qt = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₁.memory env₁ (x, qt) :=
              fun x qt k hlookup hguard hRdef =>
                hσcapA₁_regime x qt k
                  (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hguard hRdef
            have hvars_argA₁ :
                ∀ k,
                  qtypGuardTag ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ = some k →
                  result1.regime'.lookup? k ≠ none →
                  varsRegime predSat result1.regime' cf₁.memory
                    (env₁.update x₁ v₂₁) (x₁, ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩) := by
              intro k hguard hRdef
              have hvalc_arg_e2 :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ result2).regime
                    ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩ c₂'₁.memory θ₁2 v₂₁ :=
                valueConsistentWithRegime_transport_pred
                  (predSat := predSat) (R := (ctxAfter ctxᵢ result2).regime)
                  (qt := result2.qualType)
                  (qt' := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                  (μ := c₂'₁.memory) (θ := θ₁2) (v := v₂₁)
                  (by simp [hqt2]) (hetyp := by simp [hqt2])
                  (by simpa [ctxAfter] using _hvalc₂₁)
              have hvalc_arg_e1 :=
                valueConsistentWithRegime_monotone h_mono1 hvalc_arg_e2
              exact
                varsRegime_transport_predHolds
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                    c₂'₁.memory cf₁.memory)
                  (varsRegime_of_valueConsistentWithRegime_active
                    (predSat := predSat) (R := result1.regime')
                    (μ := c₂'₁.memory) (ρ := env₁.update x₁ v₂₁)
                    (x := x₁) (qt := ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩)
                    (v := v₂₁) (k := k)
                    (by simp [VarEnv.update, VarEnv.lookup])
                    hguard hRdef hvalc_arg_e1)
            have h_cap_cvcrA₁ :
                ∀ x qt v,
                  (VarTypeEnv.ofCaptured σcapA₁).lookup x = some qt →
                  env₁.lookup x = some v →
                  closureCapturedVarsRegime predSat result1.regime' qt
                    cf₁.memory θ₁1 v :=
              fun x qt v hlookup hv =>
                hσcapA₁_rec x qt v
                  (list_lookup_of_ofCaptured_lookup σcapA₁ x qt hlookup) hv
            exact
              consistentWithRegime_closure_body_start
                predSat ctxᵢ result1
                σcapA₁ x₁ ⟨etyp2, joinPoison ctxᵢ.pc p2, pred2⟩
                cf₁.memory θ₁1 env₁ v₂₁
                hlocs_src₁ hvars_capA₁ hvars_argA₁ h_cap_cvcrA₁
                (closureCapturedVarsRegime_transport_μ_θ
                  (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1
                    c₂'₁.memory cf₁.memory)
                  hθext₁1.1
                  (closureCapturedVarsRegime_monotone h_mono1
                    (closureCapturedVarsRegime_transport_etyp (by simp [hqt2])
                      (valueConsistentWithRegime_closureCapturedVarsRegime
                        _hvalc₂₁))))
          have hwfcfg_body_initA₁ :
              wfConfig
                { memory := cf₁.memory
                  varEnv := env₁.update x₁ v₂₁
                  nextAddr := cf₁.nextAddr
                  pureMode := true } := by
            have hv₂₁_wf_e2 : wfValue c₂'₁.nextAddr v₂₁ :=
              (wfConfig_preserved .ioFree e2 _ c₂'₁ _ ht₁_e2 hwfcfg₁).2
            have hnext₂_to₁ : c₂'₁.nextAddr ≤ cf₁.nextAddr :=
              terminatesTo_nextAddr_mono .ioFree e1 c₂'₁ cf₁
                (Value.peClosure x₁ body₁ env₁) ht₁_e1
            have hv₂₁_wf : wfValue cf₁.nextAddr v₂₁ :=
              wfValue_mono_of_le_nextAddr hnext₂_to₁ x₁ v₂₁ hv₂₁_wf_e2
            have henv₁_wf : wfVarEnv cf₁.nextAddr env₁ := by
              cases (wfConfig_preserved .ioFree e1 _ cf₁ _ ht₁_e1 hwfcf₂₁).2 with
              | peClosure _ _ _ henv => exact henv
            constructor
            · intro a ha; exact hwfcf₁₁.1 a ha
            · simpa [VarEnv.update] using wfVarEnv.cons x₁ v₂₁ env₁ hv₂₁_wf henv₁_wf
          have ht₁_body' : terminatesTo .ioFree body₁
              { memory := cf₁.memory, varEnv := env₁.update x₁ v₂₁,
                nextAddr := cf₁.nextAddr, pureMode := true } evalCfg₁ o₁ := ht₁_body
          have hsr₁ :=
            StepFR_single_run hIH_bodyA₁ hpredlaws hTmBodyA₁
              cf₁.memory (env₁.update x₁ v₂₁) θ₁1 evalCfg₁ o₁
              hθ₁1wf hwfBodyCtxA₁ hric_bodyA₁ htagR_bodyA₁ hRbound_bodyA₁
              hcwr_bodyA₁ cf₁.nextAddr true hwfcfg_body_initA₁ ht₁_body'
          rcases hsr₁ with
            ⟨_, θ₁_body, hθext₁_body, hv₁_body_typed,
              _hTm_bodyA₁_after, _hwf_bodyA₁_after, _hwfcf_bodyA₁,
              hric_bodyA₁_final, _htagR_bodyA₁_final,
              hcwr_bodyA₁_final, hvalc_bodyA₁, hpres₁⟩
          -- ===== Transport to joined result and pack =====
          -- etyp agreement: body result etyp = firstA etyp (normalizeAppResultByProvenance preserves etyp)
          have hfirstA₀_etyp : firstA₀.qualType.etyp = result3A₀.qualType.etyp := by
            rw [hfirstA₀_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
          have hfirstA₁_etyp : firstA₁.qualType.etyp = result3A₁.qualType.etyp := by
            rw [hfirstA₁_eq]; unfold normalizeAppResultByProvenance; split <;> rfl
          -- regime monotonicity from result1 to body results
          have h_mono_bodyA₀ : Regime.monotoneStep bodyCtxA₀.regime result3A₀.regime' :=
            regime_monotone bodyCtxA₀ (PExpr.toExpr pbodyA₀) fuelBodyA₀ result3A₀ htcBodyA₀'
          have h_mono_bodyA₁ : Regime.monotoneStep bodyCtxA₁.regime result3A₁.regime' :=
            regime_monotone bodyCtxA₁ (PExpr.toExpr pbodyA₁) fuelBodyA₁ result3A₁ htcBodyA₁'
          have hres1_to_firstA₀_mono :
              Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                (ctxAfter ctxᵢ firstA₀).regime := by
            simpa [bodyCtxA₀, ctxAfter, hfirstA₀_eq] using h_mono_bodyA₀
          have hres1_to_firstA₁_mono :
              Regime.monotoneStep (ctxAfter (ctxAfter ctxᵢ result2) result1).regime
                (ctxAfter ctxᵢ firstA₁).regime := by
            simpa [bodyCtxA₁, ctxAfter, hfirstA₁_eq] using h_mono_bodyA₁
          -- lookup-back for regime: firstA₀.regime' -> result1.regime'
          have hlookup_back_res1_to_A₀ :
              ∀ k b,
                (ctxAfter ctxᵢ firstA₀).regime.lookup? k = some b →
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
            intro k b hk_src
            have hRdef_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k ≠ none := by
              intro hnone; rw [hk_src] at hnone; contradiction
            have hRdef_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
              hres1_to_firstA₀_mono.2.2 k hRdef_src
            cases hk_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
            | none => exact False.elim (hRdef_res1 hk_res1)
            | some b1 =>
                rcases hres1_to_firstA₀_mono.2.1 k b1 hk_res1 with hk_src' | hnone_src
                · have : some b1 = some b := hk_src'.symm.trans hk_src
                  simp [Option.some.inj this]
                · rw [hnone_src] at hk_src; cases hk_src
          have hlookup_back_res1_to_A₁ :
              ∀ k b,
                (ctxAfter ctxᵢ firstA₁).regime.lookup? k = some b →
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k = some b := by
            intro k b hk_src
            have hRdef_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k ≠ none := by
              intro hnone; rw [hk_src] at hnone; contradiction
            have hRdef_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none :=
              hres1_to_firstA₁_mono.2.2 k hRdef_src
            cases hk_res1 :
                (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k with
            | none => exact False.elim (hRdef_res1 hk_res1)
            | some b1 =>
                rcases hres1_to_firstA₁_mono.2.1 k b1 hk_res1 with hk_src' | hnone_src
                · have : some b1 = some b := hk_src'.symm.trans hk_src
                  simp [Option.some.inj this]
                · rw [hnone_src] at hk_src; cases hk_src
          -- Memory/varEnv equalities (pure closure: cf = c₁ after subst, body memory preserved in pure mode)
          -- In pure mode, the body cannot allocate or modify memory, so evalCfg.memory = bodyInit.memory = cf.memory
          have hmem₀_eq : cf₀.memory = evalCfg₀.memory := by
            obtain ⟨fuel_b₀, verbose_b₀, hbeval_b₀⟩ := ht₀_body'
            have hworld₀ := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval_b₀
            exact (beval_pure_memory_eq .ioFree body₀ fuel_b₀ _ evalCfg₀ o₀ verbose_b₀
              LeanProofs.defaultWorld LeanProofs.defaultWorld pbodyA₀
              htoPExprA₀ rfl hworld₀).symm
          have hmem₁_eq : cf₁.memory = evalCfg₁.memory := by
            obtain ⟨fuel_b₁, verbose_b₁, hbeval_b₁⟩ := ht₁_body'
            have hworld₁ := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval_b₁
            exact (beval_pure_memory_eq .ioFree body₁ fuel_b₁ _ evalCfg₁ o₁ verbose_b₁
              LeanProofs.defaultWorld LeanProofs.defaultWorld pbodyA₁
              htoPExprA₁ rfl hworld₁).symm
          -- predSat compat for memory transport (trivial after hmem_eq, but stated for uniformity with arrow)
          have hpred_compat₀ :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cf₀.memory v' ↔
                  qtypPredHolds predSat qt' cf₀.memory v' :=
            fun _ _ => Iff.rfl
          have hpred_compat₁ :
              ∀ (qt' : QTyp) (v' : Value),
                qtypPredHolds predSat qt' cf₁.memory v' ↔
                  qtypPredHolds predSat qt' cf₁.memory v' :=
            fun _ _ => Iff.rfl
          exact ⟨joinTypeResults_QTypRespectsTagMeaning tm ctxᵢ first rest res
              h_join h_first_qtm h_rest_qtm,
            θ₀_body, θ₁_body,
            wfExtendsMap_trans hθext₀2 (wfExtendsMap_trans hθext₀1 hθext₀_body),
            wfExtendsMap_trans hθext₁2 (wfExtendsMap_trans hθext₁1 hθext₁_body),
            -- valueHasETyp run 0
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
              (θ := θ₀_body) (v := o₀)
              h_join hfirstA₀_mem' (hfirstA₀_etyp ▸ hv₀_body_typed),
            -- valueHasETyp run 1
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
              (θ := θ₁_body) (v := o₁)
              h_join hfirstA₁_mem' (hfirstA₁_etyp ▸ hv₁_body_typed),
            -- wfTagMeaningCtx tm (ctxAfter ctxᵢ res)
            join_transport_wfTagMeaningCtx tm ctxᵢ first rest res h_join h_first_tm,
            -- wfTypeContext (ctxAfter ctxᵢ res)
            join_transport_wfTypeContext ctxᵢ first rest res h_join h_mem_join
              (wfTypeContext_of_wfTypeResult ctxᵢ first h_first_wf)
              (fun r hr => hresults_wf r (heq_results ▸ List.mem_cons_of_mem first hr)),
            -- wfConfig cf₀ (after subst heq_cfg₀, cf₀ = c₁₀)
            hwfcf₁₀,
            -- wfConfig cf₁ (after subst heq_cfg₁, cf₁ = c₁₁)
            hwfcf₁₁,
            -- runtimeInstantiatesCtx run 0
            by
              have hmem_to_res₀ :
                  ∀ l, firstA₀.memEnv'.contains l → res.memEnv'.contains l :=
                joinTypeResults_mem_contains_of_member
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest)
                  (res := res) h_join hfirstA₀_mem'
              constructor
              · intro l a hθ
                have hloc := hric_bodyA₀_final.1 l a hθ
                rcases hloc with ⟨hcontains_body, hmem_contains⟩
                have hcontains_src : firstA₀.memEnv'.contains l := by
                  simpa [ctxAfter, hfirstA₀_eq] using hcontains_body
                exact ⟨hmem_to_res₀ l hcontains_src, by simpa [hmem₀_eq] using hmem_contains⟩
              · intro x qt hlookup
                have hlookup_ctx :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                rcases hric₀1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                exact ⟨v, hlookup_v,
                  valueHasETyp_extends hθext₀_body.1 hv_typ⟩,
            -- runtimeInstantiatesCtx run 1
            by
              have hmem_to_res₁ :
                  ∀ l, firstA₁.memEnv'.contains l → res.memEnv'.contains l :=
                joinTypeResults_mem_contains_of_member
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest)
                  (res := res) h_join hfirstA₁_mem'
              constructor
              · intro l a hθ
                have hloc := hric_bodyA₁_final.1 l a hθ
                rcases hloc with ⟨hcontains_body, hmem_contains⟩
                have hcontains_src : firstA₁.memEnv'.contains l := by
                  simpa [ctxAfter, hfirstA₁_eq] using hcontains_body
                exact ⟨hmem_to_res₁ l hcontains_src, by simpa [hmem₁_eq] using hmem_contains⟩
              · intro x qt hlookup
                have hlookup_ctx :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                rcases hric₁1.2 hlookup_ctx with ⟨v, hlookup_v, hv_typ⟩
                exact ⟨v, hlookup_v,
                  valueHasETyp_extends hθext₁_body.1 hv_typ⟩,
            -- regimeConsistentWithCtx (ctxAfter ctxᵢ res)
            join_transport_regimeConsistentWithCtx ctxᵢ first rest res h_join
              h_regime_bound_le_join h_tag_join h_first_regime,
            -- consistentWithRegime run 0
            by
              have hcwr_src₀ :
                  consistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                    (ctxAfter ctxᵢ firstA₀) cf₀.memory cf₀.varEnv θ₀_body := by
                refine ⟨?_, ?_, ?_⟩
                · intro l qt k hlookup hguard hRdef
                  have hlookup_body :
                      (ctxAfter bodyCtxA₀ result3A₀).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstA₀_eq] using hlookup
                  have hguard_body : qtypGuardTag qt = some k := by
                    simpa [ctxAfter, hfirstA₀_eq] using hguard
                  have hRdef_body :
                      (ctxAfter bodyCtxA₀ result3A₀).regime.lookup? k ≠ none := by
                    simpa [ctxAfter, hfirstA₀_eq] using hRdef
                  simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using
                    hcwr_bodyA₀_final.1 l qt k hlookup_body hguard_body hRdef_body
                · intro x qt k hlookup hguard hRdef
                  cases hk_src : (ctxAfter ctxᵢ firstA₀).regime.lookup? k with
                  | none => exact False.elim (hRdef hk_src)
                  | some b =>
                      have hRdef_res1 :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                        intro hnone
                        have hk_back := hlookup_back_res1_to_A₀ k b hk_src
                        rw [hk_back] at hnone; contradiction
                      have hlookup_res1_ctx :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                            some qt := by
                        simpa [ctxAfter] using hlookup
                      have hvar_res1 :=
                        hcwr₀1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                      have hvar_res1_mem :=
                        varsRegime_transport_predHolds hpred_compat₀ hvar_res1
                      exact
                        varsRegime_transport_active_lookup_back
                          (predSat := predSat)
                          (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                          (R' := (ctxAfter ctxᵢ firstA₀).regime)
                          (μ := cf₀.memory) (ρ := cf₀.varEnv) (entry := (x, qt))
                          hlookup_back_res1_to_A₀ hguard hk_src hvar_res1_mem
                · intro x qt v hlookup hlookup_v
                  have hcvcr := hcwr₀1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                    hlookup_v
                  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₀ hθext₀_body.1
                    (closureCapturedVarsRegime_transport_lookup_back
                      hlookup_back_res1_to_A₀ hcvcr)
              exact
                joinTypeResults_transport_consistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀_body)
                  h_join hfirstA₀_mem' hcwr_src₀,
            -- consistentWithRegime run 1
            by
              have hcwr_src₁ :
                  consistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                    (ctxAfter ctxᵢ firstA₁) cf₁.memory cf₁.varEnv θ₁_body := by
                refine ⟨?_, ?_, ?_⟩
                · intro l qt k hlookup hguard hRdef
                  have hlookup_body :
                      (ctxAfter bodyCtxA₁ result3A₁).memEnv.lookup l = some qt := by
                    simpa [ctxAfter, hfirstA₁_eq] using hlookup
                  have hguard_body : qtypGuardTag qt = some k := by
                    simpa [ctxAfter, hfirstA₁_eq] using hguard
                  have hRdef_body :
                      (ctxAfter bodyCtxA₁ result3A₁).regime.lookup? k ≠ none := by
                    simpa [ctxAfter, hfirstA₁_eq] using hRdef
                  simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using
                    hcwr_bodyA₁_final.1 l qt k hlookup_body hguard_body hRdef_body
                · intro x qt k hlookup hguard hRdef
                  cases hk_src : (ctxAfter ctxᵢ firstA₁).regime.lookup? k with
                  | none => exact False.elim (hRdef hk_src)
                  | some b =>
                      have hRdef_res1 :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).regime.lookup? k ≠ none := by
                        intro hnone
                        have hk_back := hlookup_back_res1_to_A₁ k b hk_src
                        rw [hk_back] at hnone; contradiction
                      have hlookup_res1_ctx :
                          (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x =
                            some qt := by
                        simpa [ctxAfter] using hlookup
                      have hvar_res1 :=
                        hcwr₁1.2.1 x qt k hlookup_res1_ctx hguard hRdef_res1
                      have hvar_res1_mem :=
                        varsRegime_transport_predHolds hpred_compat₁ hvar_res1
                      exact
                        varsRegime_transport_active_lookup_back
                          (predSat := predSat)
                          (R := (ctxAfter (ctxAfter ctxᵢ result2) result1).regime)
                          (R' := (ctxAfter ctxᵢ firstA₁).regime)
                          (μ := cf₁.memory) (ρ := cf₁.varEnv) (entry := (x, qt))
                          hlookup_back_res1_to_A₁ hguard hk_src hvar_res1_mem
                · intro x qt v hlookup hlookup_v
                  have hcvcr := hcwr₁1.2.2 x qt v (by simpa [ctxAfter] using hlookup)
                    hlookup_v
                  exact closureCapturedVarsRegime_transport_μ_θ hpred_compat₁ hθext₁_body.1
                    (closureCapturedVarsRegime_transport_lookup_back
                      hlookup_back_res1_to_A₁ hcvcr)
              exact
                joinTypeResults_transport_consistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁_body)
                  h_join hfirstA₁_mem' hcwr_src₁,
            -- agreeOnClean for ¬qtypCleanUnder (p1=true, parrow, different closure bodies)
            by
              -- Regime monotonicity: result1.regime' → res.regime' (through the join)
              have h_all_members_mono :
                  ∀ x ∈ (first :: rest), Regime.monotoneStep result1.regime' x.regime' := by
                apply List.mapM_Except_preserves_property
                  (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1 etyp2 p2 pred2
                    ctxᵢ result1 fuel')
                  (P := fun x => Regime.monotoneStep result1.regime' x.regime')
                · intro tcl result _htcl
                  exact applyPFnTClosure_regime_mono tcl ctxᵢ st1 st2 p p1 etyp2 p2 pred2
                    result1 result fuel'
                    (fun m _hlt e ctx' res' htc =>
                      by simpa [ctxAfter] using regime_monotone ctx' e m res' htc)
                    _htcl
                · rw [← heq_results]; exact hmap
              have h_mono_res : Regime.monotoneStep result1.regime' res.regime' :=
                joinTypeResults_regime_monotone ctxᵢ first rest res result1.regime'
                  (h_all_members_mono first (by simp))
                  (fun x hx => h_all_members_mono x (List.mem_cons_of_mem _ hx))
                  h_join
              -- Clean transfer: qtypCleanUnder res → qtypCleanUnder result1
              have h_clean_res_to_pre :
                  ∀ qt, qtypCleanUnder res.regime' qt →
                    qtypCleanUnder result1.regime' qt :=
                fun qt hc => cleanUnder_of_monotone h_mono_res hc
              constructor
              · -- Locations conjunct
                intro l qt hlookup hclean
                have hclean_res : qtypCleanUnder res.regime' qt := by
                  simpa [ctxAfter] using hclean
                have hlookup_res : res.memEnv'.lookup l = some qt := by
                  simpa [ctxAfter] using hlookup
                -- Case split: is l inherited from result1.memEnv'?
                cases hlookup_body : (result1.memEnv'.lookup l) with
                | none =>
                  -- l is NOT in result1.memEnv' but IS in res.memEnv'. Contradiction:
                  -- every alternative's memEnv' ⊆ result1.memEnv' (pure bodies can't grow memEnv)
                  exfalso
                  have hcontains_res :=
                    memEnv_contains_of_lookup_some res.memEnv' l qt hlookup_res
                  have hcontains_l : result1.memEnv'.contains l := by
                    rcases joinTypeResults_mem_contains_head_or_rest ctxᵢ first rest res
                        h_join l hcontains_res with hfirst | ⟨r, hr, hrl⟩
                    · rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          hmap (show first ∈ results by rw [heq_results]; exact List.Mem.head rest)
                        with ⟨tcl, _, happly⟩
                      exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                        pred2 result1 fuel' tcl first happly l hfirst
                    · rcases list_mapM_ok_mem_output_exists_input
                          (f := fun tcl => applyPFnTClosure .ioFree tcl st1 st2 p p1
                            etyp2 p2 pred2 ctxᵢ result1 fuel')
                          hmap (by rw [heq_results]; exact List.mem_cons_of_mem first hr)
                        with ⟨tcl, _, happly⟩
                      exact applyPFnTClosure_mem_subset ctxᵢ st1 st2 p p1 etyp2 p2
                        pred2 result1 fuel' tcl r happly l hrl
                  rcases memEnv_lookup_some_of_contains result1.memEnv' l hcontains_l
                    with ⟨_, hlookup'⟩
                  exact Option.noConfusion (hlookup_body ▸ hlookup')
                | some qt' =>
                  -- Inherited location: l is in result1.memEnv' with type qt'
                  have hetyp_qt : qt.etyp = ETyp.int :=
                    memEnv_lookup_etyp_int res.memEnv' l qt hlookup_res
                  have hetyp_qt' : qt'.etyp = ETyp.int :=
                    memEnv_lookup_etyp_int result1.memEnv' l qt' hlookup_body
                  -- qt' is clean under result1.regime' (needed for hagree1 and hpres)
                  -- Proof: applyPFnTClosure preserves memEnv values for PExpr bodies,
                  -- so firstA₀.memEnv'.lookup l = some qt'. Then
                  -- joinTypeResults_lookup_member_clean_compat gives cleanness at
                  -- firstA₀.regime', and backward monotonicity gives result1.regime'.
                  have hclean_pre' : qtypCleanUnder result1.regime' qt' := by
                    have hfirstA₀_lookup :=
                      applyPFnTClosure_preserves_memEnv_lookup ctxᵢ st1 st2 p p1
                        etyp2 p2 pred2 result1 fuel'
                        (PFnTClosure.regular x₀ pbodyA₀ σcapA₀) firstA₀
                        happlyA₀ l qt' hlookup_body
                    have hclean_member :=
                      joinTypeResults_lookup_member_clean_compat ctxᵢ first firstA₀
                        rest res h_join hfirstA₀_mem' l qt qt'
                        (by simpa [ctxAfter] using hlookup_res)
                        (by simpa [ctxAfter] using hclean_res)
                        (by simpa [ctxAfter] using hfirstA₀_lookup)
                    exact cleanUnder_of_monotone hres1_to_firstA₀_mono hclean_member
                  -- Pre-body agreement from hagree1
                  have hlookup_pre :
                      (ctxAfter (ctxAfter ctxᵢ result2) result1).memEnv.lookup l = some qt' := by
                    simpa [ctxAfter] using hlookup_body
                  have hloc_pre := hagree1.1 l qt' hlookup_pre hclean_pre'
                  -- Per-run preservation
                  rcases hpres₀ with ⟨hpres₀_fn⟩
                  have hpres_l₀ := hpres₀_fn l qt'
                    (by simp only [bodyCtxA₀]; exact hlookup_body) hclean_pre'
                  rcases hpres₁ with ⟨hpres₁_fn⟩
                  have hpres_l₁ := hpres₁_fn l qt'
                    (by simp only [bodyCtxA₁]; exact hlookup_body) hclean_pre'
                  -- Case split on pre-body loc agreement × run-0 preservation
                  cases hloc_pre with
                  | both_unrealized _ _ hθ₀_none hθ₁_none =>
                    cases hpres_l₀ with
                    | both_unrealized _ hout₀ =>
                      cases hpres_l₁ with
                      | both_unrealized _ hout₁ =>
                        exact agreeLocUnder.both_unrealized l qt hout₀ hout₁
                      | preserve_value a n hin _ _ _ =>
                        exact absurd (hθ₁_none ▸ hin) (by exact Option.noConfusion)
                    | preserve_value a n hin _ _ _ =>
                      exact absurd (hθ₀_none ▸ hin) (by exact Option.noConfusion)
                  | agree_values _ _ a₀ a₁ n₀ n₁ hθ₀_in hθ₁_in hm₀_in hm₁_in hagree_val =>
                    cases hpres_l₀ with
                    | both_unrealized hin₀ _ =>
                      exact absurd (hin₀ ▸ hθ₀_in) (by exact Option.noConfusion)
                    | preserve_value a₀' n₀' hθ₀_in' hm₀_in' hθ₀_out hm₀_out =>
                      cases hpres_l₁ with
                      | both_unrealized hin₁ _ =>
                        exact absurd (hin₁ ▸ hθ₁_in) (by exact Option.noConfusion)
                      | preserve_value a₁' n₁' hθ₁_in' hm₁_in' hθ₁_out hm₁_out =>
                        -- Equate addresses via unique θ lookups
                        have ha₀ : a₀' = a₀ :=
                          Option.some.inj (hθ₀_in'.symm.trans hθ₀_in)
                        have ha₁ : a₁' = a₁ :=
                          Option.some.inj (hθ₁_in'.symm.trans hθ₁_in)
                        -- Equate values via unique memory lookups
                        have hn₀ : n₀' = n₀ := by
                          rw [ha₀] at hm₀_in'
                          exact Option.some.inj (hm₀_in'.symm.trans hm₀_in)
                        have hn₁ : n₁' = n₁ := by
                          rw [ha₁] at hm₁_in'
                          exact Option.some.inj (hm₁_in'.symm.trans hm₁_in)
                        -- Extract pre-body value equality (clean ints must agree)
                        have heq_pre : n₀ = n₁ := by
                          cases hagree_val with
                          | clean_eq_nonref_nonarrow _ _ _ hEq =>
                            exact Value.num.inj hEq
                          | withPred_true_eq _ _ _ _ _ hEq =>
                            exact Value.num.inj hEq
                          | clean_internal_arrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                            cases hv₀
                          | dirty_internal_arrow _ hisA htyp₀ _ =>
                            simp [valueHasETyp_num_etyp htyp₀, ETyp.isArrow] at hisA
                          | clean_internal_parrow _ _ _ _ _ _ _ _ _ hv₀ _ =>
                            cases hv₀
                          | dirty_internal_parrow _ hisP htyp₀ _ =>
                            simp [valueHasETyp_num_etyp htyp₀, ETyp.isParrow] at hisP
                          | clean_ref _ _ _ _ hv₀ _ _ => cases hv₀
                          | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ => cases hv₀
                        -- Post-body values equal: n₀' = n₁'
                        have heq_post : n₀' = n₁' := by
                          rw [hn₀, hn₁, heq_pre]
                        -- Construct post-body agreeLocUnder
                        -- (rewrite evalCfg.memory → cf.memory using pure-body memory preservation)
                        refine agreeLocUnder.agree_values l qt a₀' a₁'
                          n₀' n₁' hθ₀_out hθ₁_out
                          (by rw [hmem₀_eq]; exact hm₀_out)
                          (by rw [hmem₁_eq]; exact hm₁_out) ?_
                        rw [heq_post]
                        -- Build agreeValueUnder for clean qt with equal int values
                        cases hclean_res with
                        | clean hpoison =>
                          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison
                            (by simp [hetyp_qt, ETyp.isFunctionType, ETyp.isArrow,
                                      ETyp.isParrow])
                            (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
                        | guard k htag hregime hnotfun =>
                          exact agreeValueUnder.withPred_true_eq k htag
                            (by simpa [ctxAfter] using hregime) hnotfun
                            (by intro ⟨ls, h⟩; simp [hetyp_qt] at h) rfl
              · -- Variables conjunct
                intro x qt hlookup hclean
                have hlookup_pre :
                    (ctxAfter (ctxAfter ctxᵢ result2) result1).varEnv.lookup x = some qt := by
                  simpa [ctxAfter] using hlookup
                have hclean_pre : qtypCleanUnder result1.regime' qt :=
                  h_clean_res_to_pre qt (by simpa [ctxAfter] using hclean)
                cases hagree1.2 x qt hlookup_pre hclean_pre with
                | agree_values x qt v₀ v₁ hv₀_pre hv₁_pre hagree_val =>
                  refine agreeVarUnder.agree_values x qt v₀ v₁
                    hv₀_pre hv₁_pre ?_
                  -- Transport agreeValueUnder:
                  -- 1. Extend memory/θ (result1 context → body output context)
                  have hagree_ext :=
                    agreeValueUnder_clean_extends
                      hpred_compat₀ hpred_compat₁ hclean_pre hθext₀_body.1 hθext₁_body.1
                      hagree_val
                  -- 2. Change regime (result1 → res)
                  exact agreeValueUnder_clean_monotoneRegime h_mono_res
                    (by simpa [ctxAfter] using hclean) hagree_ext
                | both_none x qt hv₀_pre hv₁_pre =>
                  exact agreeVarUnder.both_none x qt
                    hv₀_pre hv₁_pre,
            -- valueConsistentWithRegime run 0
            by
              have hfirstA₀_eq_regime : firstA₀.regime' = result3A₀.regime' := by
                simp [hfirstA₀_eq]
              have hval_src₀ :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₀).regime
                    firstA₀.qualType cf₀.memory θ₀_body o₀ := by
                have hval_first :
                    valueConsistentWithRegime predSat (ctxAfter bodyCtxA₀ result3A₀).regime
                      (normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3A₀.qualType with
                          poison := joinPoison p1 (joinPoison p result3A₀.qualType.poison) })
                      evalCfg₀.memory θ₀_body o₀ :=
                  valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                    (predSat := predSat) (R := (ctxAfter bodyCtxA₀ result3A₀).regime)
                    (p := p) (p1 := p1) (qt := result3A₀.qualType)
                    (μ := evalCfg₀.memory) (θ := θ₀_body) (v := o₀) hvalc_bodyA₀
                simpa [ctxAfter, hfirstA₀_eq, hmem₀_eq] using hval_first
              exact
                joinTypeResults_transport_valueConsistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₀) (rest := rest) (res := res)
                  (μ := cf₀.memory) (θ := θ₀_body) (v := o₀)
                  h_join hfirstA₀_mem' hval_src₀,
            -- valueConsistentWithRegime run 1
            by
              have hval_src₁ :
                  valueConsistentWithRegime predSat (ctxAfter ctxᵢ firstA₁).regime
                    firstA₁.qualType cf₁.memory θ₁_body o₁ := by
                have hval_first :
                    valueConsistentWithRegime predSat (ctxAfter bodyCtxA₁ result3A₁).regime
                      (normalizeAppResultByProvenance (joinPoison p1 p)
                        { result3A₁.qualType with
                          poison := joinPoison p1 (joinPoison p result3A₁.qualType.poison) })
                      evalCfg₁.memory θ₁_body o₁ :=
                  valueConsistentWithRegime_transport_normalizeAppResultByProvenance
                    (predSat := predSat) (R := (ctxAfter bodyCtxA₁ result3A₁).regime)
                    (p := p) (p1 := p1) (qt := result3A₁.qualType)
                    (μ := evalCfg₁.memory) (θ := θ₁_body) (v := o₁) hvalc_bodyA₁
                simpa [ctxAfter, hfirstA₁_eq, hmem₁_eq] using hval_first
              exact
                joinTypeResults_transport_valueConsistentWithRegime_from_member
                  (predSat := predSat)
                  (ctx := ctxᵢ) (first := first) (src := firstA₁) (rest := rest) (res := res)
                  (μ := cf₁.memory) (θ := θ₁_body) (v := o₁)
                  h_join hfirstA₁_mem' hval_src₁,
            -- resultAgreesIfClean (vacuously true since poison=true and pred=noPred)
            resultAgreesIfClean_of_poison_noPred hres_pack.1 hres_pack.2⟩
