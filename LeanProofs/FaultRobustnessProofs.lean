/-
  FaultRobustnessProofs.lean - Orchestration of fault-robustness proofs.

  Imports all per-operator StepFR* files and assembles the step-level IOFree
  theorem and final fault-robustness bridges.

  Each stepFR_* case proof lives in its own StepFR*.lean file.
  Shared infrastructure is in StepFR.lean.
-/
import LeanProofs.StepFR
import LeanProofs.StepFRApp
import LeanProofs.StepFRAssign
import LeanProofs.StepFRLiteral
import LeanProofs.StepFRVar
import LeanProofs.StepFROp
import LeanProofs.StepFRFnPfn
import LeanProofs.StepFRIte
import LeanProofs.StepFRDeref
import LeanProofs.StepFRKWhile
import LeanProofs.StepFRNewRef
import LeanProofs.StepFRSeq
import LeanProofs.StepFRVlet

open List
open List.Mem
open Std
open scoped MemoryTypeEnv



private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree
  (masked : Tag → Prop)
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  ∀ fuel res,
    typecheck .ioFree ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrueMaskedRegParam
      masked
      (fun ctx μ ρ θ => consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
      (fun R qt μ θ v => valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
      .ioFree ctxᵢ e res predSat tm := by
  intro fuel res htc
  revert masked e ctxᵢ res htc
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
      intro masked e ctxᵢ res htc
      have IH' :
          ∀ m < n, ∀ (masked' : Tag → Prop) (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
            typecheck .ioFree ctx' e' m = .ok res' →
            StepFRSingleRunFinalCleanPcTrueMaskedRegParam
              masked'
              (fun ctx μ ρ θ =>
                consistentWithRegimeMasked masked' predSat ctx.regime ctx μ ρ θ)
              (fun R qt μ θ v =>
                valueConsistentWithRegimeMasked masked' predSat R qt μ θ v)
              .ioFree ctx' e' res' predSat tm := by
        intro m hm masked' e' ctx' res' htc'
        exact IH m hm masked' e' ctx' res' htc'
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm Expr.unit res Value.unit hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.unit)
                  hnotfun hpredNo hctxAfter
          | num k =>
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
              have hval : Expr.toValue? (Expr.num k) = some (Value.num k) := by
                simp [Expr.toValue?]
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.num k) res (Value.num k) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.num k)
                  hnotfun hpredNo hctxAfter
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.bool b) res (Value.bool b) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.bool b)
                  hnotfun hpredNo hctxAfter
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
              have hnotfun : res.qualType.etyp.isFunctionType = false := by
                simp [hres, res_expected, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
              have hpredNo : res.qualType.pred = Predicate.noPred := by
                simp [hres, res_expected]
              have hctxAfter : ctxAfter ctxᵢ res = ctxᵢ := by
                simp [ctxAfter, hres, res_expected]
              exact
                stepFRSingleRunFinalCleanPcTrue_literal_maskedReg
                  masked .ioFree ctxᵢ predSat tm (Expr.str s) res (Value.str s) hval
                  (fun _ => by simp [hres, res_expected]; exact valueHasETyp.str s)
                  hnotfun hpredNo hctxAfter
          | var name =>
              exact
                stepFRSingleRunFinalCleanPcTrue_var_maskedReg
                  masked .ioFree
                  ctxᵢ predSat tm name res fuel
                  htc
          | op e1 op e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_op_succ, typecheckOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_op_maskedReg
                      masked ctxᵢ predSat tm e1 e2 op fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | unaryop uop e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_unaryop_succ, typecheckUnaryOp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_unaryop_maskedReg
                      masked ctxᵢ predSat tm e uop fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | ite e1 e2 e3 =>
              -- Deferred on this branch: unary `ite` remains blocked by the known
              -- regime/type-system issue tracked under issue #128.
              sorry
          | newRef e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckNewRef] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_newRef_maskedReg
                      masked ctxᵢ predSat tm e fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | assign e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckAssign] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_assign_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | deref e =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckDeref] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_deref_maskedReg
                      masked ctxᵢ predSat tm e fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | seq e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_seq_succ, typecheckSeq] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_seq_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | kwhile e1 e2 =>
              -- Deferred on this branch: `kwhile` proof work is intentionally
              -- postponed for now and is out of scope for the current app effort.
              sorry
          | vlet z e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr_vlet_succ, typecheckVlet] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_vlet_maskedReg
                      masked ctxᵢ predSat tm z e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | fn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_fn_maskedReg
                  masked .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | pfn name ty e1 ty2 =>
              exact
                stepFRSingleRunFinalCleanPcTrue_pfn_maskedReg
                  masked .ioFree ctxᵢ predSat tm name ty e1 ty2 fuel res htc
          | app e1 e2 =>
              cases fuel with
              | zero =>
                  simp [typecheck, typecheckExpr, typecheckApp] at htc
              | succ fuel' =>
                  exact
                    stepFRSingleRunFinalCleanPcTrue_app_maskedReg
                      masked ctxᵢ predSat tm e1 e2 fuel' res
                      (StepFRSingleRunFinalCleanPcTrueMaskedRegParam_IH_of_induction
                        masked
                        (fun ctx μ ρ θ =>
                          consistentWithRegimeMasked masked predSat ctx.regime ctx μ ρ θ)
                        (fun R qt μ θ v =>
                          valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
                        predSat tm (Nat.succ (Nat.succ fuel'))
                        (fun m hm e' ctx' res' htc' =>
                          IH' m hm masked e' ctx' res' htc'))
                      htc
          | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
              intro _hpredlaws _hwfTm μ ρ θ cf o hθwf hwf hric htagR hmasked_none hRbound hcwr a pm hwfcfg ht hpc
              have : False := by
                obtain ⟨fuelT, verboseT, heq⟩ := ht
                have h_world := congrArg (fun f => f LeanProofs.defaultWorld) heq
                cases fuelT with
                | zero =>
                    simp [LeanPoison.beval, pure] at h_world
                    cases h_world
                | succ fuelT' =>
                    simp [LeanPoison.beval, pure] at h_world
                    cases h_world
              exact False.elim this

private theorem TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning) :
  ∀ fuel res,
    typecheck .ioFree ctxᵢ e fuel = .ok res →
    StepFRSingleRunFinalCleanPcTrue .ioFree ctxᵢ e res predSat tm := by
  intro fuel res htc
  have hmasked :=
    TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrueMasked_IOFree
      (masked := fun _ => False) e ctxᵢ predSat tm fuel res htc
  intro hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg hRbound hcwr a pm hwfcfg ht hpc
  have hreg_masked :
      regimeConsistentWithCtxMasked (fun _ => False) ctxᵢ := by
    constructor
    · intro k deps hlookup
      exact Or.inr (hreg.1 k deps hlookup)
    · exact hreg.2
  have hcwr_masked :
      consistentWithRegimeMasked (fun _ => False) predSat ctxᵢ.regime ctxᵢ μ ρ θ := by
    rcases hcwr with ⟨hlocs, hvars, hclos⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l qt k hlookup hguard hRdef
      exact Or.inr (hlocs l qt k hlookup hguard hRdef)
    · intro x qt k hlookup hguard hRdef
      exact Or.inr (hvars x qt k hlookup hguard hRdef)
    · intro x qt v hlookup hlookup_v
      cases hclos x qt v hlookup hlookup_v with
      | intro hdeep =>
          exact
            deepValueQTypProperty_mono
              (fun σcap ρcap ⟨hP, hT⟩ =>
                ⟨(fun x qt_x k_x hlook hguard hkR =>
                    Or.inr (hP x qt_x k_x hlook hguard hkR)),
                  hT⟩)
              hdeep
  have hmasked_none_init :
      ∀ k, (fun _ => False) k → ctxᵢ.regime.lookup? k = none := by
    intro k hk
    cases hk
  rcases
      hmasked hpredlaws hwfTm μ ρ θ cf o hθwf hwf hric hreg_masked hmasked_none_init hRbound hcwr_masked a pm hwfcfg ht hpc
    with ⟨θ', hθext, hvaltyp, hric', hcwr_masked', hvalc_masked', hpres⟩
  have hmasked_none :
      ∀ k, (fun _ => False) k → (ctxAfter ctxᵢ res).regime.lookup? k = none := by
    intro k hk
    cases hk
  have hcwr' :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf.memory cf.varEnv θ' :=
    consistentWithRegimeMasked_unmask
      (masked := fun _ => False) (predSat := predSat)
      (R := (ctxAfter ctxᵢ res).regime) (ctx := ctxAfter ctxᵢ res)
      (μ := cf.memory) (ρ := cf.varEnv) (θ := θ')
      hmasked_none hcwr_masked'
  have hvalc' :
      valueConsistentWithRegime predSat (ctxAfter ctxᵢ res).regime
        res.qualType cf.memory θ' o :=
    valueConsistentWithRegimeMasked_unmask
      (masked := fun _ => False) (predSat := predSat)
      (R := (ctxAfter ctxᵢ res).regime) (qt := res.qualType)
      (μ := cf.memory) (θ := θ') (v := o)
      hmasked_none hvalc_masked'
  exact ⟨θ', hθext, hvaltyp, hric', hcwr', hvalc', hpres⟩


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
                have hsingleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')) := by
                  intro m _hm e ctx' hwfTm' res' htc'
                  exact TypeSystemEnforcesFaultRobustness_singleRunFinalCleanPcTrue_IOFree e ctx' predSat tm m res' htc'
                exact
                  stepFR_app ctxᵢ predSat tm e1 e2 fuel' res
                    (StepFR_IH_of_induction predSat tm (Nat.succ (Nat.succ fuel')) IH)
                    hsingleIH htc
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
        have hret_clean : qtypCleanUnder (ctxAfter ctx res).regime res.qualType :=
          qtypCleanUnder.clean hret_poison
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
                exact (hnotref ⟨ls, hret_et⟩).elim
            | withPred_true_eq _ _ _ _ hnotref _ =>
                exact (hnotref ⟨ls, hret_et⟩).elim
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
    simpa using TypeSystemEnforcesFaultRobustness_step_IOFree e' ctxᵢ predSat tm
