-- Formal properties of the poison language: variable-environment preservation.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.SemanticsProperties
import Mathlib.Tactic

open Std

private lemma bevalFunctionBody_preserves_varEnv
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
    LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
      LeanPoison.EvalResult.success finalConfig v →
    currentConfig.varEnv = finalConfig.varEnv := by
  intro hEval
  cases fuel with
  | zero =>
      unfold LeanPoison.bevalFunctionBody at hEval
      simp at hEval
  | succ fuel' =>
      unfold LeanPoison.bevalFunctionBody at hEval
      let bodyCfg :=
        { currentConfig with
          varEnv := VarEnv.update closureEnv paramName argValue
          pureMode := isPure }
      cases hBody : LeanPoison.beval fuel' bodyCfg body verbose with
      | success evalConfig vBody =>
          simp [bodyCfg, hBody] at hEval
          by_cases hPure : isPure = true
          · simp [hPure] at hEval
            rcases hEval with ⟨hCfg, _hVal⟩
            subst hCfg
            rfl
          · simp [hPure] at hEval
            rcases hEval with ⟨hCfg, _hVal⟩
            subst hCfg
            rfl
      | outOfFuel =>
          simp [bodyCfg, hBody] at hEval
      | runtimeError msg =>
          simp [bodyCfg, hBody] at hEval

/-- Successful evaluation never changes the variable environment. -/
lemma beval_preserves_varEnv (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
    LeanPoison.beval fuel config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
    config₀.varEnv = config₁.varEnv := by
  intro hEval
  have hmain :
      ∀ (fuel : Nat) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
        LeanPoison.beval fuel config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
        config₀.varEnv = config₁.varEnv := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | _ fuel ih =>
        intro e verbose config₀ config₁ v hEval
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at hEval
            simp at hEval
        | succ fuel' =>
            have ih' :
                ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                  LeanPoison.beval fuel' config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
                  config₀.varEnv = config₁.varEnv := by
              intro e config₀ config₁ v h
              exact ih fuel' (Nat.lt_succ_self fuel') e verbose config₀ config₁ v h
            cases e with
            | num _ | bool _ | unit | str _ | fn _ _ _ _ | pfn _ _ _ _ =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                simp [hEval.1]
            | var x =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                cases hLookup : config₀.varEnv.lookup x with
                | none =>
                    simp [hLookup] at hEval
                | some v' =>
                    simp [hLookup] at hEval
                    simp [hEval.1]
            | unaryop op e₁ =>
                rcases bevalUnaryOp_structure op e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', v', hEval₁, _hOp, _hMem, hVar, _hNext, _hPure, _⟩
                exact (ih' e₁ config₀ config' v' hEval₁).trans hVar
            | op e₁ op e₂ =>
                rcases bevalOp_structure e₁ e₂ op (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config₁', config₂', v₁, v₂, hEval₁, hEval₂, _hOp, _hMem, hVar, _hNext, _hPure, _⟩
                exact (ih' e₁ config₀ config₁' v₁ hEval₁).trans ((ih' e₂ config₁' config₂' v₂ hEval₂).trans hVar)
            | seq e₁ e₂ =>
                rcases bevalSeq_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', v', hEval₁, hEval₂⟩
                exact (ih' e₁ config₀ config' v' hEval₁).trans (ih' e₂ config' config₁ v hEval₂)
            | vlet x e₁ e₂ =>
                -- The final config restores the incoming varEnv directly, so the
                -- conclusion is immediate from the structure equation.
                rcases bevalVlet_structure x e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨_, _, _, _, _, _, _, hCfgFinal⟩
                rw [hCfgFinal]
            | newRef e₁ =>
                rcases bevalNewRef_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', n, a, hEval₁, _ha, _hMem, _hNext, hVar, _hPure, _, _hv⟩
                exact (ih' e₁ config₀ config' (Value.num n) hEval₁).trans hVar.symm
            | deref e₁ =>
                rcases bevalDeref_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', a, n, hEval₁, _hLookup, _hv, _hMem, hVar, _hNext, _hPure, _⟩
                exact (ih' e₁ config₀ config' (Value.loc a) hEval₁).trans hVar.symm
            | assign e₁ e₂ =>
                rcases bevalAssign_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config₁', config₂', a, n, hEval₁, hEval₂, _hv, _hMem, hVar, _hNext, _hPure, _⟩
                exact (ih' e₁ config₀ config₁' (Value.loc a) hEval₁).trans ((ih' e₂ config₁' config₂' (Value.num n) hEval₂).trans hVar.symm)
            | ite e₁ e₂ e₃ =>
                rcases bevalIte_structure e₁ e₂ e₃ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', b, hEval₁, hBranch⟩
                have hVar₁ : config₀.varEnv = config'.varEnv := ih' e₁ config₀ config' (Value.bool b) hEval₁
                cases hBranch with
                | inl hTrue =>
                    rcases hTrue with ⟨_hb, hEval₂⟩
                    exact hVar₁.trans (ih' e₂ config' config₁ v hEval₂)
                | inr hFalse =>
                    rcases hFalse with ⟨_hb, hEval₃⟩
                    exact hVar₁.trans (ih' e₃ config' config₁ v hEval₃)
            | app e₁ e₂ =>
                rcases bevalApp_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨configArg, configFn, vArg, hcase⟩
                have hEvalArg :
                    LeanPoison.beval fuel' config₀ e₂ verbose = .success configArg vArg := by
                  cases hcase <;> assumption
                have hArg : config₀.varEnv = configArg.varEnv := ih' e₂ config₀ configArg vArg hEvalArg
                cases hcase with
                | @userFn x body env he2 he1 hNot hpureFalse hBody hpfinal =>
                    have hFn :
                        configArg.varEnv = configFn.varEnv :=
                      ih' e₁ configArg configFn (Value.closure x body env) he1
                    exact hArg.trans (hFn.trans (bevalFunctionBody_preserves_varEnv fuel' verbose configFn config₁ env x vArg body false v hBody))
                | @userPfn x body env he2 he1 hNot htp hBody hpfinal =>
                    have hFn :
                        configArg.varEnv = configFn.varEnv :=
                      ih' e₁ configArg configFn (Value.peClosure x body env) he1
                    exact hArg.trans (hFn.trans (bevalFunctionBody_preserves_varEnv fuel' verbose configFn config₁ env x vArg body true v hBody))
                | @externFn x y id argTyp retSpec eff env he2 he1 hp impl hGet hArgTy vRaw mem' addr' hImpl hValRet
                    hcfg =>
                    have hFn :
                        configArg.varEnv = configFn.varEnv :=
                      ih' e₁ configArg configFn
                        (Value.closure x (Expr.externFn id y argTyp retSpec eff) env) he1
                    rw [hcfg]
                    exact hArg.trans hFn
                | @externPfn x y id argTyp retSpec env he2 he1 impl hGet hArgTy vRaw hImpl hValRet hcfg =>
                    have hFn :
                        configArg.varEnv = configFn.varEnv :=
                      ih' e₁ configArg configFn
                        (Value.peClosure x (Expr.externPfn id y argTyp retSpec) env) he1
                    rw [hcfg]
                    exact hArg.trans hFn
            | externVal _id _typ _poison _pred =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> (try split at hEval) <;> simp_all
            | externFn _id _arg _argTyp _retSpec _effects =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> simp_all
            | externPfn _id _arg _argTyp _retSpec =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> simp_all
  exact hmain fuel e verbose config₀ config₁ v hEval
