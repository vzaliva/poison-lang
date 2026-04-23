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
                  ⟨config', v', hEval₁, _hOp, _hMem, hVar, _hNext, _hPure⟩
                exact (ih' e₁ config₀ config' v' hEval₁).trans hVar
            | op e₁ op e₂ =>
                rcases bevalOp_structure e₁ e₂ op (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config₁', config₂', v₁, v₂, hEval₁, hEval₂, _hOp, _hMem, hVar, _hNext, _hPure⟩
                exact (ih' e₁ config₀ config₁' v₁ hEval₁).trans ((ih' e₂ config₁' config₂' v₂ hEval₂).trans hVar)
            | seq e₁ e₂ =>
                rcases bevalSeq_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', v', hEval₁, hEval₂⟩
                exact (ih' e₁ config₀ config' v' hEval₁).trans (ih' e₂ config' config₁ v hEval₂)
            | vlet x e₁ e₂ =>
                rcases bevalVlet_structure x e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config₁', config₂', config₃', v₁, hEval₁, hCfg₂, hEval₂, hCfgFinal⟩
                have hVar₁ : config₀.varEnv = config₁'.varEnv := ih' e₁ config₀ config₁' v₁ hEval₁
                have hFinal : config₁.varEnv = config₁'.varEnv := by
                  rw [hCfgFinal]
                exact hVar₁.trans hFinal.symm
            | newRef e₁ =>
                rcases bevalNewRef_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', n, a, hEval₁, _ha, _hMem, _hNext, hVar, _hPure, _hv⟩
                exact (ih' e₁ config₀ config' (Value.num n) hEval₁).trans hVar.symm
            | deref e₁ =>
                rcases bevalDeref_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config', a, n, hEval₁, _hLookup, _hv, _hMem, hVar, _hNext, _hPure⟩
                exact (ih' e₁ config₀ config' (Value.loc a) hEval₁).trans hVar.symm
            | assign e₁ e₂ =>
                rcases bevalAssign_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨config₁', config₂', a, n, hEval₁, hEval₂, _hv, _hMem, hVar, _hNext, _hPure⟩
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
                  ⟨configArg, configFn, vArg, x, body, env, hEvalArg, hBranch, _hPureFinal⟩
                have hArg : config₀.varEnv = configArg.varEnv := ih' e₂ config₀ configArg vArg hEvalArg
                cases hBranch with
                | inl hReg =>
                    rcases hReg with ⟨hEvalFn, _hPureFalse, hBody⟩
                    have hFn : configArg.varEnv = configFn.varEnv := ih' e₁ configArg configFn (Value.closure x body env) hEvalFn
                    exact hArg.trans (hFn.trans (bevalFunctionBody_preserves_varEnv fuel' verbose configFn config₁ env x vArg body false v hBody))
                | inr hPure =>
                    rcases hPure with ⟨hEvalFn, _hBodyPure, hBody⟩
                    have hFn : configArg.varEnv = configFn.varEnv := ih' e₁ configArg configFn (Value.peClosure x body env) hEvalFn
                    exact hArg.trans (hFn.trans (bevalFunctionBody_preserves_varEnv fuel' verbose configFn config₁ env x vArg body true v hBody))
            | externVal _ _ _ _ =>
                -- TODO: FFI runtime — extern dispatch preserves varEnv (registry
                -- lookup only), but proof not wired.
                sorry
            | externFn _ _ _ _ _ =>
                -- TODO: FFI runtime — extern dispatch yields a closure, varEnv
                -- unchanged.
                sorry
            | externPfn _ _ _ _ =>
                -- TODO: FFI runtime — same as `externFn`.
                sorry
  exact hmain fuel e verbose config₀ config₁ v hEval
