-- Formal properties of the poison language: memory monotonicity.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.IOHelpers
import LeanProofs.SemanticsProperties
import Mathlib.Tactic

open Std

private lemma Memory_update_contains_of_contains (μ : Memory) (aUpd a : Address) (n : Int) :
    μ.contains a = true →
    (Memory.update μ aUpd n).contains a = true := by
  intro h
  by_cases hEq : a = aUpd
  · subst hEq
    rw [Memory.update, Std.ExtTreeMap.contains_insert]
    simp
  · have hCmp : compare aUpd a ≠ Ordering.eq := by
      intro hCmp
      have : aUpd = a := LawfulEqCmp.eq_of_compare hCmp
      exact hEq this.symm
    rw [Memory.update, Std.ExtTreeMap.contains_insert]
    simp [h]

private lemma bevalFunctionBody_memory_monotonic
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
        LeanPoison.beval m config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
        ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
    LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
      LeanPoison.EvalResult.success finalConfig v →
    ∀ l, currentConfig.memory.contains l → finalConfig.memory.contains l := by
  intro hEval l hContains
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
            exact hContains
          · simp [hPure] at hEval
            rcases hEval with ⟨hCfg, _hVal⟩
            subst hCfg
            exact IH fuel' (Nat.lt_succ_self fuel') body bodyCfg evalConfig vBody hBody l hContains
      | outOfFuel =>
          simp [bodyCfg, hBody] at hEval
      | runtimeError msg =>
          simp [bodyCfg, hBody] at hEval

/-- Successful evaluation is monotone on memory: previously allocated addresses
    remain present in the final memory. -/
lemma beval_memory_monotonic :
    ∀ (e : Expr) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval fuel config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro e fuel verbose config₀ config₁ v hEval l hContains
  have hmain :
      ∀ (fuel : Nat) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
        LeanPoison.beval fuel config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
        ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | _ fuel ih =>
        intro e verbose config₀ config₁ v hEval l hContains
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at hEval
            simp at hEval
        | succ fuel' =>
            have ih' :
                ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                  LeanPoison.beval fuel' config₀ e verbose = LeanPoison.EvalResult.success config₁ v →
                  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
              intro e config₀ config₁ v h l hContains
              exact ih fuel' (Nat.lt_succ_self fuel') e verbose config₀ config₁ v h l hContains
            cases e with
          | num _ | bool _ | unit | str _ | fn _ _ _ _ | pfn _ _ _ _ =>
              unfold LeanPoison.beval at hEval
              simp at hEval
              simpa [hEval.1] using hContains
          | var x =>
              unfold LeanPoison.beval at hEval
              simp at hEval
              cases hLookup : config₀.varEnv.lookup x with
              | none =>
                  simp [hLookup] at hEval
              | some v' =>
                  simp [hLookup] at hEval
                  simpa [hEval.1] using hContains
          | unaryop op e₁ =>
              rcases bevalUnaryOp_structure op e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config', v', hEval₁, _hOp, hMem, _hVar, _hNext, _hPure⟩
              have hStep := ih' e₁ config₀ config' v' hEval₁ l hContains
              simpa [hMem] using hStep
          | op e₁ op e₂ =>
              rcases bevalOp_structure e₁ e₂ op (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config₁', config₂', v₁, v₂, hEval₁, hEval₂, _hOp, hMem, _hVar, _hNext, _hPure⟩
              have hStep₁ := ih' e₁ config₀ config₁' v₁ hEval₁ l hContains
              have hStep₂ := ih' e₂ config₁' config₂' v₂ hEval₂ l hStep₁
              simpa [hMem] using hStep₂
          | seq e₁ e₂ =>
              rcases bevalSeq_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config', v', hEval₁, hEval₂⟩
              exact ih' e₂ config' config₁ v hEval₂ l (ih' e₁ config₀ config' v' hEval₁ l hContains)
          | vlet x e₁ e₂ =>
              rcases bevalVlet_structure x e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config₁', config₂', config₃', v₁, hEval₁, hCfg₂, hEval₂, hCfgFinal⟩
              have hStep₁ := ih' e₁ config₀ config₁' v₁ hEval₁ l hContains
              have hStep₂ := ih' e₂ config₂' config₃' v hEval₂ l (by simpa [hCfg₂] using hStep₁)
              simpa [hCfgFinal] using hStep₂
          | newRef e₁ =>
              rcases bevalNewRef_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config', n, a, hEval₁, _ha, hMem, _hNext, _hVar, _hPure, _hv⟩
              have hStep := ih' e₁ config₀ config' (Value.num n) hEval₁ l hContains
              have hUpd : (Memory.update config'.memory a n).contains l = true :=
                Memory_update_contains_of_contains config'.memory a l n hStep
              simpa [Memory.update, hMem] using hUpd
          | deref e₁ =>
              rcases bevalDeref_structure e₁ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config', a, n, hEval₁, _hLookup, _hv, hMem, _hVar, _hNext, _hPure⟩
              have hStep := ih' e₁ config₀ config' (Value.loc a) hEval₁ l hContains
              simpa [hMem] using hStep
          | assign e₁ e₂ =>
              rcases bevalAssign_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config₁', config₂', a, n, hEval₁, hEval₂, _hv, hMem, _hVar, _hNext, _hPure⟩
              have hStep₁ := ih' e₁ config₀ config₁' (Value.loc a) hEval₁ l hContains
              have hStep₂ := ih' e₂ config₁' config₂' (Value.num n) hEval₂ l hStep₁
              have hUpd : (Memory.update config₂'.memory a n).contains l = true :=
                Memory_update_contains_of_contains config₂'.memory a l n hStep₂
              simpa [Memory.update, hMem] using hUpd
          | ite e₁ e₂ e₃ =>
              rcases bevalIte_structure e₁ e₂ e₃ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨config', b, hEval₁, hBranch⟩
              have hStep₁ := ih' e₁ config₀ config' (Value.bool b) hEval₁ l hContains
              cases hBranch with
              | inl hTrue =>
                  rcases hTrue with ⟨_hb, hEval₂⟩
                  exact ih' e₂ config' config₁ v hEval₂ l hStep₁
              | inr hFalse =>
                  rcases hFalse with ⟨_hb, hEval₃⟩
                  exact ih' e₃ config' config₁ v hEval₃ l hStep₁
          | app e₁ e₂ =>
              rcases bevalApp_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                ⟨configArg, configFn, vArg, x, body, env, hEvalArg, hBranch, _hPureFinal⟩
              have hStepArg := ih' e₂ config₀ configArg vArg hEvalArg l hContains
              cases hBranch with
              | inl hReg =>
                  rcases hReg with ⟨hEvalFn, _hPureFalse, hBody⟩
                  have hStepFn := ih' e₁ configArg configFn (Value.closure x body env) hEvalFn l hStepArg
                  exact
                    bevalFunctionBody_memory_monotonic (fuel' + 1 - 1) verbose configFn config₁ env x vArg body false v
                      (by
                        intro m hm e config₀ config₁ v h l hContains
                        exact ih m (Nat.lt_trans hm (Nat.lt_succ_self fuel')) e verbose config₀ config₁ v
                          h l hContains)
                      hBody l hStepFn
              | inr hPure =>
                  rcases hPure with ⟨hEvalFn, _hBodyPure, hBody⟩
                  have hStepFn := ih' e₁ configArg configFn (Value.peClosure x body env) hEvalFn l hStepArg
                  exact
                    bevalFunctionBody_memory_monotonic (fuel' + 1 - 1) verbose configFn config₁ env x vArg body true v
                      (by
                        intro m hm e config₀ config₁ v h l hContains
                        exact ih m (Nat.lt_trans hm (Nat.lt_succ_self fuel')) e verbose config₀ config₁ v
                          h l hContains)
                      hBody l hStepFn
          | externVal _ _ _ =>
              unfold LeanPoison.beval at hEval
              simp at hEval
          | externFn _ _ _ _ =>
              unfold LeanPoison.beval at hEval
              simp at hEval
          | externPfn _ _ _ =>
              unfold LeanPoison.beval at hEval
              simp at hEval
  exact hmain fuel e verbose config₀ config₁ v hEval l hContains
