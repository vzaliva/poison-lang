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
                -- e₁ is evaluated under config₀.varEnv (`functionConfig`) and the body
                -- result restores config₀.varEnv (`bodyReturnConfig`), so the conclusion
                -- follows directly from the body / extern final-config shapes.
                rcases bevalApp_structure e₁ e₂ (fuel' + 1) verbose config₀ config₁ v hEval with
                  ⟨configArg, configFn, vArg, hcase⟩
                cases hcase with
                | @userFn x body env _he2 _he1 _hNot _hpureFalse hBody _hpfinal =>
                    have h := bevalFunctionBody_preserves_varEnv fuel' verbose
                      ({ configFn with varEnv := config₀.varEnv } : Config) config₁ env x vArg body false v hBody
                    simpa using h
                | @userPfn x body env _he2 _he1 _hNot _htp hBody _hpfinal =>
                    have h := bevalFunctionBody_preserves_varEnv fuel' verbose
                      ({ configFn with varEnv := config₀.varEnv } : Config) config₁ env x vArg body true v hBody
                    simpa using h
                | @externFn x y id argTyp argPoison argPred retSpec eff cap env _he2 he1 _hp _impl _hGet _hArgTy _vRaw _mem' _addr'
                    _hImpl _hValRet hcfg =>
                    have hFn : config₀.varEnv = configFn.varEnv := by
                      have h := ih' e₁ ({ configArg with varEnv := config₀.varEnv } : Config) configFn
                        (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec eff cap) env) he1
                      simpa using h
                    rw [hcfg]; exact hFn
                | @externPfn x y id argTyp argPoison argPred retSpec cap env _he2 he1 _impl _hGet _hArgTy _vRaw _hImpl _hValRet hcfg =>
                    have hFn : config₀.varEnv = configFn.varEnv := by
                      have h := ih' e₁ ({ configArg with varEnv := config₀.varEnv } : Config) configFn
                        (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec cap) env) he1
                      simpa using h
                    rw [hcfg]; exact hFn
            | externVal _id _typ _poison _pred =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> (try split at hEval) <;> simp_all
            | externFn _id _arg _argTyp _ _ _retSpec _effects _cap =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> simp_all
            | externPfn _id _arg _argTyp _ _ _retSpec _cap =>
                unfold LeanPoison.beval at hEval
                simp at hEval
                split at hEval <;> simp_all
  exact hmain fuel e verbose config₀ config₁ v hEval

/-- Full inversion lemma for successful application evaluation.  This exposes the
    four extern dispatch branches and therefore remains valid for populated
    registries.

    It lives here, rather than in `SemanticsProperties`, because the `Expr.app`
    evaluator evaluates the function expression under the caller's variable
    environment and restores it for the result.  The proof normalises those
    explicit reset configs back to the post-`e₂`/post-`e₁` configs via
    `beval_preserves_varEnv`, which is only available downstream of
    `SemanticsProperties`. -/
lemma terminatesTo_app_inv_full (e₁ e₂ : Expr) (c₀ cf : Config) (v : Value) :
    terminatesTo (Expr.app e₁ e₂) c₀ cf v →
    TerminatesToAppSuccess e₁ e₂ c₀ cf v := by
  intro ⟨fuel, verbose, hbeval⟩
  rcases bevalApp_structure e₁ e₂ fuel verbose c₀ cf v hbeval with
    ⟨cfg2, cfg1, v2, hcase⟩
  have he2 : LeanPoison.beval (fuel - 1) c₀ e₂ verbose = .success cfg2 v2 := by
    cases hcase <;> assumption
  -- e₂ preserves varEnv, so the function-config reset coincides with cfg2; e₁
  -- then preserves it, so the body-config reset coincides with cfg1.
  have hvar2 : c₀.varEnv = cfg2.varEnv :=
    beval_preserves_varEnv e₂ (fuel - 1) verbose c₀ cfg2 v2 he2
  have hfn_eq : ({ cfg2 with varEnv := c₀.varEnv } : Config) = cfg2 := by
    rw [hvar2]
  have hvar1 : cfg1.varEnv = c₀.varEnv := by
    have he1ex : ∃ w, LeanPoison.beval (fuel - 1) { cfg2 with varEnv := c₀.varEnv } e₁ verbose =
        .success cfg1 w := by
      cases hcase <;> exact ⟨_, by assumption⟩
    obtain ⟨w, he1'⟩ := he1ex
    have hpres := beval_preserves_varEnv e₁ (fuel - 1) verbose
      ({ cfg2 with varEnv := c₀.varEnv } : Config) cfg1 w he1'
    simpa using hpres.symm
  have hbody_eq : ({ cfg1 with varEnv := c₀.varEnv } : Config) = cfg1 := by
    rw [← hvar1]
  have hpure_cfg2 : cfg2.pureMode = c₀.pureMode :=
    terminatesTo_preserves_pureMode e₂ c₀ cfg2 v2 ⟨fuel - 1, verbose, he2⟩
  cases hcase with
  | @userFn x body env he2 he1 hNot hpureFalse hBody hpfinal =>
      rw [hfn_eq] at he1
      rw [hbody_eq] at hBody
      have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
        terminatesTo_preserves_pureMode e₁ cfg2 cfg1
          (Value.closure x body env) ⟨fuel - 1, verbose, he1⟩
      obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
        bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body false
          cf v hBody
      exact
        TerminatesToAppSuccess.userFn
          (ht_e2 := ⟨fuel - 1, verbose, he2⟩)
          (ht_e1 := ⟨fuel - 1, verbose, he1⟩)
          (hNotExternAst := hNot)
          (hpureMode := hpureFalse)
          (ht_body := hbody_terminates)
          (hcfg := by simpa using hcfg_final)
          (hpure_e2 := hpure_cfg2)
          (hpure_final := by rw [hpfinal, hpure_cfg1, hpure_cfg2])
  | @externFn x y id argTyp argPoison argPred retSpec eff cap env he2 he1 hp impl hGet hArg vRaw mem' addr'
      hImpl hValRet hcfg =>
      rw [hfn_eq] at he1
      have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
        terminatesTo_preserves_pureMode e₁ cfg2 cfg1
          (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec eff cap) env)
          ⟨fuel - 1, verbose, he1⟩
      exact
        TerminatesToAppSuccess.externFn
          (ht_e2 := ⟨fuel - 1, verbose, he2⟩)
          (ht_e1 := ⟨fuel - 1, verbose, he1⟩)
          (hpureMode := hp)
          (hGet := hGet)
          (hArg := hArg)
          (hImpl := hImpl)
          (hValRet := hValRet)
          (hcfg := hcfg)
          (hpure_e2 := hpure_cfg2)
          (hpure_final := by rw [hcfg, hpure_cfg1, hpure_cfg2])
  | @userPfn x body env he2 he1 hNot htp hBody hpfinal =>
      rw [hfn_eq] at he1
      rw [hbody_eq] at hBody
      have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
        terminatesTo_preserves_pureMode e₁ cfg2 cfg1
          (Value.peClosure x body env) ⟨fuel - 1, verbose, he1⟩
      obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
        bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body true
          cf v hBody
      exact
        TerminatesToAppSuccess.userPfn
          (ht_e2 := ⟨fuel - 1, verbose, he2⟩)
          (ht_e1 := ⟨fuel - 1, verbose, he1⟩)
          (hNotExternAst := hNot)
          (htoPExpr := htp)
          (ht_body := hbody_terminates)
          (hcfg := by simpa using hcfg_final)
          (hpure_e2 := hpure_cfg2)
          (hpure_final := by rw [hpfinal, hpure_cfg1, hpure_cfg2])
  | @externPfn x y id argTyp argPoison argPred retSpec cap env he2 he1 impl hGet hArg vRaw hImpl hValRet hcfg =>
      rw [hfn_eq] at he1
      have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
        terminatesTo_preserves_pureMode e₁ cfg2 cfg1
          (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec cap) env)
          ⟨fuel - 1, verbose, he1⟩
      exact
        TerminatesToAppSuccess.externPfn
          (ht_e2 := ⟨fuel - 1, verbose, he2⟩)
          (ht_e1 := ⟨fuel - 1, verbose, he1⟩)
          (hGet := hGet)
          (hArg := hArg)
          (hImpl := hImpl)
          (hValRet := hValRet)
          (hcfg := hcfg)
          (hpure_e2 := hpure_cfg2)
          (hpure_final := by rw [hcfg, hpure_cfg1, hpure_cfg2])
